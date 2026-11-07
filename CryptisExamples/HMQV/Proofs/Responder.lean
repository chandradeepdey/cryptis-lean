module

public import CryptisExamples.HMQV.Proofs.Base

/-! The specification of the HMQV responder.

The responder works in two steps, and `respState` is what it keeps between them.
`wp_responderAccept` escrows the responder's resources for the initiator, records the use `N` of
the session on its share and sends its authenticator. `wp_responderFinish` checks the
authenticator of the initiator, decides whether the session is compromised and, if not, redeems
what the initiator escrowed. `wp_responderConfirm` chains the two steps. -/

@[expose] public section

namespace CryptisExamples.HMQV

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Term

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

@[rocq_alias cryptis.examples.hmqv.wp_responder_listen]
theorem wp_responderListen (c : Val) :
    {{ channel c ∗ cryptisCtx }}
      hl(&responderListen &c)
    {{ (Xa Pa : Term), RET encode (Xa, Pa); isPublic Xa ∗ isPublic Pa }} := by
  iintro %Φ ⟨#Hc, -⟩ HΦ
  wp_rec
  wp_pures
  iapply wp_frame_wand $$ HΦ
  wp_apply wp_doUntil'
  iintro !>
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m1 #Hm1
  wp_list_of_term ts
  on_goal 2 => (wp_pures; ileft; ipureintro; rfl)
  wp_list_match Xa Pa
  on_goal 2 => (ileft; ipureintro; rfl)
  simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
  icases Hm1 with ⟨#HXa, #HPa⟩
  wp_pures
  imodintro
  iright
  iexists _
  isplit
  · ipureintro; rfl
  iintro HΦ
  iapply HΦ
  iframe HXa HPa

variable [HmqvGS GF]

/-- What the responder keeps between its two messages. -/
@[rocq_alias cryptis.examples.hmqv.resp_state]
abbrev respState (N : Namespace) (Pa Xa : Term) (pb xb : Nonce) : IProp GF :=
  iprop(⌜G.ofTerm Pa ≠ 1⌝ ∗ ⌜(respSI Pa Xa pb xb).secret ≠ 1⌝ ∗ hmqvEphemeral xb ∗
    usage (g.exp xb) N ∗ termToken (g.exp xb) ↑(hmqvN.@"ready") ∗
    termToken (g.exp xb) ↑(hmqvN.@"compromised"))

set_option hygiene false in
/-- Return `none` from a failed run, giving back the resource `R` lent to the hook. -/
local macro "protocol_failure" : tactic =>
  `(tactic| (
    (try wp_pures)
    iapply Hpost $$ %none
    ileft
    icases Hhook with ⟨H, -⟩
    iframe H
    ipureintro; rfl))

/-- The responder answers whatever long-term key `Pa` it is given. The hook runs only if the
responder answers, so a caller that lends it `R` gets `R` back otherwise. -/
@[rocq_alias cryptis.examples.hmqv.wp_responder_accept]
theorem wp_responderAccept (c : Val) (Pa Xa : Term) (pb : Nonce) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) (R : IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ hmqvPred N φ ρ ∗ isPublic Pa ∗ isPublic Xa ∗
        hmqvKey pb ∗
        (R ∧ ∀ xb : Nonce, termToken (respSI Pa Xa pb xb).respShare (⊤ \ ↑hmqvN) ={⊤}=∗
          φ (respSI Pa Xa pb xb) .init ∗ ψ (respSI Pa Xa pb xb)) }}
      hl(&responderAccept &c &(encode (pb : Term)) &(encode (g.exp pb)) &(encode Xa) &(encode Pa)
        &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∗ R ∨ ∃ xb : Nonce, ⌜r = some ↑(respSI Pa Xa pb xb).secret⌝ ∗
        respState N Pa Xa pb xb ∗ ψ (respSI Pa Xa pb xb) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#Hm2, -, -⟩, #Hφ, #HPa, #HXa, #Hpb, Hhook⟩ Hpost
  ihave ⟨#Hmpb, -⟩ := Hpb
  ihave #HPb := isPublic_of_hmqvKey pb $$ Hpb
  wp_rec
  wp_pures
  wp_eq_term eP
  · protocol_failure
  replace eP : G.ofTerm Pa ≠ 1 := mt (congrArg ProdGroup.toTerm) eP
  wp_pures
  wp_apply wp_mkEphemeral $$ Hctx with %xb #Hephxb #HXb Hready Huse Hcomp HtokXb
  ihave ⟨⟨#Hmxb, -⟩, -⟩ := Hephxb
  wp_pures
  wp_apply HL.wp_texp_exp
  wp_pures
  wp_apply HL.wp_hmqvKE
  wp_pures
  wp_eq_term nσ
  · protocol_failure
  replace nσ := mt (congrArg ProdGroup.toTerm) nσ
  icases Hhook with ⟨-, Hhook⟩
  imod Hhook $$ %xb HtokXb with ⟨Hgift, Hψ⟩
  imod hmqvReady_alloc (respSI Pa Xa pb xb) .init $$ Hφ Hgift with #Hreadyb
  imod termMeta_set N Std.LawfulSet.subset_refl $$ Huse with #Huse
  ihave #Hmσ := minted_hmqvK $$ Hmpb Hmxb [] [] [] []
  · iapply isPublic_minted _ $$ HPb
  · iapply isPublic_minted _ $$ HXb
  · iapply isPublic_minted _ $$ HPa
  · iapply isPublic_minted _ $$ HXa
  wp_pures
  wp_list
  wp_apply wp_tagHash
  wp_list
  wp_term_of_list
  wp_apply HL.wp_send $$ Hc []
  · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe HXb
    iapply isPublic_hash_intro $$ Hm2 [] []
    · simp only [minted_ofList_cons_cons, minted_ofList_singleton]
      iframe Hmσ
      iapply minted_ofNamespace
    · inext
      iintro !>
      iexists Pa, Xa, pb, xb, N
      iframe Hpb Hephxb Huse Hreadyb
      isplit <;> ipureintro
      · rfl
      · exact eP
  wp_pures
  imodintro
  iapply Hpost $$ %(some _)
  iright
  iexists xb
  unfold respState
  iframe Hψ Hephxb Huse Hready Hcomp
  isplit <;> ipureintro
  · rfl
  · exact ⟨eP, nσ⟩

set_option hygiene false in
/-- Return `none` from a failed run. -/
local macro "protocol_failure" : tactic =>
  `(tactic| ((try wp_pures); iapply Hpost $$ %none; ileft; ipureintro; rfl))

@[rocq_alias cryptis.examples.hmqv.wp_responder_finish]
theorem wp_responderFinish (c : Val) (Pa Xa : Term) (pb xb : Nonce) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ hmqvPred N φ ρ ∗ isPublic Pa ∗ isPublic Xa ∗
        hmqvKey pb ∗ respState N Pa Xa pb xb }}
      hl(&responderFinish &c &(encode (↑(respSI Pa Xa pb xb).secret : Term))
        &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∨ ⌜r = some ↑(respSI Pa Xa pb xb).key⌝ ∗ session ρ .resp (respSI Pa Xa pb xb) ∗
        (compromised .resp (respSI Pa Xa pb xb) ∨ φ (respSI Pa Xa pb xb) .resp) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨-, #Hm3, #Hkey⟩, #Hφ, #HPa, #HXa, #Hpb,
    ⟨%nPa, %nσ, #Hephxb, #Huse, Hready, Hcomp⟩⟩ Hpost
  ihave ⟨#Hmpb, -⟩ := Hpb
  ihave ⟨⟨#Hmxb, -⟩, #Hsxb⟩ := Hephxb
  ihave ⟨#Hxb, -⟩ := Hephxb
  ihave #HPb := isPublic_of_hmqvKey pb $$ Hpb
  ihave #HXb := isPublic_of_hmqvKey xb $$ Hxb
  ihave #Hmσ := minted_hmqvK $$ Hmpb Hmxb [] [] [] []
  · iapply isPublic_minted _ $$ HPb
  · iapply isPublic_minted _ $$ HXb
  · iapply isPublic_minted _ $$ HPa
  · iapply isPublic_minted _ $$ HXa
  ihave #Hmk := minted_key (respSI Pa Xa pb xb) $$ Hmσ
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %Aa #HAa
  wp_pures
  wp_list
  wp_apply wp_tagHash
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  ihave #Hauth := isPublic_hash_elim $$ Hm3 HAa
  wp_pures
  -- A valid authenticator was either forged, so the key is public, or produced by an honest
  -- initiator, which vouches for its keys and hands over the escrowed resources.
  ihave Hsess : |={⊤}=> session ρ .resp (respSI Pa Xa pb xb) ∗
      (compromised .resp (respSI Pa Xa pb xb) ∨ ▷ φ (respSI Pa Xa pb xb) .resp)
    $$ [Hready Hcomp]
  · icases Hauth with (#Hpt | ⟨-, #Hauth⟩)
    · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
      icases Hpt with ⟨#Hσ, -⟩
      imod termMeta_set true Std.LawfulSet.subset_refl $$ Hcomp with #Hcomp
      ihave #Hpk := isPublic_key (respSI Pa Xa pb xb) $$ Hσ
      imodintro
      isplit
      · unfold session
        iframe Hmk
        isplit
        · iintro !> -
          iexact Hpk
        · ileft
          iframe Hcomp Hpk
          iintro !> %pa %e #Hpa
          subst e
          icases isPublic_hmqvK_forged isExp_g isProd_g init_ne_resp.symm $$ Hpb Hxb Hpa Hσ with
            (#H | ⟨-, #Hx⟩)
          · imodintro
            iexact H
          · ihave Hf : ▷ False $$ []
            · iapply Hsxb $$ Hx
            imod Hf with ⟨⟩
      · ileft
        iexact Hcomp
    · icases Hauth with ⟨%pa, %xa, %Pb', %Xb', %N', %e, %nPb', #Hpa, #Hephxa, #Hreadya⟩
      obtain ⟨eσ, rfl⟩ : hmqvK hmqvN "resp" "init" pb xb (g.exp pb) (g.exp xb) Pa Xa =
          hmqvK hmqvN "init" "resp" pa xa (g.exp pa) (g.exp xa) Pb' Xb' ∧ N = N' := by
        simpa [Spec.ofList_inj] using e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmqvK_inj' isExp_g isProd_g init_ne_resp.symm nPa nPb' nσ eσ
      imod termMeta_set false Std.LawfulSet.subset_refl $$ Hcomp with #Hncomp
      imod Hreadya $$ %φ %ρ Hφ Hready with Hres
      rw [initSI_eq_respSI]
      ihave ⟨#Hrel, #Hok⟩ := honest_session N φ ρ pa pb xa xb $$ Hkey Hφ Hpa Hpb
        Hephxa Hephxb Huse Hmk
      imodintro
      isplitr [Hres]
      · unfold session
        iframe Hmk Hrel
        iright
        iframe Hok
        iintro !> #Hc
        icases termMeta_agree $$ Hc Hncomp with %h
        exact absurd h (by decide)
      · iright
        iexact Hres
  imod Hsess with ⟨#Hsess, Hres⟩
  wp_apply wp_sessionKey
  wp_pures
  iapply Hpost $$ %(some _)
  iright
  iframe Hsess Hres
  ipureintro
  rfl

@[rocq_alias cryptis.examples.hmqv.wp_responder_confirm]
theorem wp_responderConfirm (c : Val) (Pa Xa : Term) (pb : Nonce) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ hmqvPred N φ ρ ∗ isPublic Pa ∗ isPublic Xa ∗
        hmqvKey pb ∗
        (∀ xb : Nonce, termToken (respSI Pa Xa pb xb).respShare (⊤ \ ↑hmqvN) ={⊤}=∗
          φ (respSI Pa Xa pb xb) .init ∗ ψ (respSI Pa Xa pb xb)) }}
      hl(&responderConfirm &c &(encode (pb : Term)) &(encode (g.exp pb)) &(encode Xa)
        &(encode Pa) &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∨ ∃ xb : Nonce, ⌜r = some ↑(respSI Pa Xa pb xb).key⌝ ∗
        session ρ .resp (respSI Pa Xa pb xb) ∗ ψ (respSI Pa Xa pb xb) ∗
        (compromised .resp (respSI Pa Xa pb xb) ∨ φ (respSI Pa Xa pb xb) .resp) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, #Hhmqv, #Hφ, #HPa, #HXa, #Hpb, Hhook⟩ Hpost
  wp_rec
  wp_pures
  wp_apply wp_responderAccept c Pa Xa pb N φ ρ ψ iprop(True) $$ [Hhook]
    with %r (⟨%rfl, -⟩ | ⟨%xb, %rfl, Hstate, Hψ⟩)
  · iframe Hc Hctx Hhmqv Hφ HPa HXa Hpb
    isplit
    · itrivial
    · iexact Hhook
  · wp_expr_simp
    wp_pures
    iapply Hpost $$ %none
    ileft
    ipureintro; rfl
  wp_expr_simp
  wp_pures
  wp_apply wp_responderFinish c Pa Xa pb xb N φ ρ $$ [Hstate] with %r (%rfl | ⟨%rfl, #Hsess, Hres⟩)
  · iframe Hc Hctx Hhmqv Hφ HPa HXa Hpb Hstate
  · iapply Hpost $$ %none
    ileft
    ipureintro; rfl
  · iapply Hpost $$ %(some _)
    iright
    iexists xb
    iframe Hsess Hψ Hres
    ipureintro; rfl

end CryptisExamples.HMQV
