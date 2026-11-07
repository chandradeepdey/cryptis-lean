module

public import Cryptis.Tactics
public import CryptisExamples.IsoDH.Proofs.Base

/-! The specification of the ISO-DH responder.

`wp_responderListen` waits for a well-formed first message. `wp_responderConfirm` records the use
`N` of the session on its share, escrows its resources for the initiator, and signs the second
message. On a valid third message it decides whether the session is compromised and, if not,
redeems what the initiator escrowed for it. `wp_responder` combines the two. -/

@[expose] public section

namespace CryptisExamples.IsoDH

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Term BigSepFinset

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF] [IsoDHGS GF]
local bi (IProp GF)

set_option hygiene false in
/-- Return `none` from a failed run. -/
local macro "protocol_failure" : tactic =>
  `(tactic| ((try wp_pures); iapply Hpost $$ %none; ileft; ipureintro; rfl))

omit [IsoDHGS GF] in
@[rocq_alias cryptis.examples.iso_dh.wp_responder_listen]
theorem wp_responderListen (c : Val) :
    {{ channel c ∗ cryptisCtx }}
      hl(&responderListen &c)
    {{ (ga : Term) (skI : Key .sign), RET encode (ga, Spec.pkey skI);
      isPublic ga ∗ minted skI }} := by
  iintro %Φ ⟨#Hc, #Hctx⟩ Hpost
  wp_rec
  wp_pures
  iapply wp_frame_wand $$ Hpost
  wp_apply wp_doUntil'
  iintro !>
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m1 #Hm1
  wp_list_of_term ts
  on_goal 2 => (wp_pures; ileft; ipureintro; rfl)
  wp_list_match ga pkI
  on_goal 2 => (ileft; ipureintro; rfl)
  simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
  icases Hm1 with ⟨#Hpga, #HppkI⟩
  wp_apply HL.wp_isVerifyKey pkI $$ []
  · iapply isPublic_minted $$ HppkI
  isplit
  on_goal 2 => ((try wp_pures); ileft; ipureintro; rfl)
  iintro %skI %rfl #HmI
  wp_pures
  imodintro
  iright
  iexists _
  isplit
  · ipureintro; rfl
  iintro Hpost
  iapply Hpost $$ %ga %skI
  iframe Hpga HmI

@[rocq_alias cryptis.examples.iso_dh.wp_responder_confirm]
theorem wp_responderConfirm (c : Val) (skI skR : Key .sign) (ga : Term) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗ isoDHPred N φ ρ ∗ isPublic ga ∗ minted skI ∗
        minted skR ∗
        (∀ b : Nonce,
          let si : SessInfo := ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩
          iprop(termToken si.respShare (⊤ \ ↑isoDHN) ={⊤}=∗ φ si .init ∗ ψ si)) }}
      hl(&responderConfirm &c &(encode skR) &(encode ga) &(encode (Spec.pkey skI))
        &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∨ ∃ b : Nonce,
        let si : SessInfo := ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩
        iprop(⌜r = some ↑si.key⌝ ∗ session ρ .resp si ∗ ψ si ∗
          (compromised .resp si ∨ φ si .resp)) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#H2, #H3⟩, #HNφ, #Hpga, #HmI, #HmR, Hhook⟩ Hpost
  have hx : (int 0).isExp = false := rfl
  have hg : (int 0).isProd .gmul = false := rfl
  ihave #Hg : isPublic (int 0) $$ []
  · iapply (isPublic_int 0).mpr; itrivial
  ihave #HpI := (isPublic_pkey_sign skI).mpr $$ HmI
  ihave #HpR := (isPublic_pkey_sign skR).mpr $$ HmR
  wp_rec
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_apply HL.wp_mkNonce_freshN ∅ (fun b => ρ ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩)
      dhKeyShare (fun b => {(int 0).exp b})
    $$ Hctx [] [] with %b - #Hmb #Hsb #Hpredb - Htok
  · iintro %t %ht
    simp at ht
  · iintro %b
    rw [(bigSepFinset_singleton _).to_eq, (minted_exp hx hg _).to_eq, (minted_int 0).to_eq]
    iintro !>
    isplit
    · iintro #H; isplit; itrivial; iexact H
    · iintro ⟨-, #H⟩; iexact H
  let si : SessInfo := ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩
  rw [(bigSepFinset_singleton _).to_eq]
  icases (termToken_difference (E1 := ↑isoDHN) CoPset.subseteq_top).mp $$ Htok with ⟨HtokN, Htok⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"compromised")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HcompTok, HtokN⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"usage")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HuseTok, HtokN⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"ready")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HreadyTok, -⟩
  imod termMeta_set N Std.LawfulSet.subset_refl $$ HuseTok with #Huse
  imod Hhook $$ %b Htok with ⟨Hgift, Hψ⟩
  imod isoDHReady_alloc N si .init $$ HNφ Hgift with #Hready
  ihave #Hpgb := isPublic_dh_share hx hg rfl $$ Hg Hmb Hpredb
  wp_pures
  wp_apply wp_mkKeyShare
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_sign skR (isoDHN.@"m2")
      (Spec.ofList [ga, (int 0).exp b, Spec.pkey skI, ofNamespace N]) msg2Pred
    $$ H2 HmR [] [] with %m2 #Hm2
  · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe Hpga Hpgb HpI
    iapply (isPublic_ofNamespace N).mpr; itrivial
  · iright
    iintro !>
    iexists ga, b, skI, N, φ, ρ
    unfold usage
    iframe HNφ Hsb Hpredb Huse Hready
    ipureintro; rfl
  wp_pures
  wp_apply HL.wp_send $$ Hc Hm2
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m3 #Hm3
  wp_apply HL.wp_verify skI (isoDHN.@"m3") m3 msg3Pred $$ H3 Hm3
  isplit
  on_goal 2 => protocol_failure
  iintro %m3 #Hpm3 #Hinv
  wp_list_of_term ts
  on_goal 2 => protocol_failure
  wp_list_match ga' gb' pkR'
  on_goal 2 => protocol_failure
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  wp_pures
  wp_apply HL.wp_texp_exp
  wp_pures
  wp_list
  wp_term_of_list
  wp_pures
  ihave #Hmk : minted si.key $$ [#]
  · unfold SessInfo.key
    simp only [(minted_coe_key _).to_eq, minted_ofList_cons_cons, minted_ofList_singleton,
      (minted_pkey _).to_eq]
    iframe HmI HmR
    isplit
    · iapply isPublic_minted $$ Hpga
    isplit
    · iapply isPublic_minted $$ Hpgb
    · iapply minted_exp_intro
      isplit
      · iapply isPublic_minted $$ Hpga
      · iexact Hmb
  ihave #Hk1 : □ (▷ □ ρ si → isPublic si.key) $$ [#]
  · iintro !> #H
    unfold SessInfo.key
    simp only [(isPublic_coe_key _).to_eq, isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe HpI HpR Hpga Hpgb
    iapply isPublic_exp $$ Hpga []
    iapply Hsb $$ H
  -- A signature on `m3` is forged, or comes from the honest initiator, which may have given up.
  ihave Hres : |={⊤}=> session ρ .resp si ∗ ▷ (compromised .resp si ∨ φ si .resp)
    $$ [HcompTok HreadyTok]
  · unfold session compromised
    icases Hinv with (#Hcomp | #Hinv)
    · imod termMeta_set true Std.LawfulSet.subset_refl $$ HcompTok with #Hc
      imodintro
      isplitr
      · iframe Hmk Hk1
        ileft
        iframe Hc
        isplitl
        · ileft; iexact Hcomp
        · itrivial
      · inext; ileft; iexact Hc
    icases Hinv with ⟨%a, %gb', %skR', %e, #Hinv⟩
    simp only [Spec.ofList_inj, List.cons.injEq, Key.pkey_injective.eq_iff, _root_.and_true] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    rw [exp_right_comm (int 0) (b : Term) (a : Term)]
    icases Hinv with (#Hcomp | ⟨%N', %φ', %ρ', #Huse', #HNφ', #Hok, #HreadyR⟩)
    · imod termMeta_set true Std.LawfulSet.subset_refl $$ HcompTok with #Hc
      imodintro
      isplitr
      · iframe Hmk Hk1
        ileft
        iframe Hc Hcomp
      · inext; ileft; iexact Hc
    unfold usage
    icases termMeta_agree $$ Huse Huse' with %rfl
    icases isoDHPred_agree $$ HNφ HNφ' with ⟨-, #Hρeq⟩
    ispecialize Hρeq $$ %si
    imod termMeta_set false Std.LawfulSet.subset_refl $$ HcompTok with #Hnc
    unfold isoDHReady
    imod HreadyR $$ %φ %ρ HNφ HreadyTok with Hφ
    imodintro
    isplitr [Hφ]
    · iframe Hmk Hk1
      iright
      isplit
      · iintro !> #Hc
        icases termMeta_agree $$ Hc Hnc with %h
        cases h
      · iintro !> #Hpk
        ihave #Hr := Hok $$ Hpk
        inext
        irewrite [Hρeq]
        iexact Hr
    · inext; iright; iexact Hφ
  imod Hres with ⟨#Hsess, Hφ⟩
  wp_apply HL.wp_deriveSEncKey
  wp_pures
  imodintro
  iapply Hpost $$ %(some _)
  iright
  iexists b
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hsess
  iframe Hψ Hφ

@[rocq_alias cryptis.examples.iso_dh.wp_responder]
theorem wp_responder (c : Val) (skR : Key .sign) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗ isoDHPred N φ ρ ∗ minted skR ∗
        (∀ (skI : Key .sign) (ga : Term) (b : Nonce),
          let si : SessInfo := ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩
          iprop(termToken si.respShare (⊤ \ ↑isoDHN) ={⊤}=∗ φ si .init ∗ ψ si)) }}
      hl(&responder &c &(encode skR) &(encode (ofNamespace N)))
    {{ (r : Option (Term × Term)), RET encode r;
      ⌜r = none⌝ ∨ ∃ (skI : Key .sign) (ga : Term) (b : Nonce),
        let si : SessInfo := ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩
        iprop(⌜r = some (Spec.pkey skI, ↑si.key)⌝ ∗ session ρ .resp si ∗ ψ si ∗
          (compromised .resp si ∨ φ si .resp)) }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hiso, #HNφ, #HmR, Hhook⟩ Hpost
  wp_rec
  wp_pures
  wp_apply wp_responderListen c $$ [] with %ga %skI ⟨#Hpga, #HmI⟩
  · iframe Hc Hctx
  wp_pures
  wp_apply wp_responderConfirm c skI skR ga N φ ρ ψ $$ [Hhook] with %r Hr
  · iframe Hc Hctx Hiso HNφ Hpga HmI HmR
    iintro %b
    iapply Hhook
  icases Hr with (%rfl | ⟨%b, %rfl, #Hsess, Hψ, Hφ⟩) <;> wp_expr_simp
  · wp_pures
    iapply Hpost $$ %none
    ileft; ipureintro; rfl
  wp_pures
  iapply Hpost $$ %(some (_, _))
  iright
  iexists skI, ga, b
  dsimp only
  iframe Hsess Hψ Hφ
  ipureintro; rfl

end CryptisExamples.IsoDH
