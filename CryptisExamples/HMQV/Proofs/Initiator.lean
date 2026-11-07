module

public import CryptisExamples.HMQV.Proofs.Base

/-! The specification of the HMQV initiator.

`wp_initiator` follows the run. When the authenticator of the responder checks out, the initiator
decides whether the session is compromised: either the authenticator may be forged, or it comes
from the honest responder of the same session, whose escrow the initiator then redeems. The
initiator then escrows its own resources for the responder and sends its authenticator. -/

@[expose] public section

namespace CryptisExamples.HMQV

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Term

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF] [HmqvGS GF]
local bi (IProp GF)

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

/-- The initiator with long-term private key `pa` talking to the peer `Pb`. The hook runs only
if the session succeeds, so a caller that lends it `R` gets `R` back otherwise. -/
@[rocq_alias cryptis.examples.hmqv.wp_initiator]
theorem wp_initiator (c : Val) (pa : Nonce) (Pb : Term) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) (R : IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ hmqvPred N φ ρ ∗ hmqvKey pa ∗ isPublic Pb ∗
        (R ∧ ∀ (xa : Nonce) (Xb : Term),
          termToken (initSI pa xa Pb Xb).initShare (⊤ \ ↑hmqvN) ={⊤}=∗
            φ (initSI pa xa Pb Xb) .resp ∗ ψ (initSI pa xa Pb Xb)) }}
      hl(&initiator &c &(encode (pa : Term)) &(encode (g.exp pa)) &(encode Pb)
        &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∗ R ∨ ∃ (xa : Nonce) (Xb : Term), ⌜r = some ↑(initSI pa xa Pb Xb).key⌝ ∗
        session ρ .init (initSI pa xa Pb Xb) ∗ ψ (initSI pa xa Pb Xb) ∗
        (compromised .init (initSI pa xa Pb Xb) ∨ φ (initSI pa xa Pb Xb) .init) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#Hm2, #Hm3, #Hkey⟩, #Hφ, #Hpa, #HPb, Hhook⟩ Hpost
  ihave ⟨#Hmpa, -⟩ := Hpa
  ihave #HPa := isPublic_of_hmqvKey pa $$ Hpa
  ihave #HmPb := isPublic_minted _ $$ HPb
  wp_rec
  wp_pures
  wp_eq_term eP
  · protocol_failure
  replace eP : G.ofTerm Pb ≠ 1 := mt (congrArg ProdGroup.toTerm) eP
  wp_pures
  wp_apply wp_mkEphemeral $$ Hctx with %xa #Hephxa #HXa Hready - Hcomp HtokXa
  ihave ⟨⟨#Hmxa, -⟩, #Hsxa⟩ := Hephxa
  ihave ⟨#Hxa, -⟩ := Hephxa
  wp_pures
  wp_apply HL.wp_texp_exp
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_send $$ Hc []
  · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe HXa HPa
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m2 #Hpm2
  wp_list_of_term ts
  on_goal 2 => protocol_failure
  wp_list_match Xb Ab
  on_goal 2 => protocol_failure
  simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
  icases Hpm2 with ⟨#HXb, #HAb⟩
  ihave #HmXb := isPublic_minted _ $$ HXb
  ihave #HmXa := isPublic_minted _ $$ HXa
  wp_pures
  wp_apply HL.wp_hmqvKE
  wp_pures
  wp_eq_term nσ
  · protocol_failure
  replace nσ := mt (congrArg ProdGroup.toTerm) nσ
  wp_pures
  wp_list
  wp_apply wp_tagHash
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  ihave #Hmσ := minted_hmqvK $$ Hmpa Hmxa [] HmXa HmPb HmXb
  · iapply isPublic_minted _ $$ HPa
  ihave #Hmk := minted_key (initSI pa xa Pb Xb) $$ Hmσ
  ihave #Hauth := isPublic_hash_elim $$ Hm2 HAb
  wp_pures
  -- A valid authenticator was either forged, so the key is public, or produced by an honest
  -- responder, which vouches for its keys and hands over the escrowed resources.
  ihave Hsess : |={⊤}=> session ρ .init (initSI pa xa Pb Xb) ∗
      (compromised .init (initSI pa xa Pb Xb) ∨ ▷ φ (initSI pa xa Pb Xb) .init) $$ [Hready Hcomp]
  · icases Hauth with (#Hpt | ⟨-, #Hauth⟩)
    · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
      icases Hpt with ⟨#Hσ, -⟩
      imod termMeta_set true Std.LawfulSet.subset_refl $$ Hcomp with #Hcomp
      ihave #Hpk := isPublic_key (initSI pa xa Pb Xb) $$ Hσ
      imodintro
      isplit
      · unfold session
        iframe Hmk
        isplit
        · iintro !> -
          iexact Hpk
        · ileft
          iframe Hcomp Hpk
          iintro !> %pb %e #Hpb
          subst e
          icases isPublic_hmqvK_forged isExp_g isProd_g init_ne_resp $$ Hpa Hxa Hpb Hσ with
            (#H | ⟨-, #Hx⟩)
          · imodintro
            iexact H
          · ihave Hf : ▷ False $$ []
            · iapply Hsxa $$ Hx
            imod Hf with ⟨⟩
      · ileft
        iexact Hcomp
    · icases Hauth with ⟨%Pa', %Xa', %pb, %xb, %N', %e, %nPa', #Hpb, #Hephxb, #Huse, #Hreadyb⟩
      obtain ⟨eσ, rfl⟩ : hmqvK hmqvN "init" "resp" pa xa (g.exp pa) (g.exp xa) Pb Xb =
          hmqvK hmqvN "resp" "init" pb xb (g.exp pb) (g.exp xb) Pa' Xa' ∧ N = N' := by
        simpa [Spec.ofList_inj] using e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmqvK_inj' isExp_g isProd_g init_ne_resp eP nPa' nσ eσ
      rw [initSI_eq_respSI]
      imod termMeta_set false Std.LawfulSet.subset_refl $$ Hcomp with #Hncomp
      imod Hreadyb $$ %φ %ρ Hφ Hready with Hres
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
  icases Hhook with ⟨-, Hhook⟩
  imod Hhook $$ %xa %Xb HtokXa with ⟨Hgift, Hψ⟩
  imod hmqvReady_alloc (initSI pa xa Pb Xb) .resp $$ Hφ Hgift with #Hreadya
  wp_list
  wp_apply wp_tagHash
  wp_apply HL.wp_send $$ Hc []
  · iapply isPublic_hash_intro $$ Hm3 [] []
    · simp only [minted_ofList_cons_cons, minted_ofList_singleton]
      iframe Hmσ
      iapply minted_ofNamespace
    · inext
      iintro !>
      iexists pa, xa, Pb, Xb, N
      iframe Hpa Hephxa Hreadya
      isplit <;> ipureintro
      · rfl
      · exact eP
  wp_pures
  wp_apply wp_sessionKey
  wp_pures
  iapply Hpost $$ %(some _)
  iright
  iexists xa, Xb
  iframe Hsess Hψ Hres
  ipureintro
  rfl

end CryptisExamples.HMQV
