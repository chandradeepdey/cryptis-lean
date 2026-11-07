module

public import Cryptis.Tactics
public import CryptisExamples.IsoDH.Proofs.Base

/-! The specification of the ISO-DH initiator.

The exponent `a` of the initiator becomes public when the session is compromised or released;
`initSecrecy` says so, finding the responder's share through metadata on the initiator's share.
`wp_initiator` follows the run: on a valid second message it records the responder's share,
decides whether the session is compromised, redeems what the responder escrowed for it, escrows
its own resources for the responder, and signs the third message. -/

@[expose] public section

namespace CryptisExamples.IsoDH

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Term BigSepFinset

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF] [IsoDHGS GF]
local bi (IProp GF)

/-- The secrecy of the exponent `a` of the initiator: compromise makes it public, and so does the
release of the session, once the share of the responder is known. -/
@[rocq_alias cryptis.examples.iso_dh.init_secrecy]
abbrev initSecrecy (ρ : SessInfo → IProp GF) (skI skR : Key .sign) (a : Nonce) : IProp GF :=
  iprop(termMeta ((int 0).exp a) (isoDHN.@"compromised") true ∨
    ∃ gb, termMeta ((int 0).exp a) (isoDHN.@"resp_share") gb ∗
      ρ ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩)

set_option hygiene false in
/-- Return `none` from a failed run, and give back the resource `R` lent to the hook. -/
local macro "protocol_failure" : tactic => `(tactic|
  ((try wp_pures); iapply Hpost $$ %none; ileft; icases Hhook with ⟨Hhook, -⟩; isplitr;
   ipureintro; rfl; iexact Hhook))

/-- The hook runs only if the session succeeds, so a caller that lends it `R` gets `R` back
otherwise. -/
@[rocq_alias cryptis.examples.iso_dh.wp_initiator]
theorem wp_initiator (c : Val) (skI skR : Key .sign) (N : Namespace)
    (φ : SessInfo → Role → IProp GF) (ρ ψ : SessInfo → IProp GF) (R : IProp GF) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗ isoDHPred N φ ρ ∗ minted skI ∗ minted skR ∗
        (R ∧ ∀ (a : Nonce) (gb : Term),
          let si : SessInfo := ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩
          iprop(termToken si.initShare (⊤ \ ↑isoDHN) ={⊤}=∗ φ si .resp ∗ ψ si)) }}
      hl(&initiator &c &(encode skI) &(encode (Spec.pkey skR)) &(encode (ofNamespace N)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∗ R ∨ ∃ (a : Nonce) (gb : Term),
        let si : SessInfo := ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩
        iprop(⌜r = some ↑si.key⌝ ∗ session ρ .init si ∗ ψ si ∗
          (compromised .init si ∨ φ si .init)) }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#H2, #H3⟩, #HNφ, #HmI, #HmR, Hhook⟩ Hpost
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
  wp_apply HL.wp_mkNonce_freshN ∅ (initSecrecy ρ skI skR) dhKeyShare (fun a => {(int 0).exp a})
    $$ Hctx [] [] with %a - #Hma #Hsa #Hapred - Htok
  · iintro %t %ht
    simp at ht
  · iintro %a
    rw [(bigSepFinset_singleton _).to_eq, (minted_exp hx hg _).to_eq, (minted_int 0).to_eq]
    iintro !>
    isplit
    · iintro #H; isplit; itrivial; iexact H
    · iintro ⟨-, #H⟩; iexact H
  rw [(bigSepFinset_singleton _).to_eq]
  icases (termToken_difference (E1 := ↑isoDHN) CoPset.subseteq_top).mp $$ Htok with ⟨HtokN, Htok⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"compromised")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HcompTok, HtokN⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"resp_share")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HshareTok, HtokN⟩
  icases (termToken_difference (E1 := ↑(isoDHN.@"ready")) (by solve_ndisj)).mp $$ HtokN
    with ⟨HreadyTok, -⟩
  wp_pures
  wp_apply wp_mkKeyShare
  wp_pures
  wp_list
  wp_term_of_list
  ihave #Hpga := isPublic_dh_share hx hg rfl $$ Hg Hma Hapred
  wp_pures
  wp_apply HL.wp_send $$ Hc []
  · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe Hpga HpI
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m2 #Hm2
  wp_apply HL.wp_verify skR (isoDHN.@"m2") m2 msg2Pred $$ H2 Hm2
  isplit
  on_goal 2 => protocol_failure
  iintro %m2 #Hpm2 #Hinv
  wp_list_of_term ts
  on_goal 2 => protocol_failure
  wp_list_match ga' gb pkI' N'
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
  icases (isPublic_ofList _).mp $$ Hpm2 with ⟨-, #Hpgb, -⟩
  ihave #Hmgb := isPublic_minted gb $$ Hpgb
  wp_pures
  wp_apply HL.wp_texp_exp
  wp_pures
  wp_list
  wp_term_of_list
  wp_pures
  wp_list
  wp_term_of_list
  imod termMeta_set gb Std.LawfulSet.subset_refl $$ HshareTok with #Hmeta
  let si : SessInfo := ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩
  ihave #Hsa : □ (isPublic a ↔ ▷ □ (compromised .init si ∨ ρ si)) $$ [#]
  · unfold compromised
    iintro !>
    isplit
    · iintro #Hpa
      ihave #H := Hsa $$ Hpa
      inext
      icases H with (#Hc | ⟨%gb', #Hmeta', #Hr⟩)
      · iintro !>; ileft; iexact Hc
      icases termMeta_agree $$ Hmeta Hmeta' with %rfl
      iintro !>; iright; iexact Hr
    · iintro #H
      iapply Hsa
      inext
      icases H with (#Hc | #Hr)
      · iintro !>; ileft; iexact Hc
      · iintro !>; iright; iexists gb; isplitl; iexact Hmeta; iexact Hr
  ihave #Hk1 : □ (▷ □ (compromised .init si ∨ ρ si) → isPublic si.key) $$ [#]
  · iintro !> #H
    unfold SessInfo.key
    simp only [(isPublic_coe_key _).to_eq, isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe HpI HpR Hpga Hpgb
    iapply isPublic_exp $$ Hpgb []
    iapply Hsa $$ H
  ihave #Hmk : minted si.key $$ [#]
  · unfold SessInfo.key
    simp only [(minted_coe_key _).to_eq, minted_ofList_cons_cons, minted_ofList_singleton,
      (minted_pkey _).to_eq]
    iframe HmI HmR Hmgb
    isplit
    · iapply isPublic_minted $$ Hpga
    · iapply minted_exp_intro $$ [Hmgb Hma]
      isplit <;> iassumption
  -- A signature on `m2` is forged, or vouches for the share and escrow of the honest responder.
  ihave Hres : |={⊤}=> session ρ .init si ∗ ▷ (compromised .init si ∨ φ si .init) ∗
      ((isPublic skI ∨ isPublic skR) ∨ ∃ φ' ρ', usage gb N ∗ isoDHPred N φ' ρ' ∗
        □ (isPublic si.key → ▷ □ ρ' si)) $$ [HcompTok HreadyTok]
  · icases Hinv with (#Hcomp | #Hinv)
    · imod termMeta_set true Std.LawfulSet.subset_refl $$ HcompTok with #Hc
      ihave #Hpk := Hk1 $$ []
      · inext; iintro !>; ileft; unfold compromised; iexact Hc
      imodintro
      isplitr
      · unfold session compromised
        iframe Hmk
        isplitl
        · iintro !> -; iexact Hpk
        ileft
        iframe Hc Hpk
        iright; iexact Hcomp
      isplitr
      · inext; ileft; unfold compromised; iexact Hc
      · ileft; iright; iexact Hcomp
    icases Hinv with ⟨%ga', %b, %skI', %N', %φ', %ρ', %e, #HNφ', #Hsb, #Hpredb, #Huse, #Hready⟩
    simp only [Spec.ofList_inj, List.cons.injEq, Key.pkey_injective.eq_iff,
      ofNamespace_inj, _root_.and_true] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    rw [exp_right_comm (int 0) (a : Term) (b : Term)]
    imod termMeta_set false Std.LawfulSet.subset_refl $$ HcompTok with #Hnc
    ihave #Hnc' : □ (compromised .init si → False) $$ [#]
    · unfold compromised
      iintro !> #Hc
      icases termMeta_agree $$ Hc Hnc with %h
      cases h
    icases isoDHPred_agree $$ HNφ HNφ' with ⟨-, #Hρeq⟩
    ispecialize Hρeq $$ %si
    ihave #Hsa' : □ (isPublic a ↔ ▷ □ ρ si) $$ [#]
    · iintro !>
      isplit
      · iintro #Hpa
        ihave #H := Hsa $$ Hpa
        inext
        icases H with (#Hc | #Hr)
        · iexfalso; iapply Hnc' $$ Hc
        · iintro !>; iexact Hr
      · iintro #Hr
        iapply Hsa
        inext
        iintro !>; iright; iexact Hr
    ihave #Hsb' : □ (isPublic b ↔ ▷ □ ρ si) $$ [#]
    · iintro !>
      isplit
      · iintro #Hpb
        ihave #H := Hsb $$ Hpb
        inext
        irewrite [Hρeq]
        iexact H
      · iintro #Hr
        iapply Hsb
        inext
        irewrite [← Hρeq]
        iexact Hr
    ihave #Hok : □ (isPublic si.key → ▷ □ ρ si) $$ [#]
    · unfold SessInfo.key
      simp only [(isPublic_coe_key _).to_eq, isPublic_ofList_cons_cons, isPublic_ofList_singleton]
      iintro !> ⟨-, -, -, -, #Hpgab⟩
      iapply isPublic_dh_secret_elim hx hg rfl rfl iprop(▷ □ ρ si) $$ Hsb' Hpredb Hsa' Hapred
      rw [← exp_exp]
      iexact Hpgab
    unfold isoDHReady
    imod Hready $$ %φ %ρ HNφ HreadyTok with Hφ
    imodintro
    isplitr [Hφ]
    · unfold session
      iframe Hmk
      isplitl
      · iintro !> #Hr; iapply Hk1; inext; iintro !>; iright; iexact Hr
      iright
      iframe Hnc' Hok
    isplitl [Hφ]
    · inext; iright; iexact Hφ
    iright
    iexists φ', ρ'
    iframe Huse HNφ'
    iintro !> #Hpk
    ihave #Hr := Hok $$ Hpk
    inext
    irewrite [← Hρeq]
    iexact Hr
  imod Hres with ⟨#Hsess, Hφ, #Hk2⟩
  icases Hhook with ⟨-, Hhook⟩
  imod Hhook $$ %a %gb Htok with ⟨Hgift, Hψ⟩
  imod isoDHReady_alloc N si .resp $$ HNφ Hgift with #HreadyR
  wp_pures
  wp_apply HL.wp_sign skI (isoDHN.@"m3") (Spec.ofList [(int 0).exp a, gb, Spec.pkey skR]) msg3Pred
    $$ H3 HmI [] [] with %m3 #Hm3
  · simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
    iframe Hpga Hpgb HpR
  · iright
    iintro !>
    iexists a, gb, skR
    isplit
    · ipureintro; rfl
    icases Hk2 with (#H | ⟨%φ', %ρ', #Huse, #HNφ', #Hok⟩)
    · ileft; iexact H
    · iright
      iexists N, φ', ρ'
      iframe Huse HNφ' Hok HreadyR
  wp_pures
  wp_apply HL.wp_send $$ Hc Hm3
  wp_pures
  wp_apply HL.wp_deriveSEncKey
  wp_pures
  iapply Hpost $$ %(some _)
  iright
  iexists a, gb
  iframe Hsess Hψ Hφ
  ipureintro; rfl

end CryptisExamples.IsoDH
