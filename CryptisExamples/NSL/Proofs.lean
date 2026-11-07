module

public import Cryptis.Tactics
public import CryptisExamples.NSL.Impl

/-! The specifications of the NSL roles.

A run of either role that completes returns a session key that is public only if the secret key
of one of the two participants is. The proof rests on invariants attached to the tags of the
encrypted messages.

- A session is described by its participants and their nonces, which determine its key.
- The message invariants say that the nonce in the first and in the second message is public
  exactly when one of the participants is compromised. `nslCtx` registers them.
- `sessionNSL` is what a completed run guarantees: the key is minted, and it is public exactly
  when one of the participants is compromised.
- `wp_init` and `wp_resp` specify the two roles. Each also hands back the token of its own nonce,
  which the game uses to show that keys are never reused. -/

@[expose] public section

namespace CryptisExamples.NSL

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode BigSepFinset

/-- The participants of a session and the nonces that they contribute. -/
@[rocq_alias cryptis.examples.nsl.sess_info]
structure SessInfo where
  init : Key .aenc
  resp : Key .aenc
  initShare : Term
  respShare : Term

attribute [rocq_alias cryptis.examples.nsl.SessInfo] SessInfo.mk
attribute [rocq_alias cryptis.examples.nsl.si_init] SessInfo.init
attribute [rocq_alias cryptis.examples.nsl.si_resp] SessInfo.resp
attribute [rocq_alias cryptis.examples.nsl.si_init_share] SessInfo.initShare
attribute [rocq_alias cryptis.examples.nsl.si_resp_share] SessInfo.respShare

namespace SessInfo

/-- The session key, derived from both public keys and both nonces. -/
@[rocq_alias cryptis.examples.nsl.si_key]
def key (si : SessInfo) : Key .senc :=
  ⟨Spec.ofList [Spec.pkey si.init, Spec.pkey si.resp, si.initShare, si.respShare]⟩

@[rocq_alias cryptis.examples.nsl.nsl_session_agree]
theorem key_injective : Function.Injective key := by
  rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
  simp_all [key, Key.pkey_injective.eq_iff]

end SessInfo

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The first message carries the nonce of the initiator `skI`, which is public exactly when one
of the participants is compromised. -/
@[rocq_alias cryptis.examples.nsl.msg1_pred]
abbrev msg1Pred (skR : Key .aenc) (m1 : Term) : IProp GF :=
  iprop(∃ (nI : Term) (skI : Key .aenc), ⌜m1 = Spec.ofList [nI, Spec.pkey skI]⌝ ∧
    (isPublic nI ↔ ▷ (isPublic skI ∨ isPublic skR)))

/-- The second message carries the nonce of the responder `skR`, which is public exactly when one
of the participants is compromised. -/
@[rocq_alias cryptis.examples.nsl.msg2_pred]
abbrev msg2Pred (skI : Key .aenc) (m2 : Term) : IProp GF :=
  iprop(∃ (nI nR : Term) (skR : Key .aenc), ⌜m2 = Spec.ofList [nI, nR, Spec.pkey skR]⌝ ∧
    (isPublic nR ↔ ▷ (isPublic skI ∨ isPublic skR)))

/-- The third message needs no invariant. -/
@[rocq_alias cryptis.examples.nsl.msg3_pred]
abbrev msg3Pred (_skR : Key .aenc) (_nR : Term) : IProp GF := iprop(True)

/-- The message predicates of the protocol. -/
@[rocq_alias cryptis.examples.nsl.nsl_ctx]
abbrev nslCtx : IProp GF :=
  iprop(keyPred .aenc (nslN.@"m1") msg1Pred ∧ keyPred .aenc (nslN.@"m2") msg2Pred ∧
    keyPred .aenc (nslN.@"m3") msg3Pred)

@[rocq_alias cryptis.examples.nsl.nsl_ctx_persistent]
instance nslCtx_persistent : Persistent (nslCtx (GF := GF)) := inferInstance

@[rocq_alias cryptis.examples.nsl.nsl_alloc]
theorem nslCtx_alloc {E₁ E₂ : CoPset} (h : ↑nslN ⊆ E₁) :
    sealPredToken .aenc E₁ ={E₂}=∗ nslCtx ∗ sealPredToken .aenc (E₁ \ ↑nslN) := by
  iintro Htok
  rw [(sealPredToken_difference h).to_eq]
  icases Htok with ⟨Htok, Htok'⟩
  imod keyPred_set .aenc (nslN.@"m1") msg1Pred (by solve_ndisj) $$ Htok with ⟨#H1, Htok⟩
  imod keyPred_set .aenc (nslN.@"m2") msg2Pred (by solve_ndisj) $$ Htok with ⟨#H2, Htok⟩
  imod keyPred_set .aenc (nslN.@"m3") msg3Pred (by solve_ndisj) $$ Htok with ⟨#H3, -⟩
  imodintro
  unfold nslCtx
  iframe Htok' H1 H2 H3

/-- A session between `skI` and `skR`: its key is minted, and public exactly when one of them is
compromised. -/
@[rocq_alias cryptis.examples.nsl.session_NSL]
abbrev sessionNSL (skI skR : Key .aenc) (si : SessInfo) : IProp GF :=
  iprop(⌜skI = si.init⌝ ∗ ⌜skR = si.resp⌝ ∗ minted si.key ∗
    □ (isPublic si.key ↔ ▷ (isPublic skI ∨ isPublic skR)))

/-- A session is established once `nR` is public exactly when one of `skI` and `skR` is
compromised, and `nI` is public if one of them is. -/
theorem sessionNSL_intro (skI skR : Key .aenc) (nI nR : Term) :
    minted skI -∗ minted skR -∗ minted nI -∗ minted nR -∗
    □ (▷ (isPublic skI ∨ isPublic skR) → isPublic nI) -∗
    □ (isPublic nR ↔ ▷ (isPublic skI ∨ isPublic skR)) -∗
    sessionNSL skI skR ⟨skI, skR, nI, nR⟩ := by
  iintro #HmI #HmR #HmnI #HmnR #HsnI #HsnR
  ihave #HpI := (isPublic_pkey_aenc skI).mpr $$ HmI
  ihave #HpR := (isPublic_pkey_aenc skR).mpr $$ HmR
  unfold sessionNSL SessInfo.key
  simp only [(minted_coe_key _).to_eq, (isPublic_coe_key _).to_eq,
    minted_ofList_cons_cons, minted_ofList_singleton, isPublic_ofList_cons_cons,
    isPublic_ofList_singleton, (minted_pkey _).to_eq]
  iframe HmI HmR HmnI HmnR
  iintro !>
  isplit
  · iintro ⟨-, -, -, #HpnR⟩
    iapply HsnR $$ HpnR
  · iintro #Hfail
    iframe HpI HpR
    isplit
    · iapply HsnI $$ Hfail
    · iapply HsnR $$ Hfail

set_option hygiene false in
/-- Return `none` from a failed run. -/
local macro "protocol_failure" : tactic =>
  `(tactic| ((try wp_pures); iapply Hpost $$ %none; ileft; ipureintro; rfl))

@[rocq_alias cryptis.examples.nsl.wp_init]
theorem wp_init (c : Val) (skI skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skI ∗ minted skR }}
      hl(&init &c &(encode skI) &(encode (Spec.pkey skR)))
    {{ (r : Option Term), RET encode r;
      ⌜r = none⌝ ∨ ∃ si : SessInfo, ⌜r = some ↑si.key⌝ ∗ sessionNSL skI skR si ∗
        termToken si.initShare ⊤ }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#H1, #H2, #H3⟩, #HmI, #HmR⟩ Hpost
  ihave #HpI := (isPublic_pkey_aenc skI).mpr $$ HmI
  ihave #HpR := (isPublic_pkey_aenc skR).mpr $$ HmR
  wp_rec
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_apply HL.wp_mkNonce (fun _ => iprop(isPublic skI ∨ isPublic skR)) (fun _ => iprop(False))
    $$ Hctx with %nI #HmnI #HsnI - - Htok
  simp only [later_intuitionistically_eq]
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_aenc skR (nslN.@"m1") (Spec.ofList [↑nI, Spec.pkey skI]) msg1Pred
    $$ H1 HmR [] [] with %m1 #Hm1
  · simp only [minted_ofList_cons_cons, minted_ofList_singleton, (minted_pkey _).to_eq]
    iframe HmnI HmI
  · iright
    isplit
    · iintro !>
      iexists ↑nI, skI
      iframe HsnI
      ipureintro; rfl
    · iintro !> #HpskR
      simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
      iframe HpI
      iapply HsnI
      inext
      iright
      iexact HpskR
  wp_pures
  wp_apply HL.wp_send $$ Hc Hm1
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m2 #Hm2
  wp_apply HL.wp_adec skI (nslN.@"m2") m2 msg2Pred $$ H2 Hm2
  isplit
  on_goal 2 => protocol_failure
  iintro %m2 #Hmm2 #Hinv2
  wp_list_of_term ts
  on_goal 2 => protocol_failure
  wp_list_match nI' nR pkR'
  on_goal 2 => protocol_failure
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  icases (minted_ofList _).mp $$ Hmm2 with ⟨-, #HmnR, -⟩
  ihave #HsnR : □ (isPublic nR ↔ ▷ (isPublic skI ∨ isPublic skR)) $$ [#]
  · iintro !>
    icases Hinv2 with (#Hp | ⟨#Hinv2, -⟩)
    · icases (isPublic_ofList _).mp $$ Hp with ⟨#HpnI, #HpnR, -⟩
      isplit
      · iintro -; iapply HsnI $$ HpnI
      · iintro -; iexact HpnR
    · icases Hinv2 with ⟨%nI', %nR', %skR', %e, #HsnR⟩
      simp [Key.pkey_injective.eq_iff] at e
      obtain ⟨-, rfl, rfl⟩ := e
      iexact HsnR
  wp_pures
  wp_apply HL.wp_aenc skR (nslN.@"m3") nR msg3Pred $$ H3 HmR HmnR [] with %m3 #Hm3
  · iright
    isplit
    · iintro !>; itrivial
    · iintro !> #HpskR
      iapply HsnR
      inext
      iright
      iexact HpskR
  wp_pures
  wp_apply HL.wp_send $$ Hc Hm3
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_deriveSEncKey
  wp_pures
  imodintro
  iapply Hpost $$ %(some _)
  iright
  iexists ⟨skI, skR, nI, nR⟩
  iframe Htok
  isplitr
  · ipureintro; rfl
  iapply sessionNSL_intro $$ HmI HmR HmnI HmnR [] HsnR
  iintro !> #Hfail
  iapply HsnI $$ Hfail

@[rocq_alias cryptis.examples.nsl.wp_resp]
theorem wp_resp (c : Val) (skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skR }}
      hl(&resp &c &(encode skR))
    {{ (r : Option (Term × Term)), RET encode r;
      ⌜r = none⌝ ∨ ∃ (skI : Key .aenc) (si : SessInfo), ⌜r = some (Spec.pkey skI, ↑si.key)⌝ ∗
        sessionNSL skI skR si ∗ termToken si.respShare ⊤ }} := by
  iintro %Ψ ⟨#Hc, #Hctx, ⟨#H1, #H2, #H3⟩, #HmR⟩ Hpost
  ihave #HpR := (isPublic_pkey_aenc skR).mpr $$ HmR
  wp_rec
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m1 #Hm1
  wp_apply HL.wp_adec skR (nslN.@"m1") m1 msg1Pred $$ H1 Hm1
  isplit
  on_goal 2 => protocol_failure
  iintro %m1 #Hmm1 #Hinv1
  wp_list_of_term ts
  on_goal 2 => protocol_failure
  wp_list_match nI pkI
  on_goal 2 => protocol_failure
  icases (minted_ofList _).mp $$ Hmm1 with ⟨#HmnI, #HmpkI, -⟩
  wp_apply HL.wp_isAEncKey pkI $$ HmpkI
  isplit
  on_goal 2 => protocol_failure
  iintro %skI %rfl #HmI
  wp_pures
  ihave #HsnI : □ (▷ (isPublic skI ∨ isPublic skR) → isPublic nI) $$ [#]
  · iintro !>
    icases Hinv1 with (#Hp | ⟨#Hinv1, -⟩)
    · icases (isPublic_ofList _).mp $$ Hp with ⟨#HpnI, -⟩
      iintro -
      iexact HpnI
    · iintro #Hfail
      icases Hinv1 with ⟨%nI', %skI', %e, #HsnI⟩
      simp [Key.pkey_injective.eq_iff] at e
      obtain ⟨rfl, rfl⟩ := e
      iapply HsnI $$ Hfail
  wp_apply HL.wp_mkNonce_freshN ∅ (fun _ => iprop(isPublic skI ∨ isPublic skR))
      (fun _ => iprop(False))
      (fun nR => {(nR : Term), ↑(⟨Spec.ofList [Spec.pkey skI, Spec.pkey skR, nI, nR]⟩ : Key .senc)})
    $$ Hctx [] [] with %nR - #HmnR #HsnR - - Htoks
  · iintro %t %ht
    simp at ht
  · iintro %nR
    iapply bigSepFinset_forall.mpr
    iintro %t %ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · iintro !>
      isplit <;> iintro #H <;> iexact H
    · simp only [(minted_coe_key _).to_eq, minted_ofList_cons_cons, minted_ofList_singleton,
        (minted_pkey _).to_eq]
      iintro !>
      isplit
      · iintro #HmnR
        iframe HmI HmR HmnI HmnR
      · iintro ⟨-, -, -, #HmnR⟩
        iexact HmnR
  simp only [later_intuitionistically_eq]
  rw [(bigSepFinset_insert (by simp)).to_eq, (bigSepFinset_singleton _).to_eq]
  icases Htoks with ⟨Htok, -⟩
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_aenc skI (nslN.@"m2") (Spec.ofList [nI, ↑nR, Spec.pkey skR]) msg2Pred
    $$ H2 HmI [] [] with %m2 #Hm2
  · simp only [minted_ofList_cons_cons, minted_ofList_singleton, (minted_pkey _).to_eq]
    iframe HmnI HmnR HmR
  · iright
    isplit
    · iintro !>
      iexists nI, ↑nR, skR
      iframe HsnR
      ipureintro; rfl
    · iintro !> #HpskI
      simp only [isPublic_ofList_cons_cons, isPublic_ofList_singleton]
      iframe HpR
      isplit
      · iapply HsnI
        inext
        ileft
        iexact HpskI
      · iapply HsnR
        inext
        ileft
        iexact HpskI
  wp_pures
  wp_apply HL.wp_send $$ Hc Hm2
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m3 #Hm3
  wp_apply HL.wp_adec skR (nslN.@"m3") m3 msg3Pred $$ H3 Hm3
  isplit
  on_goal 2 => protocol_failure
  iintro %m3 - -
  wp_pures
  wp_eq_term e
  on_goal 2 => protocol_failure
  subst e
  wp_pures
  wp_list
  wp_term_of_list
  wp_apply HL.wp_deriveSEncKey
  wp_pures
  imodintro
  iapply Hpost $$ %(some (_, _))
  iright
  iexists skI, ⟨skI, skR, nI, nR⟩
  iframe Htok
  isplitr
  · ipureintro; rfl
  iapply sessionNSL_intro $$ HmI HmR HmnI HmnR HsnI HsnR

end CryptisExamples.NSL
