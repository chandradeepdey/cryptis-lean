module

public import Cryptis.Lib.DH
public import Cryptis.Role
public import CryptisExamples.IsoDH.Impl

/-! The invariants of the ISO-DH protocol.

A session records both signing keys, both shares and the shared secret. Each use of the protocol,
named by a namespace `N`, fixes two things: the resources that the two sides hand each other when
a session completes, and the condition under which a session key may be released to the attacker.
A session that completes is either compromised, meaning that the signature its owner checked may
have been forged by an attacker holding a long-term key, or its key is public exactly when the
session was released.

- The ghost state lets each use `N` register its resources and release condition with
  `isoDHPred`.
- `session` is what a completed run guarantees, and the lemmas after it take it apart.
- Each side escrows the resources it gives in `isoDHReady`, and its peer redeems them with the
  token of its own share.
- The message invariants attach to the second message the share of the responder and its view of
  the session, and to the third one the initiator's confirmation of that view. `isoDHCtx`
  registers them. -/

@[expose] public section

namespace CryptisExamples.IsoDH

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Term

/-- The participants of a session, their shares and the shared secret. -/
@[rocq_alias cryptis.examples.iso_dh.sess_info]
structure SessInfo where
  init : Key .sign
  resp : Key .sign
  initShare : Term
  respShare : Term
  secret : Term
deriving Inhabited

attribute [rocq_alias cryptis.examples.iso_dh.SessInfo] SessInfo.mk
attribute [rocq_alias cryptis.examples.iso_dh.si_init] SessInfo.init
attribute [rocq_alias cryptis.examples.iso_dh.si_resp] SessInfo.resp
attribute [rocq_alias cryptis.examples.iso_dh.si_init_share] SessInfo.initShare
attribute [rocq_alias cryptis.examples.iso_dh.si_resp_share] SessInfo.respShare
attribute [rocq_alias cryptis.examples.iso_dh.si_secret] SessInfo.secret
attribute [rocq_alias cryptis.examples.iso_dh.sess_info_inhabited] instInhabitedSessInfo

namespace SessInfo

/-- The share that the participant `rl` contributes to a session. -/
@[rocq_alias cryptis.examples.iso_dh.si_share_of]
abbrev shareOf : Role → SessInfo → Term
  | .init => initShare
  | .resp => respShare

/-- The session key, derived from both public keys, both shares and the shared secret. -/
@[rocq_alias cryptis.examples.iso_dh.si_key]
def key (si : SessInfo) : Key .senc :=
  ⟨Spec.ofList [Spec.pkey si.init, Spec.pkey si.resp, si.initShare, si.respShare, si.secret]⟩

@[rocq_alias cryptis.examples.iso_dh.session_agree]
theorem key_injective : Function.Injective key := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  simp_all [key, Key.pkey_injective.eq_iff]

end SessInfo

/-- The ghost state of ISO-DH, without its ghost name. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dhGpreS]
class IsoDHGpreS (GF : BundledGFunctors) where
  metaGS : MetaGS GF
  savedPred : SavedPredG GF (SessInfo × Option Role)

/-- The ghost state of ISO-DH. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dhGS]
class IsoDHGS (GF : BundledGFunctors) extends IsoDHGpreS GF where
  name : GName

attribute [rocq_alias cryptis.examples.iso_dh.IsoDhGPreS] IsoDHGpreS.mk
attribute [rocq_alias cryptis.examples.iso_dh.iso_dhGpreS_meta] IsoDHGpreS.metaGS
attribute [rocq_alias cryptis.examples.iso_dh.iso_dhGpreS_pred] IsoDHGpreS.savedPred
attribute [rocq_alias cryptis.examples.iso_dh.IsoDhGS] IsoDHGS.mk
attribute [rocq_alias cryptis.examples.iso_dh.iso_dh_inG] IsoDHGS.toIsoDHGpreS
attribute [rocq_alias cryptis.examples.iso_dh.iso_dh_name] IsoDHGS.name

#rocq_ignore cryptis.examples.iso_dh.«iso_dhΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.examples.iso_dh.subG_iso_dhGpreS
  "Subsumed by BundledGFunctors typeclass synthesis"

attribute [local instance_reducible, local instance] IsoDHGpreS.metaGS IsoDHGpreS.savedPred

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

section Ghost

variable [IsoDHGS GF]

/-- The right to register the usages of the namespaces in `E`. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_token]
def isoDHToken (E : CoPset) : IProp GF := gmetaToken (IsoDHGS.name GF) E

/-- The usage `N` gives `φ si rl` to the participant `rl` of a completed session, and releases
its key when `ρ si` holds: one saved predicate, at `some rl` and at `none`. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_pred]
def isoDHPred (N : Namespace) (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF) :
    IProp GF :=
  nown (IsoDHGS.name GF) N <| savedPred .discard fun p : SessInfo × Option Role =>
    match p.2 with
    | some rl => φ p.1 rl
    | none => ρ p.1

instance isoDHPred_persistent (N : Namespace) (φ : SessInfo → Role → IProp GF)
    (ρ : SessInfo → IProp GF) : Persistent (isoDHPred N φ ρ) := by
  unfold isoDHPred; infer_instance

variable {N : Namespace} {E E₁ E₂ : CoPset} {φ φ' : SessInfo → Role → IProp GF}
  {ρ ρ' : SessInfo → IProp GF}

@[rocq_alias cryptis.examples.iso_dh.iso_dh_pred_set]
theorem isoDHPred_set (N : Namespace) (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF)
    (h : ↑N ⊆ E) : isoDHToken E ==∗ isoDHPred N φ ρ ∗ isoDHToken (E \ ↑N) :=
  nown_alloc _ h (savedPred_valid.mpr DFrac.valid_discard)

@[rocq_alias cryptis.examples.iso_dh.iso_dh_token_difference]
theorem isoDHToken_difference (h : E₁ ⊆ E₂) :
    isoDHToken (GF := GF) E₂ ⊣⊢ isoDHToken E₁ ∗ isoDHToken (E₂ \ E₁) :=
  gmetaToken_difference h

@[rocq_alias cryptis.examples.iso_dh.iso_dh_token_drop]
theorem isoDHToken_drop (h : E₁ ⊆ E₂) : isoDHToken (GF := GF) E₂ -∗ isoDHToken E₁ :=
  gmetaToken_drop h

@[rocq_alias cryptis.examples.iso_dh.iso_dh_pred_agree]
theorem isoDHPred_agree :
    isoDHPred N φ ρ -∗ isoDHPred N φ' ρ' -∗
      (∀ si rl, ▷ (φ si rl ≡ φ' si rl)) ∗ (∀ si, ▷ (ρ si ≡ ρ' si)) := by
  unfold isoDHPred
  iintro #H1 #H2
  ihave #Hv := nown_valid_2 $$ H1 H2
  icases savedPred_op_validI.mp $$ Hv with ⟨-, #Heq⟩
  isplitl
  · iintro %si %rl
    iapply Heq $$ %(si, some rl)
  · iintro %si
    iapply Heq $$ %(si, none)

end Ghost

/-! ### Key shares -/

@[rocq_alias cryptis.examples.iso_dh.wp_mk_keyshare]
theorem wp_mkKeyShare (t : Term) (Ψ : Val → IProp GF) {s : Stuckness} {E : CoPset} :
    Ψ (encode ((int 0).exp t)) ⊢ WP hl(&mkKeyShare &(encode t)) @ s; E {{ Ψ }} := by
  iintro H
  wp_rec
  wp_apply HL.wp_tint
  wp_apply HL.wp_texp_exp
  iexact H

variable [CryptisGS GF]

/-- The responder records the usage of a session at its share, which ties the last message of
the initiator to it. -/
@[rocq_alias cryptis.examples.iso_dh.usage]
def usage (gb : Term) (N : Namespace) : IProp GF := termMeta gb (isoDHN.@"usage") N

instance usage_persistent (gb : Term) (N : Namespace) : Persistent (usage (GF := GF) gb N) := by
  unfold usage; infer_instance

/-- When `rl` completed `si`, it could not rule out a forged signature. -/
@[rocq_alias cryptis.examples.iso_dh.compromised]
def compromised (rl : Role) (si : SessInfo) : IProp GF :=
  termMeta (si.shareOf rl) (isoDHN.@"compromised") true

@[rocq_alias cryptis.examples.iso_dh.compromised_persistent]
instance compromised_persistent (rl : Role) (si : SessInfo) :
    Persistent (compromised (GF := GF) rl si) := by
  unfold compromised; infer_instance

@[rocq_alias cryptis.examples.iso_dh.compromised_timeless]
instance compromised_timeless (rl : Role) (si : SessInfo) :
    Timeless (compromised (GF := GF) rl si) := by
  unfold compromised; infer_instance

/-- A session completed by `rl`: compromised, with a leaked long-term key (and a public session
key, for the initiator), or with a key that is public exactly when the session is released. -/
@[rocq_alias cryptis.examples.iso_dh.session]
abbrev session (ρ : SessInfo → IProp GF) (rl : Role) (si : SessInfo) : IProp GF :=
  iprop(minted si.key ∗ □ (▷ □ ρ si → isPublic si.key) ∗
    (compromised rl si ∗ (isPublic si.init ∨ isPublic si.resp) ∗
        (match rl with | .init => isPublic si.key | .resp => True) ∨
      □ (compromised rl si → False) ∗ □ (isPublic si.key → ▷ □ ρ si)))

@[rocq_alias cryptis.examples.iso_dh.session_persistent]
instance session_persistent (ρ : SessInfo → IProp GF) (rl : Role) (si : SessInfo) :
    Persistent (session ρ rl si) := by
  cases rl <;> infer_instance

variable {ρ : SessInfo → IProp GF} {rl : Role} {si : SessInfo}

@[rocq_alias cryptis.examples.iso_dh.session_minted]
theorem session_minted : session ρ rl si -∗ minted si.key := by
  iintro ⟨#H, -⟩
  iexact H

@[rocq_alias cryptis.examples.iso_dh.session_release]
theorem session_release : session ρ rl si -∗ □ (▷ □ ρ si → isPublic si.key) := by
  iintro ⟨-, #H, -⟩
  iexact H

@[rocq_alias cryptis.examples.iso_dh.session_ok]
theorem session_ok :
    session ρ rl si -∗ (compromised rl si → False) -∗ □ (isPublic si.key ↔ ▷ □ ρ si) := by
  iintro ⟨-, #Hrel, (⟨#Hc, -⟩ | ⟨-, #Hok⟩)⟩ Hnc
  · iexfalso
    iapply Hnc $$ Hc
  · iintro !>
    isplit
    · iexact Hok
    · iexact Hrel

@[rocq_alias cryptis.examples.iso_dh.session_compromised]
theorem session_compromised :
    session ρ rl si -∗ compromised rl si -∗
      (isPublic si.init ∨ isPublic si.resp) ∗
        (match rl with | .init => isPublic si.key | .resp => True) := by
  iintro ⟨-, -, (⟨-, #Hl, Hp⟩ | ⟨#Hnc, -⟩)⟩ #Hc
  · isplitr
    · iexact Hl
    · iexact Hp
  · iexfalso
    iapply Hnc $$ Hc

@[rocq_alias cryptis.examples.iso_dh.secret_session]
theorem secret_session :
    secret si.init -∗ secret si.resp -∗ session ρ rl si -∗ ◇ □ (compromised rl si → False) := by
  iintro HsI HsR ⟨-, -, (⟨-, (#Hl | #Hl), -⟩ | ⟨#Hnc, -⟩)⟩
  · ihave H := secret_not_isPublic _ $$ HsI Hl
    imod H with ⟨⟩
  · ihave H := secret_not_isPublic _ $$ HsR Hl
    imod H with ⟨⟩
  · iintro !> !>
    iexact Hnc

variable [IsoDHGS GF] {N : Namespace} {φ : SessInfo → Role → IProp GF}

/-- The resources that a participant escrows for its peer `rl`, which `rl` redeems once with the
`ready` part of the token of its share. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_ready]
def isoDHReady (N : Namespace) (si : SessInfo) (rl : Role) : IProp GF :=
  iprop(∀ φ ρ, isoDHPred N φ ρ → termToken (si.shareOf rl) ↑(isoDHN.@"ready") ={⊤}=∗ ▷ φ si rl)

@[rocq_alias cryptis.examples.iso_dh.iso_dh_ready_alloc]
theorem isoDHReady_alloc (N : Namespace) (si : SessInfo) (rl : Role) :
    isoDHPred N φ ρ -∗ φ si rl ={⊤}=∗ □ isoDHReady N si rl := by
  iintro #Hφ Hts
  ihave Hsw := termToken_switch (si.shareOf rl) (isoDHN.@"ready") (φ si rl)
  imod escrow_intro nroot ⊤ _ _ $$ [Hts] Hsw with #He
  · inext; iexact Hts
  unfold isoDHReady
  iintro !> !> %φ' %ρ' #Hφ' Hready
  icases isoDHPred_agree $$ Hφ Hφ' with ⟨#Heq, -⟩
  ispecialize Heq $$ %si %rl
  imod escrow_elim CoPset.subseteq_top _ _ $$ He Hready with Hres
  iintro !> !>
  irewrite [← Heq]
  · exact OFE.id_ne
  iexact Hres

/-- The second message carries the share `g^b` of the responder `skR`, the usage `N` of the
session, the condition for releasing its key, and the resources it escrows for the initiator. -/
@[rocq_alias cryptis.examples.iso_dh.msg2_pred]
abbrev msg2Pred (skR : Key .sign) (m2 : Term) : IProp GF :=
  iprop(∃ (ga : Term) (b : Nonce) (skI : Key .sign) (N : Namespace)
      (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF),
    ⌜m2 = Spec.ofList [ga, (int 0).exp b, Spec.pkey skI, ofNamespace N]⌝ ∧
    isoDHPred N φ ρ ∧
    □ (isPublic b ↔ ▷ □ ρ ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩) ∧
    (∀ t, expPred b t ↔ ▷ □ dhKeyShare t) ∧
    usage ((int 0).exp b) N ∧
    isoDHReady N ⟨skI, skR, ga, (int 0).exp b, ga.exp b⟩ .init)

/-- The third message carries the share `g^a` of the initiator `skI` and, unless a long-term key
leaked, confirms the usage, the release condition and the escrow of the initiator. -/
@[rocq_alias cryptis.examples.iso_dh.msg3_pred]
abbrev msg3Pred (skI : Key .sign) (m3 : Term) : IProp GF :=
  iprop(∃ (a : Nonce) (gb : Term) (skR : Key .sign),
    ⌜m3 = Spec.ofList [(int 0).exp a, gb, Spec.pkey skR]⌝ ∧
    ((isPublic skI ∨ isPublic skR) ∨
      ∃ (N : Namespace) (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF),
        usage gb N ∧ isoDHPred N φ ρ ∧
        □ (isPublic (SessInfo.key ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩) →
          ▷ □ ρ ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩) ∧
        isoDHReady N ⟨skI, skR, (int 0).exp a, gb, gb.exp a⟩ .resp))

/-- The message predicates of the protocol. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_ctx]
abbrev isoDHCtx : IProp GF :=
  iprop(keyPred .sign (isoDHN.@"m2") msg2Pred ∧ keyPred .sign (isoDHN.@"m3") msg3Pred)

@[rocq_alias cryptis.examples.iso_dh.iso_dh_ctx_alloc]
theorem isoDHCtx_alloc {E₁ E₂ : CoPset} (h : ↑isoDHN ⊆ E₁) :
    sealPredToken .sign E₁ ={E₂}=∗ isoDHCtx ∗ sealPredToken .sign (E₁ \ ↑isoDHN) := by
  iintro Htok
  rw [(sealPredToken_difference h).to_eq]
  icases Htok with ⟨Htok, Htok'⟩
  imod keyPred_set .sign (isoDHN.@"m2") msg2Pred (by solve_ndisj) $$ Htok with ⟨#H2, Htok⟩
  imod keyPred_set .sign (isoDHN.@"m3") msg3Pred (by solve_ndisj) $$ Htok with ⟨#H3, -⟩
  imodintro
  unfold isoDHCtx
  iframe Htok' H2 H3

omit [IsoDHGS GF] in
@[rocq_alias cryptis.examples.iso_dh.iso_dhGS_alloc]
theorem isoDHGS_alloc [IsoDHGpreS GF] {E : CoPset} (h : ↑isoDHN ⊆ E) :
    sealPredToken .sign E ={⊤}=∗ ∃ _ : IsoDHGS GF,
      isoDHCtx ∗ isoDHToken ⊤ ∗ sealPredToken .sign (E \ ↑isoDHN) := by
  iintro Htok
  imod gmetaToken_alloc (GF := GF) with ⟨%γ, Hown⟩
  let _ : IsoDHGS GF := ⟨γ⟩
  imod isoDHCtx_alloc (E₂ := ⊤) h $$ Htok with ⟨#Hctx, Htok⟩
  imodintro
  iexists ‹IsoDHGS GF›
  unfold isoDHToken
  iframe Hctx Htok Hown

end CryptisExamples.IsoDH
