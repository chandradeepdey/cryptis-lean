module

public import Cryptis.Tactics
public import Cryptis.Role
public import CryptisExamples.HMQV.Impl

/-! The invariants of the HMQV protocol.

A session completed by a party is either compromised, when the party could not rule out a forged
authenticator, or its key is public only if the session was released. A compromised session has
a public key, and the peer's long-term private key has leaked, if the peer is honest. Ephemeral
private keys are deleted right away, so they never leak.

- Session information: a session records both long-term public keys, which identify the parties,
  both ephemeral public keys and the HMQV key. A session that a role accepts is determined by its
  key (`sessionOf_key_inj`).
- Usages: each use `N` of the protocol registers with `hmqvPred` what each party receives from its
  peer in a session, and the condition under which a session is released. The right to register
  them comes from allocating the ghost state (`hmqvGS_alloc`).
- Each party escrows what it gives its peer in `hmqvReady`, which the peer redeems once with the
  token of its own share.
- Sessions: `session` is what a completed run guarantees to its role, and the lemmas after it take
  it apart.
- Message predicates: the invariants of the two authenticators and of the hash that yields the
  session key. Releasing a session publishes its key through the latter. `hmqvCtx` registers
  them. -/

@[expose] public section

namespace CryptisExamples.HMQV

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode BigSepFinset Term

/-! ### Session information -/

/-- The hash of `t` tagged with `hmqvN.@c`, which `tagHash c` computes. -/
@[rocq_alias cryptis.examples.hmqv.hash_result]
abbrev hashResult (c : String) (t : Term) : Term := .hash (Spec.tag (ofNamespace (hmqvN.@c)) t)

@[rocq_alias cryptis.examples.hmqv.gNX]
theorem isExp_g : g.isExp = false := rfl

@[rocq_alias cryptis.examples.hmqv.gNm]
theorem isProd_g : g.isProd .gmul = false := rfl

@[rocq_alias cryptis.examples.hmqv.tags]
theorem init_ne_resp : "init" ≠ "resp" := by decide

#rocq_ignore cryptis.examples.hmqv.tags' "init_ne_resp.symm"
#rocq_ignore cryptis.examples.hmqv.TExp_g_inj "Cryptis.nonce_eq_of_exp_eq isExp_g isProd_g"
#rocq_ignore cryptis.examples.hmqv.TExp_g_neq_one "Cryptis.ofTerm_exp_ne_one isProd_g"

/-- The participants of a session, their ephemeral public keys, and the HMQV key. -/
@[rocq_alias cryptis.examples.hmqv.sess_info]
structure SessInfo where
  /-- The initiator's long-term public key. -/
  init : Term
  /-- The responder's long-term public key. -/
  resp : Term
  /-- The initiator's ephemeral public key. -/
  initShare : Term
  /-- The responder's ephemeral public key. -/
  respShare : Term
  /-- The HMQV key. -/
  secret : G

attribute [rocq_alias cryptis.examples.hmqv.SessInfo] SessInfo.mk
attribute [rocq_alias cryptis.examples.hmqv.si_init] SessInfo.init
attribute [rocq_alias cryptis.examples.hmqv.si_resp] SessInfo.resp
attribute [rocq_alias cryptis.examples.hmqv.si_init_share] SessInfo.initShare
attribute [rocq_alias cryptis.examples.hmqv.si_resp_share] SessInfo.respShare
attribute [rocq_alias cryptis.examples.hmqv.si_secret] SessInfo.secret

@[rocq_alias cryptis.examples.hmqv.sess_info_inhabited]
instance : Inhabited SessInfo := ⟨⟨default, default, default, default, 1⟩⟩

namespace SessInfo

/-- The ephemeral public key of the role `rl`. -/
@[rocq_alias cryptis.examples.hmqv.si_share_of]
abbrev shareOf : Role → SessInfo → Term
  | .init => initShare
  | .resp => respShare

/-- The long-term public key of the role `rl`. -/
@[rocq_alias cryptis.examples.hmqv.si_static]
abbrev staticOf : Role → SessInfo → Term
  | .init => init
  | .resp => resp

/-- The session key. -/
@[rocq_alias cryptis.examples.hmqv.si_key]
def key (si : SessInfo) : Key .senc := ⟨hashResult "key" (Spec.ofList [↑si.secret])⟩

@[rocq_alias cryptis.examples.hmqv.si_key_inj]
theorem secret_eq_of_key_eq {si₁ si₂ : SessInfo} (h : si₁.key = si₂.key) :
    si₁.secret = si₂.secret := by
  simpa [key, hashResult, Spec.tag_inj, Spec.ofList_inj] using h

end SessInfo

/-- The initiator's view of a session: its own keys are honest, its peer's are whatever came off
the network. -/
@[rocq_alias cryptis.examples.hmqv.init_si]
noncomputable abbrev initSI (pa xa : Nonce) (Pb Xb : Term) : SessInfo :=
  ⟨g.exp pa, Pb, g.exp xa, Xb, hmqvK hmqvN "init" "resp" pa xa (g.exp pa) (g.exp xa) Pb Xb⟩

/-- The responder's view of a session. -/
@[rocq_alias cryptis.examples.hmqv.resp_si]
noncomputable abbrev respSI (Pa Xa : Term) (pb xb : Nonce) : SessInfo :=
  ⟨Pa, g.exp pb, Xa, g.exp xb, hmqvK hmqvN "resp" "init" pb xb (g.exp pb) (g.exp xb) Pa Xa⟩

@[rocq_alias cryptis.examples.hmqv.init_resp_si]
theorem initSI_eq_respSI (pa xa pb xb : Nonce) :
    initSI pa xa (g.exp pb) (g.exp xb) = respSI (g.exp pa) (g.exp xa) pb xb := by
  simp only [initSI, respSI, hmqvK_comm]

/-- A session of the initiator, which accepts it only if neither the peer's long-term key nor the
HMQV key is the unit. -/
@[rocq_alias cryptis.examples.hmqv.init_session]
def initSession (si : SessInfo) : Prop :=
  ∃ pa xa Pb Xb, si = initSI pa xa Pb Xb ∧ G.ofTerm Pb ≠ 1 ∧ si.secret ≠ 1

/-- A session of the responder, which accepts it only if neither the peer's long-term key nor the
HMQV key is the unit. -/
@[rocq_alias cryptis.examples.hmqv.resp_session]
def respSession (si : SessInfo) : Prop :=
  ∃ Pa Xa pb xb, si = respSI Pa Xa pb xb ∧ G.ofTerm Pa ≠ 1 ∧ si.secret ≠ 1

/-- A session of the role `rl`. -/
@[rocq_alias cryptis.examples.hmqv.session_of]
def sessionOf : Role → SessInfo → Prop
  | .init => initSession
  | .resp => respSession

@[rocq_alias cryptis.examples.hmqv.init_session_vetted]
theorem initSession_initSI (pa xa pb : Nonce) (Xb : Term) :
    initSession (initSI pa xa (g.exp pb) Xb) :=
  ⟨pa, xa, _, Xb, rfl, ofTerm_exp_ne_one isProd_g _, hmqvK_ne_one isExp_g isProd_g⟩

@[rocq_alias cryptis.examples.hmqv.resp_session_vetted]
theorem respSession_respSI (pa : Nonce) (Xa : Term) (pb xb : Nonce) :
    respSession (respSI (g.exp pa) Xa pb xb) :=
  ⟨_, Xa, pb, xb, rfl, ofTerm_exp_ne_one isProd_g _, hmqvK_ne_one isExp_g isProd_g⟩

#rocq_ignore cryptis.examples.hmqv.init_si_inj "Inlined in sessionOf_key_inj"
#rocq_ignore cryptis.examples.hmqv.resp_si_inj "Inlined in sessionOf_key_inj"

/-- A session that a role can build is determined by its key. -/
@[rocq_alias cryptis.examples.hmqv.session_of_key_inj]
theorem sessionOf_key_inj {rl : Role} {si₁ si₂ : SessInfo} (h₁ : sessionOf rl si₁)
    (h₂ : sessionOf rl si₂) (h : si₁.key = si₂.key) : si₁ = si₂ := by
  have hs := SessInfo.secret_eq_of_key_eq h
  cases rl
  · obtain ⟨_, _, _, _, rfl, hP, hK⟩ := h₁
    obtain ⟨_, _, _, _, rfl, hP', -⟩ := h₂
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmqvK_inj isExp_g isProd_g init_ne_resp hP hP' hK hs
    rfl
  · obtain ⟨_, _, _, _, rfl, hP, hK⟩ := h₁
    obtain ⟨_, _, _, _, rfl, hP', -⟩ := h₂
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmqvK_inj isExp_g isProd_g init_ne_resp.symm hP hP' hK hs
    rfl

/-- The ghost state of HMQV, without its ghost name. -/
@[rocq_alias cryptis.examples.hmqv.hmqvGpreS]
class HmqvGpreS (GF : BundledGFunctors) where
  metaGS : MetaGS GF
  savedPred : SavedPredG GF (SessInfo × Option Role)

/-- The ghost state of HMQV. -/
@[rocq_alias cryptis.examples.hmqv.hmqvGS]
class HmqvGS (GF : BundledGFunctors) extends HmqvGpreS GF where
  name : GName

attribute [rocq_alias cryptis.examples.hmqv.HmqvGPreS] HmqvGpreS.mk
attribute [rocq_alias cryptis.examples.hmqv.hmqvGpreS_meta] HmqvGpreS.metaGS
attribute [rocq_alias cryptis.examples.hmqv.hmqvGpreS_pred] HmqvGpreS.savedPred
attribute [rocq_alias cryptis.examples.hmqv.HmqvGS] HmqvGS.mk
attribute [rocq_alias cryptis.examples.hmqv.hmqv_inG] HmqvGS.toHmqvGpreS
attribute [rocq_alias cryptis.examples.hmqv.hmqv_name] HmqvGS.name

#rocq_ignore cryptis.examples.hmqv.«hmqvΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.examples.hmqv.subG_hmqvGpreS "Subsumed by BundledGFunctors typeclass synthesis"

attribute [local instance_reducible, local instance] HmqvGpreS.metaGS HmqvGpreS.savedPred

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

@[rocq_alias cryptis.examples.hmqv.wp_H]
theorem wp_tagHash (c : String) (ts : List Term) (Ψ : Val → IProp GF) :
    Ψ (encode (hashResult c (Spec.ofList ts))) ⊢ WP hl(&(tagHash c) &(encode ts)) {{ Ψ }} := by
  unfold hashResult
  iintro H
  wp_rec
  wp_term_of_list
  wp_tag
  wp_hash
  iexact H

theorem minted_g : ⊢ minted (GF := GF) g := true_intro.trans (minted_int 0).mpr

@[rocq_alias cryptis.examples.hmqv.minted_hash_result]
theorem minted_hashResult (c : String) (t : Term) :
    minted (GF := GF) (hashResult c t) ⊣⊢ minted t :=
  (minted_hash _).trans (minted_tag _ _)

theorem minted_coe_key_iff (si : SessInfo) :
    minted (GF := GF) si.key ⊣⊢ minted ↑si.secret := by
  rw [SessInfo.key, (minted_coe_key _).to_eq, (minted_hashResult _ _).to_eq,
    minted_ofList_singleton]
  exact .rfl

@[rocq_alias cryptis.examples.hmqv.minted_si_key]
theorem minted_key (si : SessInfo) : minted (GF := GF) ↑si.secret -∗ minted si.key :=
  entails_wand (minted_coe_key_iff si).mpr

@[rocq_alias cryptis.examples.hmqv.wp_session_key]
theorem wp_sessionKey (σ : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (⟨hashResult "key" (Spec.ofList [σ])⟩ : Key .senc)) ⊢
      WP hl(&sessionKey &(encode σ)) {{ Ψ }} := by
  iintro H
  wp_rec
  wp_list
  wp_apply wp_tagHash
  wp_apply HL.wp_deriveSEncKey
  iexact H

/-! ### Usages -/

section Usage

variable [HmqvGS GF]

/-- The right to register the usages of the namespaces in `E`. -/
@[rocq_alias cryptis.examples.hmqv.hmqv_token]
def hmqvToken (E : CoPset) : IProp GF := gmetaToken (HmqvGS.name GF) E

/-- The usage `N` of the protocol: the party with role `rl` receives `φ si rl` from its peer in the
session `si`, and `ρ si` releases the key of `si`. One saved predicate holds both, the gifts at
`some rl` and the release condition at `none`. -/
@[rocq_alias cryptis.examples.hmqv.hmqv_pred]
def hmqvPred (N : Namespace) (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF) :
    IProp GF :=
  nown (HmqvGS.name GF) N
    (savedPred .discard fun p : SessInfo × Option Role => p.2.elim (ρ p.1) (φ p.1))

instance hmqvPred_persistent (N : Namespace) (φ : SessInfo → Role → IProp GF)
    (ρ : SessInfo → IProp GF) : Persistent (hmqvPred N φ ρ) := by
  unfold hmqvPred; infer_instance

@[rocq_alias cryptis.examples.hmqv.hmqv_pred_set]
theorem hmqvPred_set (N : Namespace) (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF)
    {E : CoPset} (h : ↑N ⊆ E) : hmqvToken E ==∗ hmqvPred N φ ρ ∗ hmqvToken (E \ ↑N) :=
  nown_alloc _ h (savedPred_valid.mpr DFrac.valid_discard)

@[rocq_alias cryptis.examples.hmqv.hmqv_token_difference]
theorem hmqvToken_difference {E₁ E₂ : CoPset} (h : E₁ ⊆ E₂) :
    hmqvToken (GF := GF) E₂ ⊣⊢ hmqvToken E₁ ∗ hmqvToken (E₂ \ E₁) :=
  gmetaToken_difference h

@[rocq_alias cryptis.examples.hmqv.hmqv_token_drop]
theorem hmqvToken_drop {E₁ E₂ : CoPset} (h : E₁ ⊆ E₂) : hmqvToken (GF := GF) E₂ -∗ hmqvToken E₁ :=
  gmetaToken_drop h

variable {N : Namespace} {φ φ' : SessInfo → Role → IProp GF} {ρ ρ' : SessInfo → IProp GF}

@[rocq_alias cryptis.examples.hmqv.hmqv_pred_agree]
theorem hmqvPred_agree :
    hmqvPred N φ ρ -∗ hmqvPred N φ' ρ' -∗
      (∀ si rl, ▷ (φ si rl ≡ φ' si rl)) ∗ (∀ si, ▷ (ρ si ≡ ρ' si)) := by
  unfold hmqvPred
  iintro #H₁ #H₂
  ihave #Hv := nown_valid_2 $$ H₁ H₂
  icases savedPred_op_validI.mp $$ Hv with ⟨-, #Heq⟩
  isplit
  · iintro %si %rl
    ihave H := Heq $$ %(si, some rl)
    simp only [Option.elim_some]
    iexact H
  · iintro %si
    ihave H := Heq $$ %(si, none)
    simp only [Option.elim_none]
    iexact H

end Usage

variable [CryptisGS GF]

theorem isPublic_g : ⊢ isPublic (GF := GF) g := true_intro.trans (isPublic_int 0).mpr

@[rocq_alias cryptis.examples.hmqv.hmqv_key_public]
theorem isPublic_of_hmqvKey (p : Nonce) : hmqvKey (GF := GF) p -∗ isPublic (g.exp p) := by
  unfold hmqvKey
  iintro ⟨#Hm, #He⟩
  iapply isPublic_dh_share isExp_g isProd_g rfl $$ [] Hm He
  iapply isPublic_g

@[rocq_alias cryptis.examples.hmqv.wp_mk_lt_key]
theorem wp_mkLtKey :
    {{ cryptisCtx }}
      hl(&mkLtKey #())
    {{ (p : Nonce), RET encode ((p : Term), g.exp p);
      hmqvKey p ∗ secret (p : Term) ∗ isPublic (g.exp p) ∗ termToken (g.exp p) ⊤ }} := by
  iintro %Φ #Hctx HΦ
  wp_rec
  imod pending_alloc (GF := GF) with ⟨%γ, Hpend⟩
  wp_apply HL.wp_mkNonce_freshN ∅ (fun _ => shot γ 1) dhKeyShare (fun x => {g.exp x})
    $$ Hctx [] [] with %p - #Hm #Hs #He - Htok
  · iintro %t %ht
    simp at ht
  · iintro %x
    iapply (bigSepFinset_singleton _).mpr
    iintro !>
    rw [(minted_exp isExp_g isProd_g _).to_eq]
    isplit
    · iintro #H
      isplit
      · iapply minted_g
      · iexact H
    · iintro ⟨-, #H⟩
      iexact H
  ihave #Hs' : □ (isPublic (p : Term) ↔ ▷ shot γ 1) $$ []
  · simp only [later_intuitionistically_eq]
    iexact Hs
  ihave Hsec := secret_alloc _ γ $$ Hs' Hpend
  ihave #Hkey : hmqvKey p $$ []
  · unfold hmqvKey
    iframe Hm He
  rw [(bigSepFinset_singleton _).to_eq]
  wp_pures
  wp_apply HL.wp_texp_exp
  wp_pures
  iapply HΦ
  iframe Hkey Hsec Htok
  iapply isPublic_of_hmqvKey $$ Hkey

section Ready

variable [HmqvGS GF] {N : Namespace} {φ : SessInfo → Role → IProp GF} {ρ : SessInfo → IProp GF}

/-- The resource that a party escrows for its peer, redeemable once with the `ready` part of the
token of the peer's share. -/
@[rocq_alias cryptis.examples.hmqv.hmqv_ready]
abbrev hmqvReady (N : Namespace) (si : SessInfo) (rl : Role) : IProp GF :=
  iprop(∀ (φ : SessInfo → Role → IProp GF) (ρ : SessInfo → IProp GF), hmqvPred N φ ρ →
    termToken (si.shareOf rl) ↑(hmqvN.@"ready") ={⊤}=∗ ▷ φ si rl)

@[rocq_alias cryptis.examples.hmqv.hmqv_ready_alloc]
theorem hmqvReady_alloc (si : SessInfo) (rl : Role) :
    hmqvPred N φ ρ -∗ φ si rl ={⊤}=∗ □ hmqvReady N si rl := by
  iintro #Hφ H
  imod escrow_intro nroot ⊤ (termToken (si.shareOf rl) ↑(hmqvN.@"ready")) (φ si rl) $$ [H] []
    with #Hesc
  · inext; iexact H
  · iapply termToken_switch
  imodintro
  unfold hmqvReady
  iintro !> %φ' %ρ' #Hφ' Htok
  icases hmqvPred_agree $$ Hφ Hφ' with ⟨#Heq, -⟩
  imod escrow_elim CoPset.subseteq_top _ _ $$ Hesc Htok with H
  imodintro
  ispecialize Heq $$ %si %rl
  inext
  irewrite [← Heq]
  · exact OFE.id_ne
  iexact H

end Ready

@[rocq_alias cryptis.examples.hmqv.public_si_key]
theorem isPublic_key (si : SessInfo) : isPublic (GF := GF) ↑si.secret -∗ isPublic si.key := by
  iintro #H
  rw [SessInfo.key, (isPublic_coe_key _).to_eq, hashResult, (isPublic_hash _).to_eq,
    (isPublic_tag _ _).to_eq, isPublic_ofList_singleton]
  ileft
  iexact H

/-- An ephemeral private key, with the parts of the token of its share that the protocol keeps:
the `hmqvN` part goes to the protocol, and the rest to the caller. -/
@[rocq_alias cryptis.examples.hmqv.wp_mk_ephemeral]
theorem wp_mkEphemeral (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ x : Nonce, hmqvEphemeral x -∗ isPublic (g.exp x) -∗
      termToken (g.exp x) ↑(hmqvN.@"ready") -∗ termToken (g.exp x) ↑(hmqvN.@"usage") -∗
      termToken (g.exp x) ↑(hmqvN.@"compromised") -∗ termToken (g.exp x) (⊤ \ ↑hmqvN) -∗
      Ψ (encode (x : Term))) -∗
    WP hl(&HL.mkNonce #()) {{ Ψ }} := by
  iintro #Hctx HΨ
  iapply HL.wp_mkNonce_freshN ∅ (fun _ => iprop(False)) dhKeyShare (fun x => {g.exp x})
    $$ Hctx [] []
  · iintro %t %ht
    simp at ht
  · iintro %x
    iapply (bigSepFinset_singleton _).mpr
    iintro !>
    rw [(minted_exp isExp_g isProd_g _).to_eq]
    isplit
    · iintro #H
      isplit
      · iapply minted_g
      · iexact H
    · iintro ⟨-, #H⟩
      iexact H
  iintro %x - #Hm #Hs #He - Htok
  rw [(bigSepFinset_singleton _).to_eq]
  ihave #Heph : hmqvEphemeral x $$ []
  · unfold hmqvEphemeral hmqvKey
    iframe Hm He
    simp only [later_intuitionistically_eq]
    iexact Hs
  icases (termToken_difference (E1 := ↑hmqvN) CoPset.subseteq_top).mp $$ Htok
    with ⟨HtN, Htok⟩
  icases (termToken_difference (E1 := ↑(hmqvN.@"ready")) (by solve_ndisj)).mp $$ HtN
    with ⟨Hready, HtN⟩
  icases (termToken_difference (E1 := ↑(hmqvN.@"usage")) (by solve_ndisj)).mp $$ HtN
    with ⟨Husage, HtN⟩
  icases (termToken_difference (E1 := ↑(hmqvN.@"compromised")) (by solve_ndisj)).mp $$ HtN
    with ⟨Hcomp, -⟩
  iapply HΨ $$ %x Heph [] Hready Husage Hcomp Htok
  unfold hmqvEphemeral hmqvKey
  iapply isPublic_dh_share isExp_g isProd_g rfl $$ [] Hm He
  iapply isPublic_g

/-! ### Sessions -/

/-- The responder records the usage `N` of a session on its share `X`, where the hash predicate of
the key finds the release condition. -/
@[rocq_alias cryptis.examples.hmqv.usage]
abbrev usage (X : Term) (N : Namespace) : IProp GF := termMeta X (hmqvN.@"usage") N

/-- When the role `rl` completed `si`, it could not rule out a forged authenticator. -/
@[rocq_alias cryptis.examples.hmqv.compromised]
abbrev compromised (rl : Role) (si : SessInfo) : IProp GF :=
  termMeta (si.shareOf rl) (hmqvN.@"compromised") true

#rocq_ignore cryptis.examples.hmqv.compromised_persistent "Inferred through the abbrev"
#rocq_ignore cryptis.examples.hmqv.compromised_timeless "Inferred through the abbrev"

/-- The private key behind `P`, if `P` is honest, leaked. -/
@[rocq_alias cryptis.examples.hmqv.leaked]
abbrev leaked (P : Term) : IProp GF :=
  iprop(∀ p : Nonce, ⌜P = g.exp p⌝ → hmqvKey p → ◇ isPublic (p : Term))

/-- The confidentiality of the key of `si` from the point of view of `rl`. The second later of
the last disjunct comes from finding the release condition through the usage of the session. -/
@[rocq_alias cryptis.examples.hmqv.session]
abbrev session (ρ : SessInfo → IProp GF) (rl : Role) (si : SessInfo) : IProp GF :=
  iprop(minted si.key ∗ □ (▷ □ ρ si → isPublic si.key) ∗
    (compromised rl si ∗ isPublic si.key ∗ □ leaked (si.staticOf rl.swap) ∨
      □ (¬ compromised rl si) ∗ □ (isPublic si.key → ▷ ▷ □ ρ si)))

@[rocq_alias cryptis.examples.hmqv.session_persistent]
instance session_persistent (ρ : SessInfo → IProp GF) (rl : Role) (si : SessInfo) :
    Persistent (session ρ rl si) := inferInstance

variable {ρ : SessInfo → IProp GF} {rl : Role} {si : SessInfo}

@[rocq_alias cryptis.examples.hmqv.session_minted]
theorem session_minted : session ρ rl si -∗ minted si.key := by
  iintro ⟨#H, -⟩
  iexact H

@[rocq_alias cryptis.examples.hmqv.session_release]
theorem session_release : session ρ rl si -∗ □ (▷ □ ρ si → isPublic si.key) := by
  iintro ⟨-, #H, -⟩
  iexact H

@[rocq_alias cryptis.examples.hmqv.session_ok]
theorem session_ok :
    session ρ rl si -∗ (¬ compromised rl si) -∗ □ (isPublic si.key → ▷ ▷ □ ρ si) := by
  iintro ⟨-, -, (⟨#Hc, -⟩ | ⟨-, #Hok⟩)⟩ Hnc
  · iexfalso
    iapply Hnc $$ Hc
  · iexact Hok

@[rocq_alias cryptis.examples.hmqv.session_compromised]
theorem session_compromised :
    session ρ rl si -∗ compromised rl si -∗ isPublic si.key ∗ □ leaked (si.staticOf rl.swap) := by
  iintro ⟨-, -, (⟨-, #Hp, #Hl⟩ | ⟨#Hnc, -⟩)⟩ #Hc
  · iframe Hp Hl
  · iexfalso
    iapply Hnc $$ Hc

/-- A secret peer key rules out compromise, whatever happens to the role's own long-term key. -/
@[rocq_alias cryptis.examples.hmqv.secret_session]
theorem secret_session (p : Nonce) (h : si.staticOf rl.swap = g.exp p) :
    hmqvKey p -∗ secret (p : Term) -∗ session ρ rl si -∗ ◇ □ (¬ compromised rl si) := by
  iintro #Hkey Hs ⟨-, -, (⟨-, -, #Hl⟩ | ⟨#Hnc, -⟩)⟩
  · imod Hl $$ %p %h Hkey with #Hp
    ihave H := secret_not_isPublic _ $$ Hs Hp
    imod H with ⟨⟩
  · imodintro
    iexact Hnc

/-! ### Message predicates -/

section Ctx

variable [HmqvGS GF]

/-- The authenticator of the responder, computed by an honest responder. The long-term key that
the responder used for its peer is not the unit, so the HMQV key binds it (`hmqvK_inj'`). -/
@[rocq_alias cryptis.examples.hmqv.m2_pred]
noncomputable abbrev m2Pred (t : Term) : IProp GF :=
  iprop(∃ (Pa Xa : Term) (pb xb : Nonce) (N : Namespace),
    ⌜t = Spec.ofList [↑(respSI Pa Xa pb xb).secret, ofNamespace N]⌝ ∗ ⌜G.ofTerm Pa ≠ 1⌝ ∗
    hmqvKey pb ∗ hmqvEphemeral xb ∗ usage (g.exp xb) N ∗ hmqvReady N (respSI Pa Xa pb xb) .init)

/-- The authenticator of the initiator. -/
@[rocq_alias cryptis.examples.hmqv.m3_pred]
noncomputable abbrev m3Pred (t : Term) : IProp GF :=
  iprop(∃ (pa xa : Nonce) (Pb Xb : Term) (N : Namespace),
    ⌜t = Spec.ofList [↑(initSI pa xa Pb Xb).secret, ofNamespace N]⌝ ∗ ⌜G.ofTerm Pb ≠ 1⌝ ∗
    hmqvKey pa ∗ hmqvEphemeral xa ∗ hmqvReady N (initSI pa xa Pb Xb) .resp)

/-- The hash of the key: released sessions publish their key through it. -/
@[rocq_alias cryptis.examples.hmqv.key_pred]
noncomputable abbrev keyPred (t : Term) : IProp GF :=
  iprop(∃ (si : SessInfo) (N : Namespace) (φ : SessInfo → Role → IProp GF)
      (ρ : SessInfo → IProp GF),
    ⌜t = Spec.ofList [↑si.secret]⌝ ∗ ⌜respSession si⌝ ∗ usage si.respShare N ∗
      hmqvPred N φ ρ ∗ □ ρ si)

/-- The hash predicates of the protocol. -/
@[rocq_alias cryptis.examples.hmqv.hmqv_ctx]
noncomputable abbrev hmqvCtx : IProp GF :=
  iprop(hashPred (hmqvN.@"m2") m2Pred ∗ hashPred (hmqvN.@"m3") m3Pred ∗
    hashPred (hmqvN.@"key") keyPred)

instance hmqvCtx_persistent : Persistent (hmqvCtx (GF := GF)) := inferInstance

@[rocq_alias cryptis.examples.hmqv.hmqv_ctx_alloc]
theorem hmqvCtx_alloc {E : CoPset} (h : ↑hmqvN ⊆ E) :
    hashPredToken E ==∗ hmqvCtx ∗ hashPredToken (E \ ↑hmqvN) := by
  iintro Htok
  rw [(hashPredToken_difference h).to_eq]
  icases Htok with ⟨Htok, Htok'⟩
  imod hashPred_set (hmqvN.@"m2") m2Pred (by solve_ndisj) $$ Htok with ⟨#H2, Htok⟩
  imod hashPred_set (hmqvN.@"m3") m3Pred (by solve_ndisj) $$ Htok with ⟨#H3, Htok⟩
  imod hashPred_set (hmqvN.@"key") keyPred (by solve_ndisj) $$ Htok with ⟨#Hk, -⟩
  imodintro
  unfold hmqvCtx
  iframe Htok' H2 H3 Hk

/-- In a session between honest ephemerals, only release can publish the key. -/
@[rocq_alias cryptis.examples.hmqv.honest_session]
theorem honest_session (N : Namespace) (φ : SessInfo → Role → IProp GF)
    (ρ : SessInfo → IProp GF) (pa pb xa xb : Nonce) :
    hashPred (hmqvN.@"key") keyPred -∗ hmqvPred N φ ρ -∗ hmqvKey pa -∗ hmqvKey pb -∗
      hmqvEphemeral xa -∗ hmqvEphemeral xb -∗ usage (g.exp xb) N -∗
      minted (respSI (g.exp pa) (g.exp xa) pb xb).key -∗
      □ (▷ □ ρ (respSI (g.exp pa) (g.exp xa) pb xb) →
          isPublic (respSI (g.exp pa) (g.exp xa) pb xb).key) ∗
        □ (isPublic (respSI (g.exp pa) (g.exp xa) pb xb).key →
          ▷ ▷ □ ρ (respSI (g.exp pa) (g.exp xa) pb xb)) := by
  have ss := respSession_respSI pa (g.exp xa) pb xb
  unfold hmqvEphemeral
  iintro #Hpred #Hφ #Hpa #Hpb ⟨#Hxa, #Hsxa⟩ ⟨#Hxb, #Hsxb⟩ #Huse #Hmk
  isplit
  · iintro !> #Hrel
    ihave #Hm := (minted_coe_key_iff _).mp $$ Hmk
    rw [SessInfo.key, (isPublic_coe_key _).to_eq, hashResult]
    iapply isPublic_hash_intro $$ Hpred []
    · rw [minted_ofList_singleton]
      iexact Hm
    · inext
      iintro !>
      iexists respSI (g.exp pa) (g.exp xa) pb xb, N, φ, ρ
      iframe Huse Hφ Hrel
      ipureintro
      exact ⟨rfl, ss⟩
  · iintro !> #Hpk
    rw [SessInfo.key, (isPublic_coe_key _).to_eq, hashResult]
    icases isPublic_hash_elim $$ Hpred Hpk with (#Hp | ⟨-, #Hrel⟩)
    · rw [isPublic_ofList_singleton]
      icases isPublic_hmqvK_honest isExp_g isProd_g init_ne_resp.symm $$ Hpb Hxb Hpa Hxa Hp with
        (⟨-, #H⟩ | ⟨-, #H⟩)
      · ihave Hf : ▷ False $$ []
        · iapply Hsxb $$ H
        inext
        iexfalso
        iexact Hf
      · ihave Hf : ▷ False $$ []
        · iapply Hsxa $$ H
        inext
        iexfalso
        iexact Hf
    · inext
      icases Hrel with ⟨%si', %N', %φ', %ρ', %e, %ss', #Huse', #Hφ', #Hr⟩
      obtain rfl := sessionOf_key_inj (rl := .resp) ss ss' (by simp [SessInfo.key, e])
      icases termMeta_agree $$ Huse Huse' with %rfl
      icases hmqvPred_agree $$ Hφ Hφ' with ⟨-, #Heq⟩
      ispecialize Heq $$ %(respSI (g.exp pa) (g.exp xa) pb xb)
      inext
      irewrite [Heq]
      iexact Hr

end Ctx

/-- Allocate the ghost state of HMQV and its hash predicates. -/
@[rocq_alias cryptis.examples.hmqv.hmqvGS_alloc]
theorem hmqvGS_alloc [HmqvGpreS GF] {E : CoPset} (h : ↑hmqvN ⊆ E) :
    hashPredToken E ={⊤}=∗ ∃ _ : HmqvGS GF, hmqvCtx ∗ hmqvToken ⊤ ∗
      hashPredToken (E \ ↑hmqvN) := by
  iintro Htok
  imod gmetaToken_alloc (GF := GF) with ⟨%γ, Hγ⟩
  let _ : HmqvGS GF := ⟨γ⟩
  imod hmqvCtx_alloc h $$ Htok with ⟨#Hctx, Htok⟩
  imodintro
  iexists ‹HmqvGS GF›
  unfold hmqvToken
  iframe Hctx Hγ Htok

end CryptisExamples.HMQV
