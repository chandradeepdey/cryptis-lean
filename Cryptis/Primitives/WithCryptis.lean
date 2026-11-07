module

public import Cryptis.Lib.Misc
public import Cryptis.Logic
public import Cryptis.Primitives.Simple

/-! The primitives that need the ghost state of Cryptis: network channels, nonces, keys, and
encryption and signatures specified with the public-term predicates.

A channel is a list of public terms behind a ticket lock. Sending adds a term to the list, and
receiving returns any term of the list, so the attacker sees and may replay every message. A
fresh nonce comes with the right to decide when it is public and which exponentials of it may be
published; a fresh key is a secret, which stays private until its owner decides otherwise. -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode ProgramLogic Term.ProdGroup BigSepFinset

namespace HL

/-! ## Programs -/

/-- The receiving end of the channel `c`, guarded by `lock`. -/
@[rocq_alias cryptis.get_chan]
def getChan : Val := hl_val%
  λ c lock,
    rec loop _ :=
      let n := &nondetNat #();
      &TicketLock.acquire lock;
      let ts := !c;
      &TicketLock.release lock;
      match &getList ts n with
      | none() => loop #()
      | some(t) => t

/-- The sending end of the channel `c`, guarded by `lock`. -/
@[rocq_alias cryptis.put_chan]
def putChan : Val := hl_val%
  λ c lock t,
    &TicketLock.acquire lock;
    c ← t :: !c;
    &TicketLock.release lock

/-- A new channel, as its pair of sending and receiving functions. -/
@[rocq_alias cryptis.mk_channel]
def mkChannel : Val := hl_val%
  λ _,
    let c := ref([]);
    let lock := &TicketLock.newlock #();
    (&putChan c lock, &getChan c lock)

/-- Send a term on a channel. -/
@[rocq_alias cryptis.send]
def send : Val := hl_val% λ c, fst(c)

/-- Receive a term from a channel. -/
@[rocq_alias cryptis.recv]
def recv : Val := hl_val% λ c, snd(c) #()

/-- A fresh nonce. -/
@[rocq_alias cryptis.mk_nonce]
def mkNonce : Val := hl_val% λ _, let n := ref(#()); (#Tag.op0, (#Tag.nonce, n))

/-- A fresh secret key for public-key encryption. -/
@[rocq_alias cryptis.mk_aenc_key]
def mkAEncKey : Val := hl_val% λ _, let n := &mkNonce #(); &deriveAEncKey n

/-- A fresh signing key. -/
@[rocq_alias cryptis.mk_sign_key]
def mkSignKey : Val := hl_val% λ _, let n := &mkNonce #(); &deriveSignKey n

/-- A fresh key for symmetric encryption. -/
@[rocq_alias cryptis.mk_senc_key]
def mkSEncKey : Val := hl_val% λ _, let n := &mkNonce #(); &deriveSEncKey n

end HL

/-! ## Specifications -/

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset}
local bi (IProp GF)

namespace HL

/-! ### Recognising keys -/

@[rocq_alias cryptis.twp_is_aenc_key]
theorem twp_isAEncKey (pk : Term) (Ψ : Val → IProp GF) :
    minted pk -∗
    ((∀ sk : Key .aenc, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ hl_val(#true)) ∧
      Ψ hl_val(#false)) -∗
    WP hl(&isAEncKey &(encode pk)) @ s; E [{ Ψ }] := by
  iintro #Hm H
  twp_rec
  twp_apply twp_hasKeyType .aenc pk
  cases h : Spec.hasKeyType .aenc pk
  · icases H with ⟨-, H⟩; iexact H
  obtain ⟨k, rfl⟩ := Spec.isKey_eq_some_iff.mp (by simpa [Spec.hasKeyType] using h)
  icases H with ⟨H, -⟩
  iapply H $$ %⟨k⟩ %rfl
  iapply (minted_coe_key (F := .aenc) ⟨k⟩).mpr
  iapply (minted_key _ _).mp $$ Hm

@[rocq_alias cryptis.wp_is_aenc_key]
theorem wp_isAEncKey (pk : Term) (Ψ : Val → IProp GF) :
    minted pk -∗
    ((∀ sk : Key .aenc, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ hl_val(#true)) ∧
      Ψ hl_val(#false)) -∗
    WP hl(&isAEncKey &(encode pk)) @ s; E {{ Ψ }} := by
  iintro #Hm H
  iapply twp.to_wp
  iapply twp_isAEncKey pk Ψ $$ Hm H

@[rocq_alias cryptis.twp_is_adec_key]
theorem twp_isADecKey (sk : Term) (Ψ : Val → IProp GF) :
    minted sk -∗ ((∀ sk' : Key .aenc, ⌜sk = sk'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isADecKey &(encode sk)) @ s; E [{ Ψ }] := by
  iintro - H
  twp_rec
  twp_apply twp_hasKeyType .adec sk
  cases h : Spec.hasKeyType .adec sk
  · icases H with ⟨-, H⟩; iexact H
  obtain ⟨k, rfl⟩ := Spec.isKey_eq_some_iff.mp (by simpa [Spec.hasKeyType] using h)
  icases H with ⟨H, -⟩
  iapply H $$ %⟨k⟩ %rfl

@[rocq_alias cryptis.wp_is_adec_key]
theorem wp_isADecKey (sk : Term) (Ψ : Val → IProp GF) :
    minted sk -∗ ((∀ sk' : Key .aenc, ⌜sk = sk'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isADecKey &(encode sk)) @ s; E {{ Ψ }} := by
  iintro #Hm H
  iapply twp.to_wp
  iapply twp_isADecKey sk Ψ $$ Hm H

@[rocq_alias cryptis.twp_is_senc_key]
theorem twp_isSEncKey (k : Term) (Ψ : Val → IProp GF) :
    minted k -∗ ((∀ k' : Key .senc, ⌜k = k'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isSEncKey &(encode k)) @ s; E [{ Ψ }] := by
  iintro - H
  twp_rec
  twp_apply twp_hasKeyType .senc k
  cases h : Spec.hasKeyType .senc k
  · icases H with ⟨-, H⟩; iexact H
  obtain ⟨k, rfl⟩ := Spec.isKey_eq_some_iff.mp (by simpa [Spec.hasKeyType] using h)
  icases H with ⟨H, -⟩
  iapply H $$ %⟨k⟩ %rfl

@[rocq_alias cryptis.wp_is_senc_key]
theorem wp_isSEncKey (k : Term) (Ψ : Val → IProp GF) :
    minted k -∗ ((∀ k' : Key .senc, ⌜k = k'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isSEncKey &(encode k)) @ s; E {{ Ψ }} := by
  iintro #Hm H
  iapply twp.to_wp
  iapply twp_isSEncKey k Ψ $$ Hm H

@[rocq_alias cryptis.twp_is_verify_key]
theorem twp_isVerifyKey (pk : Term) (Ψ : Val → IProp GF) :
    minted pk -∗
    ((∀ sk : Key .sign, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ hl_val(#true)) ∧
      Ψ hl_val(#false)) -∗
    WP hl(&isVerifyKey &(encode pk)) @ s; E [{ Ψ }] := by
  iintro #Hm H
  twp_rec
  twp_apply twp_hasKeyType .verify pk
  cases h : Spec.hasKeyType .verify pk
  · icases H with ⟨-, H⟩; iexact H
  obtain ⟨k, rfl⟩ := Spec.isKey_eq_some_iff.mp (by simpa [Spec.hasKeyType] using h)
  icases H with ⟨H, -⟩
  iapply H $$ %⟨k⟩ %rfl
  iapply (minted_coe_key (F := .sign) ⟨k⟩).mpr
  iapply (minted_key _ _).mp $$ Hm

@[rocq_alias cryptis.wp_is_verify_key]
theorem wp_isVerifyKey (pk : Term) (Ψ : Val → IProp GF) :
    minted pk -∗
    ((∀ sk : Key .sign, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ hl_val(#true)) ∧
      Ψ hl_val(#false)) -∗
    WP hl(&isVerifyKey &(encode pk)) @ s; E {{ Ψ }} := by
  iintro #Hm H
  iapply twp.to_wp
  iapply twp_isVerifyKey pk Ψ $$ Hm H

@[rocq_alias cryptis.twp_is_sign_key]
theorem twp_isSignKey (sk : Term) (Ψ : Val → IProp GF) :
    minted sk -∗ ((∀ sk' : Key .sign, ⌜sk = sk'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isSignKey &(encode sk)) @ s; E [{ Ψ }] := by
  iintro - H
  twp_rec
  twp_apply twp_hasKeyType .sign sk
  cases h : Spec.hasKeyType .sign sk
  · icases H with ⟨-, H⟩; iexact H
  obtain ⟨k, rfl⟩ := Spec.isKey_eq_some_iff.mp (by simpa [Spec.hasKeyType] using h)
  icases H with ⟨H, -⟩
  iapply H $$ %⟨k⟩ %rfl

@[rocq_alias cryptis.wp_is_sign_key]
theorem wp_isSignKey (sk : Term) (Ψ : Val → IProp GF) :
    minted sk -∗ ((∀ sk' : Key .sign, ⌜sk = sk'⌝ -∗ Ψ hl_val(#true)) ∧ Ψ hl_val(#false)) -∗
    WP hl(&isSignKey &(encode sk)) @ s; E {{ Ψ }} := by
  iintro #Hm H
  iapply twp.to_wp
  iapply twp_isSignKey sk Ψ $$ Hm H

end HL

variable [CryptisGS GF]

attribute [local instance_reducible, local instance] CryptisGS.tlock

/-! ### Channels -/

/-- `c` is a channel: it sends public terms and receives public terms. -/
@[rocq_alias cryptis.channel]
def channel (c : Val) : IProp GF :=
  iprop(∃ sf rf : Val, ⌜c = hl_val((&sf, &rf))⌝ ∗
    □ (∀ (t : Term) (Ψ : Val → IProp GF), isPublic t -∗ Ψ hl_val(#()) -∗
      WP hl(&sf &(encode t)) {{ Ψ }}) ∗
    □ (∀ Ψ : Val → IProp GF, (∀ t : Term, isPublic t -∗ Ψ (encode t)) -∗
      WP hl(&rf #()) {{ Ψ }}))

@[rocq_alias cryptis.channel_persistent]
instance channel_persistent (c : Val) : Persistent (channel (GF := GF) c) := by
  unfold channel; infer_instance

/-- The invariant of a channel: the list of terms sent so far, all of them public. -/
@[rocq_alias cryptis.chan_inv]
def chanInv (c : Loc) : IProp GF :=
  iprop(∃ ts : List Term, c ↦ some (encode ts) ∗ [∗list] t ∈ ts, isPublic t)

namespace HL

@[rocq_alias cryptis.wp_mk_channel]
theorem wp_mkChannel (Ψ : Val → IProp GF) :
    (∀ c, channel c -∗ Ψ c) ⊢ WP hl(&mkChannel #()) {{ Ψ }} := by
  iintro H
  wp_rec
  wp_pures
  wp_alloc c with Hc
  wp_pures
  wp_apply TicketLock.newlock_spec $$ [//] with %lk %γ Hinit
  imod Hinit $$ %(chanInv c) %⊤ [Hc] with #Hlk
  · unfold chanInv
    iexists []
    simp only [encode_nil]
    iframe Hc
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  unfold getChan putChan chanInv
  wp_pures
  imodintro
  iapply H
  unfold channel
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %t %Ψ #Hp HΨ
    wp_pures
    wp_apply TicketLock.acquire_spec γ lk _ $$ Hlk with ⟨Hlocked, ⟨%ts, Hc, #Hts⟩⟩
    wp_pures
    wp_load
    wp_apply wp_cons t ts
    wp_store
    wp_apply TicketLock.release_spec γ lk _ $$ [Hlocked Hc] with -
    · iframe Hlk Hlocked
      iexists t :: ts
      iframe Hc Hts
      iexact Hp
    iexact HΨ
  · imodintro
    iloeb as IH
    iintro %Ψ HΨ
    wp_rec
    wp_apply wp_nondetNat with %n
    wp_pures
    wp_apply TicketLock.acquire_spec γ lk _ $$ Hlk with ⟨Hlocked, ⟨%ts, Hc, #Hts⟩⟩
    wp_pures
    wp_load
    wp_pures
    wp_apply TicketLock.release_spec γ lk _ $$ [Hlocked Hc] with -
    · iframe Hlk Hlocked
      iexists ts
      iframe Hc Hts
    wp_pures
    wp_apply wp_getList ts n
    cases h : ts[n]? with
    | none => simp only [encode_none]; wp_match; iapply IH $$ HΨ
    | some t =>
      simp only [encode_some]
      wp_pures
      iapply HΨ
      iapply BigSepL.bigSepL_lookup h $$ Hts

@[rocq_alias cryptis.wp_send]
theorem wp_send (c : Val) (t : Term) (Ψ : Val → IProp GF) :
    channel c -∗ ▷ isPublic t -∗ Ψ hl_val(#()) -∗ WP hl(&send &c &(encode t)) {{ Ψ }} := by
  unfold channel
  iintro ⟨%sf, %rf, %rfl, #Hs, -⟩ #Hp HΨ
  wp_rec
  wp_pures
  iapply Hs $$ %t %Ψ Hp HΨ

@[rocq_alias cryptis.wp_recv]
theorem wp_recv (c : Val) (Ψ : Val → IProp GF) :
    channel c -∗ (∀ t : Term, isPublic t -∗ Ψ (encode t)) -∗ WP hl(&recv &c) {{ Ψ }} := by
  unfold channel
  iintro ⟨%sf, %rf, %rfl, -, #Hr⟩ HΨ
  wp_rec
  wp_pures
  iapply Hr $$ %Ψ HΨ

/-! ### Nonces -/

@[rocq_alias cryptis.twp_mk_nonce_gen]
theorem twp_mkNonce_gen (P : Nonce → IProp GF) (Q : Term → IProp GF) (Ψ : Val → IProp GF)
    (Φ : Nonce → IProp GF) :
    (∀ a : Nonce, (minted (a : Term) -∗ False) ∧
        (|==> (minted (a : Term) ∗ □ (isPublic (a : Term) ↔ ▷ □ P a) ∗
          □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t))) ={E}=∗
      minted (a : Term) ∗ □ (isPublic (a : Term) ↔ ▷ □ P a) ∗
        □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) ∗ Φ a) -∗
    (∀ a : Nonce, minted (a : Term) -∗ □ (isPublic (a : Term) ↔ ▷ □ P a) -∗
      □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      Φ a -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; E [{ Ψ }] := by
  iintro Hmint Hpost
  twp_rec
  twp_apply twp_alloc $$ [//] with %l ⟨-, Htok⟩
  ihave Hfresh := nonce_alloc P Q ⟨l⟩ $$ Htok
  imod Hmint $$ %⟨l⟩ Hfresh with ⟨#Hm, #Hp, #He, HΦ⟩
  twp_pures
  simp only [Term.encode_nonce]
  iapply Hpost $$ %⟨l⟩ Hm Hp He [] HΦ
  iintro !> %t
  rw [(expPred_inv (f := Term.E.ofTerm (Term.nonce ⟨l⟩)) rfl t).to_eq]
  isplit <;> iintro H <;> iexact H

@[rocq_alias cryptis.wp_mk_nonce_gen]
theorem wp_mkNonce_gen (P : Nonce → IProp GF) (Q : Term → IProp GF) (Ψ : Val → IProp GF)
    (Φ : Nonce → IProp GF) :
    (∀ a : Nonce, (minted (a : Term) -∗ False) ∧
        (|==> (minted (a : Term) ∗ □ (isPublic (a : Term) ↔ ▷ □ P a) ∗
          □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t))) ={E}=∗
      minted (a : Term) ∗ □ (isPublic (a : Term) ↔ ▷ □ P a) ∗
        □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) ∗ Φ a) -∗
    (∀ a : Nonce, minted (a : Term) -∗ □ (isPublic (a : Term) ↔ ▷ □ P a) -∗
      □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      Φ a -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; E {{ Ψ }} := by
  iintro H1 H2
  iapply twp.to_wp
  iapply twp_mkNonce_gen P Q Ψ Φ $$ H1 H2

@[rocq_alias cryptis.twp_mk_nonce_freshN]
theorem twp_mkNonce_freshN (T : Finset Term) (P : Nonce → IProp GF) (Q : Term → IProp GF)
    (T' : Nonce → Finset Term) (Ψ : Val → IProp GF) :
    cryptisCtx -∗ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
    (∀ a : Nonce, [∗finset] t' ∈ T' a, □ (minted (a : Term) ↔ minted t')) -∗
    (∀ a : Nonce, ⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ -∗ minted (a : Term) -∗
      □ (isPublic (a : Term) ↔ ▷ □ P a) -∗ □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      ([∗finset] t' ∈ T' a, termToken t' ⊤) -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ [{ Ψ }] := by
  iintro #Hctx HT #HT' Hpost
  iapply twp_mkNonce_gen P Q Ψ (fun a => iprop(⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ ∗
      [∗finset] t' ∈ T' a, termToken t' ⊤)) $$ [HT] [Hpost]
  · iintro %a Hfresh
    ihave %hfresh : ⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ $$ [HT Hfresh]
    · by_cases hc : ∀ t' ∈ T, ¬ (a : Term).Subterm t'
      · ipureintro; exact hc
      obtain ⟨t', ht', hsub⟩ : ∃ t' ∈ T, (a : Term).Subterm t' := by simpa using hc
      iexfalso
      icases Hfresh with ⟨H, -⟩
      iapply H
      iapply hsub.minted
      iapply HT $$ %t' %ht'
    imod termToken_alloc (T' a) iprop(minted (a : Term) -∗ False)
        iprop(minted (a : Term) ∗ □ (isPublic (a : Term) ↔ ▷ □ P a) ∗
          □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t)) CoPset.subseteq_top
      $$ Hctx [] [] [Hfresh] with ⟨⟨#Hm, #Hp, #He⟩, Htok⟩
    · iintro %t' %ht' Hcontra Hmt'
      iapply Hcontra
      ihave #HTa := HT' $$ %a
      icases bigSepFinset_mem ht' $$ HTa with ⟨-, H⟩
      iapply H $$ Hmt'
    · iintro %t' %ht' ⟨#Hm, -⟩
      ihave #HTa := HT' $$ %a
      icases bigSepFinset_mem ht' $$ HTa with ⟨H, -⟩
      iapply H $$ Hm
    · isplit
      · icases Hfresh with ⟨H, -⟩; iexact H
      · icases Hfresh with ⟨-, H⟩; imod H with H; imodintro; iexact H
    imodintro
    iframe Hm Hp He Htok
    ipureintro; exact hfresh
  · iintro %a #Hm #Hp #He #Hinv ⟨%hfresh, Htok⟩
    iapply Hpost $$ %a %hfresh Hm Hp He Hinv Htok

@[rocq_alias cryptis.wp_mk_nonce_freshN]
theorem wp_mkNonce_freshN (T : Finset Term) (P : Nonce → IProp GF) (Q : Term → IProp GF)
    (T' : Nonce → Finset Term) (Ψ : Val → IProp GF) :
    cryptisCtx -∗ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
    (∀ a : Nonce, [∗finset] t' ∈ T' a, □ (minted (a : Term) ↔ minted t')) -∗
    (∀ a : Nonce, ⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ -∗ minted (a : Term) -∗
      □ (isPublic (a : Term) ↔ ▷ □ P a) -∗ □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      ([∗finset] t' ∈ T' a, termToken t' ⊤) -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H1 H2 H3
  iapply twp.to_wp
  iapply twp_mkNonce_freshN T P Q T' Ψ $$ Hctx H1 H2 H3

@[rocq_alias cryptis.twp_mk_nonce_fresh]
theorem twp_mkNonce_fresh (T : Finset Term) (P : Nonce → IProp GF) (Q : Term → IProp GF)
    (Ψ : Val → IProp GF) :
    cryptisCtx -∗ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
    (∀ a : Nonce, ⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ -∗ minted (a : Term) -∗
      □ (isPublic (a : Term) ↔ ▷ □ P a) -∗ □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗ termToken (a : Term) ⊤ -∗
      Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ [{ Ψ }] := by
  iintro #Hctx HT Hpost
  iapply twp_mkNonce_freshN T P Q (fun a => {(a : Term)}) Ψ $$ Hctx HT [] [Hpost]
  · iintro %a
    iapply (bigSepFinset_singleton _).mpr
    iintro !>
    isplit <;> iintro #H <;> iexact H
  · iintro %a %hfresh #Hm #Hp #He #Hinv Htok
    rw [(bigSepFinset_singleton _).to_eq]
    iapply Hpost $$ %a %hfresh Hm Hp He Hinv Htok

@[rocq_alias cryptis.wp_mk_nonce_fresh]
theorem wp_mkNonce_fresh (T : Finset Term) (P : Nonce → IProp GF) (Q : Term → IProp GF)
    (Ψ : Val → IProp GF) :
    cryptisCtx -∗ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
    (∀ a : Nonce, ⌜∀ t' ∈ T, ¬ (a : Term).Subterm t'⌝ -∗ minted (a : Term) -∗
      □ (isPublic (a : Term) ↔ ▷ □ P a) -∗ □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗ termToken (a : Term) ⊤ -∗
      Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H1 H2
  iapply twp.to_wp
  iapply twp_mkNonce_fresh T P Q Ψ $$ Hctx H1 H2

@[rocq_alias cryptis.twp_mk_nonce]
theorem twp_mkNonce (P : Nonce → IProp GF) (Q : Term → IProp GF) (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ a : Nonce, minted (a : Term) -∗ □ (isPublic (a : Term) ↔ ▷ □ P a) -∗
      □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      termToken (a : Term) ⊤ -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ [{ Ψ }] := by
  iintro #Hctx Hpost
  iapply twp_mkNonce_fresh ∅ P Q Ψ $$ Hctx []
  · iintro %t %ht
    simp at ht
  · iintro %a - Hm Hp He Hinv Htok
    iapply Hpost $$ Hm Hp He Hinv Htok

@[rocq_alias cryptis.wp_mk_nonce]
theorem wp_mkNonce (P : Nonce → IProp GF) (Q : Term → IProp GF) (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ a : Nonce, minted (a : Term) -∗ □ (isPublic (a : Term) ↔ ▷ □ P a) -∗
      □ (∀ t, expPred (a : Term) t ↔ ▷ □ Q t) -∗
      □ (∀ t, expPred ↑(Term.E.ofTerm a)⁻¹ t ↔ ▷ False) -∗
      termToken (a : Term) ⊤ -∗ Ψ (encode (a : Term))) -∗
    WP hl(&mkNonce #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H
  iapply twp.to_wp
  iapply twp_mkNonce P Q Ψ $$ Hctx H

end HL

/-! ### Keys -/

/-- A term that is public exactly when the nonce `a` is, which is public once `γ` is shot, is a
secret. -/
theorem secret_of_isPublic_seed {k : Term} {a : Nonce} (γ : GName)
    (hk : isPublic (GF := GF) k ⊣⊢ isPublic (a : Term)) :
    □ (isPublic (a : Term) ↔ ▷ □ shot (GF := GF) γ 1) -∗ pending γ -∗ secret k := by
  iintro #Hp Hpend
  iapply secret_alloc k γ $$ [] Hpend
  iintro !>
  isplit
  · iintro #H
    icases Hp with ⟨Hl, -⟩
    ihave #H' := Hl $$ [H]
    · iapply hk.mp $$ H
    inext
    icases H' with #H'
    iexact H'
  · iintro #H
    iapply hk.mpr
    icases Hp with ⟨-, Hr⟩
    iapply Hr
    inext
    iintro !>
    iexact H

namespace HL

/-- The specs of `mkAEncKey`, `mkSignKey` and `mkSEncKey`, for the keys of `F`. -/
private theorem twp_mkKey (F : Functionality) (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ sk : Key F, minted sk -∗ secret sk -∗ termToken sk ⊤ -∗ Ψ (encode sk)) -∗
    WP hl(&(hl_val% λ _, let n := &mkNonce #(); &(hl_val% λ seed, &(key F.keyType) seed) n)
      #()) @ s; ⊤ [{ Ψ }] := by
  iintro #Hctx Hpost
  imod pending_alloc with ⟨%γ, Hpend⟩
  twp_rec
  twp_apply twp_mkNonce_freshN ∅ (fun _ => shot γ 1) (fun _ => iprop(False))
      (fun a => {((⟨a⟩ : Key F) : Term)}) $$ Hctx [] [] [Hpost Hpend]
  · iintro %t %ht
    simp at ht
  · iintro %a
    iapply (bigSepFinset_singleton _).mpr
    iintro !>
    rw [Key.toTerm, (minted_key _ _).to_eq]
    isplit <;> iintro #H <;> iexact H
  iintro %a - #Hm #Hp - - Htok
  rw [(bigSepFinset_singleton _).to_eq]
  twp_pures
  twp_rec
  twp_pures
  rw [← Term.encode_key, ← Key.toTerm_mk]
  iapply Hpost $$ [] [Hpend] Htok
  · iapply (minted_coe_key ⟨a⟩).mpr $$ Hm
  · iapply secret_of_isPublic_seed γ (isPublic_coe_key ⟨a⟩) $$ Hp Hpend

@[rocq_alias cryptis.twp_mk_aenc_key]
theorem twp_mkAEncKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ sk : Key .aenc, minted sk -∗ secret sk -∗ termToken sk ⊤ -∗ Ψ (encode sk)) -∗
    WP hl(&mkAEncKey #()) @ s; ⊤ [{ Ψ }] :=
  twp_mkKey .aenc Ψ

@[rocq_alias cryptis.wp_mk_aenc_key]
theorem wp_mkAEncKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ sk : Key .aenc, minted sk -∗ secret sk -∗ termToken sk ⊤ -∗ Ψ (encode sk)) -∗
    WP hl(&mkAEncKey #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H
  iapply twp.to_wp
  iapply twp_mkAEncKey Ψ $$ Hctx H

@[rocq_alias cryptis.twp_mk_sign_key]
theorem twp_mkSignKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ sk : Key .sign, minted sk -∗ secret sk -∗ termToken sk ⊤ -∗ Ψ (encode sk)) -∗
    WP hl(&mkSignKey #()) @ s; ⊤ [{ Ψ }] :=
  twp_mkKey .sign Ψ

@[rocq_alias cryptis.wp_mk_sign_key]
theorem wp_mkSignKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ sk : Key .sign, minted sk -∗ secret sk -∗ termToken sk ⊤ -∗ Ψ (encode sk)) -∗
    WP hl(&mkSignKey #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H
  iapply twp.to_wp
  iapply twp_mkSignKey Ψ $$ Hctx H

@[rocq_alias cryptis.twp_mk_senc_key]
theorem twp_mkSEncKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ k : Key .senc, minted k -∗ secret k -∗ termToken k ⊤ -∗ Ψ (encode k)) -∗
    WP hl(&mkSEncKey #()) @ s; ⊤ [{ Ψ }] :=
  twp_mkKey .senc Ψ

@[rocq_alias cryptis.wp_mk_senc_key]
theorem wp_mkSEncKey (Ψ : Val → IProp GF) :
    cryptisCtx -∗
    (∀ k : Key .senc, minted k -∗ secret k -∗ termToken k ⊤ -∗ Ψ (encode k)) -∗
    WP hl(&mkSEncKey #()) @ s; ⊤ {{ Ψ }} := by
  iintro #Hctx H
  iapply twp.to_wp
  iapply twp_mkSEncKey Ψ $$ Hctx H

/-! ### Encryption and signatures -/

@[rocq_alias cryptis.twp_aenc]
theorem twp_aenc (sk : Key .aenc) (N : Namespace) (t : Term) (φ : Key .aenc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .aenc N φ -∗ minted sk -∗ minted t -∗
    (isPublic t ∨ □ φ sk t ∧ □ (isPublic sk → isPublic t)) -∗
    (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&aenc &(encode (Spec.pkey sk)) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      [{ Ψ }] := by
  iintro #Hφ #Hmk #Hmt #Hinv HΨ
  twp_apply twp_aenc'
  iapply HΨ
  unfold Spec.enc
  icases Hinv with (#Hp | ⟨#H, #Ho⟩)
  · iapply isPublic_sealed_of_isPublic
    · iapply (isPublic_pkey_aenc sk).mpr $$ Hmk
    · iapply (isPublic_tag N t).mpr $$ Hp
  · iapply isPublic_aenc_intro sk N φ t $$ Hφ Hmk Hmt H Ho

@[rocq_alias cryptis.wp_aenc]
theorem wp_aenc (sk : Key .aenc) (N : Namespace) (t : Term) (φ : Key .aenc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .aenc N φ -∗ minted sk -∗ minted t -∗
    (isPublic t ∨ □ φ sk t ∧ □ (isPublic sk → isPublic t)) -∗
    (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&aenc &(encode (Spec.pkey sk)) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      {{ Ψ }} := by
  iintro #H1 #H2 #H3 #H4 H5
  iapply twp.to_wp
  iapply twp_aenc sk N t φ Ψ $$ H1 H2 H3 H4 H5

@[rocq_alias cryptis.wp_adec]
theorem wp_adec (sk : Key .aenc) (N : Namespace) (m : Term) (φ : Key .aenc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .aenc N φ -∗ isPublic m -∗
    ((∀ t, minted t -∗ (isPublic t ∨ □ φ sk t ∧ □ (isPublic sk → isPublic t)) -∗
        Ψ hl_val(some(&(encode t)))) ∧ Ψ hl_val(none())) -∗
    WP hl(&adec &(encode sk) &(encode (Term.ofNamespace N)) &(encode m)) @ s; E
      {{ Ψ }} := by
  iintro #Hφ #Hm Hpost
  iapply wp_adec'
  cases h : Spec.dec (sk : Term) (Term.ofNamespace N) m with
  | none =>
    inext
    isplit
    · iintro %t' - %h'
      simp [h] at h'
    · iintro -
      icases Hpost with ⟨-, H⟩
      iexact H
  | some t =>
    obtain ⟨kt, hkt, rfl⟩ := Spec.dec_eq_some_iff.mp h
    obtain rfl := Spec.eq_pkey_of_openKey_eq_aenc hkt
    unfold Spec.enc at h ⊢
    icases isPublic_aenc_elim sk N φ t $$ Hm Hφ with ⟨#Hmt, Hinv⟩
    inext
    isplit
    · iintro %t' - %h'
      obtain rfl : t = t' := Option.some_injective _ (h.symm.trans h')
      icases Hpost with ⟨H, -⟩
      iapply H $$ Hmt Hinv
    · iintro %h'
      simp [h] at h'

@[rocq_alias cryptis.twp_senc]
theorem twp_senc (k : Key .senc) (N : Namespace) (t : Term) (φ : Key .senc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .senc N φ -∗ minted k -∗ minted t -∗ (isPublic k ∨ □ φ k t) -∗
    □ (isPublic k → isPublic t) -∗ (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&senc &(encode k) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      [{ Ψ }] := by
  iintro #Hφ #Hmk #Hmt #Hinv #Ho HΨ
  twp_apply twp_senc'
  iapply HΨ
  unfold Spec.enc
  icases Hinv with (#Hp | #H)
  · iapply isPublic_sealed_of_isPublic $$ Hp
    iapply (isPublic_tag N t).mpr
    iapply Ho $$ Hp
  · iapply isPublic_senc_intro k N φ t $$ Hφ Hmk Hmt H Ho

@[rocq_alias cryptis.wp_senc]
theorem wp_senc (k : Key .senc) (N : Namespace) (t : Term) (φ : Key .senc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .senc N φ -∗ minted k -∗ minted t -∗ (isPublic k ∨ □ φ k t) -∗
    □ (isPublic k → isPublic t) -∗ (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&senc &(encode k) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      {{ Ψ }} := by
  iintro #H1 #H2 #H3 #H4 #H5 H6
  iapply twp.to_wp
  iapply twp_senc k N t φ Ψ $$ H1 H2 H3 H4 H5 H6

@[rocq_alias cryptis.wp_sdec]
theorem wp_sdec (k : Key .senc) (N : Namespace) (m : Term) (φ : Key .senc → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .senc N φ -∗ isPublic m -∗
    ((∀ t, minted t -∗ (isPublic k ∨ □ φ k t) -∗ □ (isPublic k → isPublic t) -∗
        Ψ hl_val(some(&(encode t)))) ∧ Ψ hl_val(none())) -∗
    WP hl(&sdec &(encode k) &(encode (Term.ofNamespace N)) &(encode m)) @ s; E
      {{ Ψ }} := by
  iintro #Hφ #Hm Hpost
  iapply wp_sdec'
  cases h : Spec.dec (k : Term) (Term.ofNamespace N) m with
  | none =>
    inext
    isplit
    · iintro %t' - %h'
      simp [h] at h'
    · iintro -
      icases Hpost with ⟨-, H⟩
      iexact H
  | some t =>
    obtain ⟨kt, hkt, rfl⟩ := Spec.dec_eq_some_iff.mp h
    obtain rfl := Spec.eq_of_openKey_eq_senc hkt
    unfold Spec.enc at h ⊢
    icases isPublic_senc_elim k N φ t $$ Hm Hφ with ⟨#Hmt, Hinv, #Ho⟩
    inext
    isplit
    · iintro %t' - %h'
      obtain rfl : t = t' := Option.some_injective _ (h.symm.trans h')
      icases Hpost with ⟨H, -⟩
      iapply H $$ Hmt Hinv Ho
    · iintro %h'
      simp [h] at h'

@[rocq_alias cryptis.twp_sign]
theorem twp_sign (sk : Key .sign) (N : Namespace) (t : Term) (φ : Key .sign → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .sign N φ -∗ minted sk -∗ isPublic t -∗ (isPublic sk ∨ □ φ sk t) -∗
    (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&sign &(encode sk) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      [{ Ψ }] := by
  iintro #Hφ #Hmk #Ht #Hinv HΨ
  twp_apply twp_sign'
  iapply HΨ
  unfold Spec.enc
  icases Hinv with (#Hp | #H)
  · iapply isPublic_sealed_of_isPublic $$ Hp
    iapply (isPublic_tag N t).mpr $$ Ht
  · iapply isPublic_sign_intro sk N φ t $$ Hφ Hmk Ht H

@[rocq_alias cryptis.wp_sign]
theorem wp_sign (sk : Key .sign) (N : Namespace) (t : Term) (φ : Key .sign → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .sign N φ -∗ minted sk -∗ isPublic t -∗ (isPublic sk ∨ □ φ sk t) -∗
    (∀ m, isPublic m → Ψ (encode m)) -∗
    WP hl(&sign &(encode sk) &(encode (Term.ofNamespace N)) &(encode t)) @ s; E
      {{ Ψ }} := by
  iintro #H1 #H2 #H3 #H4 H5
  iapply twp.to_wp
  iapply twp_sign sk N t φ Ψ $$ H1 H2 H3 H4 H5

@[rocq_alias cryptis.wp_verify]
theorem wp_verify (sk : Key .sign) (N : Namespace) (m : Term) (φ : Key .sign → Term → IProp GF)
    (Ψ : Val → IProp GF) :
    keyPred .sign N φ -∗ isPublic m -∗
    ((∀ t, isPublic t -∗ (isPublic sk ∨ □ φ sk t) -∗ Ψ hl_val(some(&(encode t)))) ∧
      Ψ hl_val(none())) -∗
    WP hl(&verify &(encode (Spec.pkey sk)) &(encode (Term.ofNamespace N)) &(encode m)) @ s; E
      {{ Ψ }} := by
  iintro #Hφ #Hm Hpost
  iapply wp_verify'
  cases h : Spec.dec (Spec.pkey sk) (Term.ofNamespace N) m with
  | none =>
    inext
    isplit
    · iintro %t' - %h'
      simp [h] at h'
    · iintro -
      icases Hpost with ⟨-, H⟩
      iexact H
  | some t =>
    obtain ⟨kt, hkt, rfl⟩ := Spec.dec_eq_some_iff.mp h
    obtain rfl := Spec.eq_of_openKey_eq_sign hkt
    unfold Spec.enc at h ⊢
    icases isPublic_sign_elim sk N φ t $$ Hm Hφ with ⟨#Ht, Hinv⟩
    inext
    isplit
    · iintro %t' - %h'
      obtain rfl : t = t' := Option.some_injective _ (h.symm.trans h')
      icases Hpost with ⟨H, -⟩
      iapply H $$ Ht Hinv
    · iintro %h'
      simp [h] at h'

end HL

end Cryptis
