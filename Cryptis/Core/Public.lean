module

public import Cryptis.Core.TermMeta

/-! Public terms.

A term is public when the attacker may know it. `isPublic t` holds when `t` is minted and either
the attacker can build `t` from public parts, or an honest party published it under conditions
that the protocol proof chose and recorded as ghost state:

- a nonce is public when the predicate registered at its creation holds;
- a key is public when it is the public half of a key pair: an encryption or verification key;
- a sealed message is public when its payload satisfies the predicate registered for its tag and
  its kind of key, and whoever can open it already knows the payload;
- a hash is public when its payload satisfies the hash predicate registered for its tag.

Exponentials follow Diffie–Hellman reasoning. The attacker can raise a public term to a public
exponent, and strip a public exponent from a public term. An exponential is also public when the
owner of one of its exponents agrees to publish it and the exponential without that exponent is
public, or when the owners of all its exponents agree (`expPred`). A negative exponent has no
owner.

- Nonces, sealed messages and hashes: the ghost state behind these conditions, and the tokens
  that register them.
- The definition, and what it says about each kind of term, exponentials and products included.
- Further rules: a minted term is public under `▷ False`, a negative exponent of a public
  exponential is public, and an owner may consent to raising public terms to its exponent.
- Lists, tags, sealed messages, nonces, keys and secrets: the rules that protocol proofs use. A
  secret is a term that is not public yet, and can later be made public or kept secret forever.
- Sealing with key records: encryption and signatures with a registered predicate. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.Std Iris.HeapLang Iris.ProofMode COFE Term Term.ProdGroup BigSepMultiset

/-- The ghost state of public terms, without its ghost names. -/
@[rocq_alias cryptis.publicGpreS]
class PublicGpreS (GF : BundledGFunctors) where
  savedPredNonce : SavedPredG GF Nonce
  savedPredTerm : SavedPredG GF Term
  savedPredSeal : SavedPredG GF (Term × Term)
  metaGS : MetaGS GF

/-- The ghost state of public terms. -/
@[rocq_alias cryptis.publicGS]
class PublicGS (GF : BundledGFunctors) extends PublicGpreS GF where
  hashName : GName
  aencName : GName
  signName : GName
  sencName : GName

attribute [rocq_alias cryptis.PublicGPreS] PublicGpreS.mk
attribute [rocq_alias cryptis.publicGpreS_nonce] PublicGpreS.savedPredNonce
attribute [rocq_alias cryptis.publicGpreS_term] PublicGpreS.savedPredTerm
attribute [rocq_alias cryptis.publicGpreS_seal] PublicGpreS.savedPredSeal
attribute [rocq_alias cryptis.publicGpreS_meta] PublicGpreS.metaGS
attribute [rocq_alias cryptis.PublicGS] PublicGS.mk
attribute [rocq_alias cryptis.public_inG] PublicGS.toPublicGpreS
attribute [rocq_alias cryptis.public_hash_name] PublicGS.hashName
attribute [rocq_alias cryptis.public_aenc_name] PublicGS.aencName
attribute [rocq_alias cryptis.public_sign_name] PublicGS.signName
attribute [rocq_alias cryptis.public_senc_name] PublicGS.sencName

#rocq_ignore cryptis.«publicΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.subG_publicGpreS "Subsumed by BundledGFunctors typeclass synthesis"

attribute [local instance_reducible, local instance] PublicGpreS.savedPredNonce
  PublicGpreS.savedPredTerm PublicGpreS.savedPredSeal PublicGpreS.metaGS

section Factors

variable {PROP : Type _} [BI PROP] [BIAffine PROP]
local bi PROP

@[rocq_alias cryptis.big_sepL_factors_TMul2, rocq_alias cryptis.big_sepL_gfactors_TGMul2]
theorem bigSepMultiset_factors_coe_mul {o : TermOpN} (Φ : Term → PROP) [∀ t, Persistent (Φ t)]
    (a b : ProdGroup o) :
    ([∗multiset] u ∈ ((a : Term).factors o).elements, Φ u) -∗
    ([∗multiset] u ∈ ((b : Term).factors o).elements, Φ u) -∗
      [∗multiset] u ∈ ((↑(a * b) : Term).factors o).elements, Φ u := by
  simp only [bigSepMultiset_forall.to_eq]
  iintro H1 H2 %u %hu
  rcases ProdGroup.mem_factors_coe_mul hu with h | h
  · iapply H1 $$ %u %h
  · iapply H2 $$ %u %h

end Factors

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [PublicGS GF]
local bi (IProp GF)

/-! ### Nonces -/

/-- The predicate registered for the nonce `a` when it was created holds of `a`. -/
@[rocq_alias cryptis.pnonce]
def pnonce (a : Nonce) : IProp GF :=
  iprop(∃ γ, ∃ P : Nonce → IProp GF,
    metaInfo a.loc (nroot.@"nonce") γ ∧ iOwn γ (savedPred .discard P) ∧ ▷ □ P a)

@[rocq_alias cryptis.Persistent_pnonce]
instance pnonce_persistent (a : Nonce) : Persistent (pnonce (GF := GF) a) := by
  unfold pnonce; infer_instance

/-- `t'` may be published as an exponential of `t`, according to the owner of the nonce `t`. -/
@[rocq_alias cryptis.exp_pred]
def expPred : Term → Term → IProp GF
  | nonce a, t' => iprop(∃ γ, ∃ φ : Term → IProp GF,
      metaInfo a.loc (nroot.@"dh") γ ∧ iOwn γ (savedPred .discard φ) ∧ ▷ □ φ t')
  | _, _ => iprop(▷ False)

@[rocq_alias cryptis.exp_pred_persistent]
instance expPred_persistent (t t' : Term) : Persistent (expPred (GF := GF) t t') := by
  cases t <;> (unfold expPred; infer_instance)

@[rocq_alias cryptis.exp_pred_TInv]
theorem expPred_inv {f : Term.E} (h : (f : Term).isProd .mul = false) (t' : Term) :
    expPred (GF := GF) ↑f⁻¹ t' ⊣⊢ ▷ False := by
  have := ProdGroup.isProd_coe_inv h
  cases ht : (↑f⁻¹ : Term) <;> simp_all [expPred, isProd, PreTerm.isProd]

/-! ### Predicates of sealed messages -/

/-- The ghost name of the predicates of a key functionality. -/
@[rocq_alias cryptis.name_of_functionality]
def Functionality.name : Functionality → GName
  | .aenc => PublicGS.aencName GF
  | .sign => PublicGS.signName GF
  | .senc => PublicGS.sencName GF

/-- `Φ k t` must hold of the messages `t` tagged with `N` and sealed with `k` and the
functionality `F`. -/
@[rocq_alias cryptis.seal_pred]
def sealPred (F : Functionality) (N : Namespace) (Φ : Term → Term → IProp GF) : IProp GF :=
  nown (F.name (GF := GF)) N (savedPred .discard fun p : Term × Term => Φ p.1 p.2)

/-- `sealPred` for the keys of `F`: `Φ k t` must hold of the messages `t` tagged with `N` and
sealed with the key `k`. -/
@[rocq_alias cryptis.aenc_pred, rocq_alias cryptis.sign_pred, rocq_alias cryptis.senc_pred]
def keyPred (F : Functionality) (N : Namespace) (Φ : Key F → Term → IProp GF) : IProp GF :=
  sealPred F N fun k t => iprop(∃ k' : Key F, ⌜k = k'⌝ ∗ Φ k' t)

/-- The right to register the predicates of the namespaces in `E` for the functionality `F`. -/
@[rocq_alias cryptis.seal_pred_token]
def sealPredToken (F : Functionality) (E : CoPset) : IProp GF := gmetaToken (F.name (GF := GF)) E

variable {F : Functionality} {N : Namespace} {E E1 E2 : CoPset}

@[rocq_alias cryptis.seal_pred_token_difference]
theorem sealPredToken_difference (h : E1 ⊆ E2) :
    sealPredToken F E2 ⊣⊢ sealPredToken F E1 ∗ sealPredToken F (E2 \ E1) :=
  gmetaToken_difference h

@[rocq_alias cryptis.seal_pred_token_drop]
theorem sealPredToken_drop (h : E1 ⊆ E2) : sealPredToken F E2 -∗ sealPredToken F E1 :=
  gmetaToken_drop h

@[rocq_alias cryptis.seal_pred_persistent]
instance sealPred_persistent (F : Functionality) (N : Namespace) (Φ : Term → Term → IProp GF) :
    Persistent (sealPred F N Φ) := by
  unfold sealPred; infer_instance

@[rocq_alias cryptis.seal_pred_agree]
theorem sealPred_agree (k t : Term) {Φ1 Φ2 : Term → Term → IProp GF} :
    sealPred F N Φ1 -∗ sealPred F N Φ2 -∗ ▷ (Φ1 k t ≡ Φ2 k t) := by
  unfold sealPred
  iintro #H1 #H2
  ihave #Hv := nown_valid_2 $$ H1 H2
  icases savedPred_op_validI.mp $$ Hv with ⟨-, #Heq⟩
  iapply Heq $$ %(k, t)

@[rocq_alias cryptis.seal_pred_set]
theorem sealPred_set (F : Functionality) (N : Namespace) (Φ : Term → Term → IProp GF)
    (h : ↑N ⊆ E) : sealPredToken F E ==∗ sealPred F N Φ ∗ sealPredToken F (E \ ↑N) :=
  nown_alloc _ h (savedPred_valid.mpr DFrac.valid_discard)

instance keyPred_persistent (F : Functionality) (N : Namespace) (Φ : Key F → Term → IProp GF) :
    Persistent (keyPred F N Φ) := by
  unfold keyPred; infer_instance

@[rocq_alias cryptis.aenc_pred_set, rocq_alias cryptis.sign_pred_set,
  rocq_alias cryptis.senc_pred_set]
theorem keyPred_set (F : Functionality) (N : Namespace) (Φ : Key F → Term → IProp GF)
    (h : ↑N ⊆ E) : sealPredToken F E ==∗ keyPred F N Φ ∗ sealPredToken F (E \ ↑N) :=
  sealPred_set _ _ _ h

/-- `t` is tagged with a namespace whose predicate for `F` holds of `k` and the payload. -/
@[rocq_alias cryptis.wf_seal]
def wfSeal (F : Functionality) (k t : Term) : IProp GF :=
  iprop(∃ N t', ∃ Φ : Term → Term → IProp GF,
    ⌜t = Spec.tag (ofNamespace N) t'⌝ ∧ sealPred F N Φ ∧ □ ▷ Φ k t')

@[rocq_alias cryptis.wf_seal_persistent]
instance wfSeal_persistent (F : Functionality) (k t : Term) :
    Persistent (wfSeal (GF := GF) F k t) := by
  unfold wfSeal; infer_instance

@[rocq_alias cryptis.wf_seal_elim]
theorem wfSeal_elim {k t : Term} {Φ : Term → Term → IProp GF} :
    wfSeal F k (Spec.tag (ofNamespace N) t) -∗ sealPred F N Φ -∗ □ ▷ Φ k t := by
  unfold wfSeal
  iintro ⟨%N', %t', %Φ', %ht, #HΦ', #H⟩ #HΦ
  obtain ⟨rfl, rfl⟩ := by simpa using ht
  ihave #Heq := sealPred_agree k t $$ HΦ HΦ'
  iintro !>
  inext
  irewrite [Heq]
  · exact OFE.id_ne
  iexact H

/-! ### Predicates of hashes -/

/-- `P t` must hold of the messages `t` tagged with `N` and hashed. -/
@[rocq_alias cryptis.hash_pred]
def hashPred (N : Namespace) (P : Term → IProp GF) : IProp GF :=
  nown (PublicGS.hashName GF) N (savedPred .discard P)

/-- The right to register the hash predicates of the namespaces in `E`. -/
@[rocq_alias cryptis.hash_pred_token]
def hashPredToken (E : CoPset) : IProp GF := gmetaToken (PublicGS.hashName GF) E

@[rocq_alias cryptis.hash_pred_token_difference]
theorem hashPredToken_difference (h : E1 ⊆ E2) :
    hashPredToken E2 ⊣⊢ hashPredToken E1 ∗ hashPredToken (E2 \ E1) :=
  gmetaToken_difference h

@[rocq_alias cryptis.hash_pred_token_drop]
theorem hashPredToken_drop (h : E1 ⊆ E2) : hashPredToken E2 -∗ hashPredToken E1 :=
  gmetaToken_drop h

@[rocq_alias cryptis.hash_pred_persistent]
instance hashPred_persistent (N : Namespace) (P : Term → IProp GF) :
    Persistent (hashPred N P) := by
  unfold hashPred; infer_instance

@[rocq_alias cryptis.hash_pred_agree]
theorem hashPred_agree (t : Term) {P1 P2 : Term → IProp GF} :
    hashPred N P1 -∗ hashPred N P2 -∗ ▷ (P1 t ≡ P2 t) := by
  unfold hashPred
  iintro #H1 #H2
  ihave #Hv := nown_valid_2 $$ H1 H2
  icases savedPred_op_validI.mp $$ Hv with ⟨-, #Heq⟩
  iapply Heq $$ %t

@[rocq_alias cryptis.hash_pred_set]
theorem hashPred_set (N : Namespace) (P : Term → IProp GF) (h : ↑N ⊆ E) :
    hashPredToken E ==∗ hashPred N P ∗ hashPredToken (E \ ↑N) :=
  nown_alloc _ h (savedPred_valid.mpr DFrac.valid_discard)

/-- `t` is tagged with a namespace whose hash predicate holds of the payload. -/
@[rocq_alias cryptis.wf_hash]
def wfHash (t : Term) : IProp GF :=
  iprop(∃ N t', ∃ P : Term → IProp GF,
    ⌜t = Spec.tag (ofNamespace N) t'⌝ ∧ hashPred N P ∧ □ ▷ P t')

@[rocq_alias cryptis.wf_hash_persistent]
instance wfHash_persistent (t : Term) : Persistent (wfHash (GF := GF) t) := by
  unfold wfHash; infer_instance

@[rocq_alias cryptis.wf_hash_elim]
theorem wfHash_elim {t : Term} {P : Term → IProp GF} :
    wfHash (Spec.tag (ofNamespace N) t) -∗ hashPred N P -∗ □ ▷ P t := by
  unfold wfHash
  iintro ⟨%N', %t', %P', %ht, #HP', #H⟩ #HP
  obtain ⟨rfl, rfl⟩ := by simpa using ht
  ihave #Heq := hashPred_agree t $$ HP HP'
  iintro !>
  inext
  irewrite [Heq]
  · exact OFE.id_ne
  iexact H

/-! ### The definition of public terms -/

/-- The attacker can build `t` from the terms `ts` with a free constructor. -/
@[rocq_alias cryptis.decompose]
inductive Decompose : List Term → Term → Prop
  | int (n : Int) : Decompose [] (.int n)
  | pair (t₁ t₂ : Term) : Decompose [t₁, t₂] (.pair t₁ t₂)
  | key (kt : KeyType) (t : Term) : Decompose [t] (.key kt t)
  | sealed (k t : Term) : Decompose [k, t] (.sealed k t)
  | hash (t : Term) : Decompose [t] (.hash t)

attribute [rocq_alias cryptis.DInt] Decompose.int
attribute [rocq_alias cryptis.DPair] Decompose.pair
attribute [rocq_alias cryptis.DKey] Decompose.key
attribute [rocq_alias cryptis.DSeal] Decompose.sealed
attribute [rocq_alias cryptis.DHash] Decompose.hash

namespace Decompose

variable {ts : List Term} {t : Term}

@[rocq_alias cryptis.decompose_tsize]
theorem tsize_lt (h : Decompose ts t) {t' : Term} (ht : t' ∈ ts) : t'.tsize < t.tsize := by
  cases h <;> simp at ht <;> rcases ht with rfl | rfl <;> simp <;> omega

@[rocq_alias cryptis.decompose_Nmul, rocq_alias cryptis.decompose_Ngmul]
theorem isProd_eq_false (h : Decompose ts t) (o : TermOpN) : t.isProd o = false := by
  cases h <;> cases o <;> rfl

@[rocq_alias cryptis.decompose_Nexp]
theorem isExp_eq_false (h : Decompose ts t) : t.isExp = false := by cases h <;> rfl

end Decompose

/-- If `k` seals, `P` of the key that opens it implies `P t`. -/
def openCond (P : Term → IProp GF) (k t : Term) : IProp GF :=
  match Spec.openKey k with
  | some k' => iprop(□ (P k' → P t))
  | none => iprop(True)

/-- The condition under which an honest party publishes `sealed k t`: the key seals, the message
satisfies the predicate of its tag, and opening it reveals `t` only to those who know `t`. -/
def sealCond (P : Term → IProp GF) (k t : Term) : IProp GF :=
  match k.functionality with
  | some F => iprop(⌜Spec.isSealKey k⌝ ∧ wfSeal F (Spec.skey k) t ∧ openCond P k t)
  | none => iprop(True)

instance openCond_persistent (P : Term → IProp GF) (k t : Term) :
    Persistent (openCond P k t) := by
  unfold openCond; split <;> infer_instance

instance sealCond_persistent (P : Term → IProp GF) (k t : Term) :
    Persistent (sealCond P k t) := by
  unfold sealCond; split <;> infer_instance

/-- The ways an honest party makes an atom public. -/
def publicAtom (P : Term → IProp GF) : Term → IProp GF
  | .nonce a => iprop(◇ pnonce a)
  | .key kt _ => iprop(⌜Spec.publicKeyType kt⌝)
  | .hash t => wfHash t
  | .sealed k t => sealCond P k t
  | _ => iprop(False)

instance publicAtom_persistent (P : Term → IProp GF) (t : Term) :
    Persistent (publicAtom P t) := by
  cases t <;> (unfold publicAtom; infer_instance)

/-- The attacker may know `t`. The recursion is on the size of `t`, over attached lists and
multisets whose elements carry the proofs that they are smaller; `isPublic_eq` states the
definition without them. -/
@[rocq_alias cryptis.public, rocq_alias cryptis.public_def]
def isPublic (t : Term) : IProp GF :=
  iprop(minted t ∧
    ((∃ ts, ∃ _ : Decompose ts t, [∗list] u ∈ ts.attach, isPublic u.1) ∨
     (∃ o, ∃ _ : t.isProd o, [∗multiset] u ∈ (t.factors o).elements.attach, isPublic u.1) ∨
     (⌜t.isExp⌝ ∧
       ([∗multiset] f ∈ (satoms t.exps).attach, □ (isPublic ↑f.1 → isPublic (t.exp ↑f.1⁻¹))) ∧
       ((∃ f, ∃ _ : f ∈ satoms t.exps, (isPublic ↑f ∨ expPred ↑f t) ∧
          isPublic (t.exp ↑f⁻¹)) ∨
        [∗multiset] f ∈ satoms t.exps, expPred ↑f t)) ∨
     match t with
     | .nonce a => iprop(◇ pnonce a)
     | .key kt _ => iprop(⌜Spec.publicKeyType kt⌝)
     | .hash t => wfHash t
     | .sealed k m =>
       match k.functionality with
       | some F => iprop(⌜Spec.isSealKey k⌝ ∧ wfSeal F (Spec.skey k) m ∧
           match _ : Spec.openKey k with
           | some k' => iprop(□ (isPublic k' → isPublic m))
           | none => iprop(True))
       | none => iprop(True)
     | _ => iprop(False)))
termination_by t.tsize
decreasing_by
  all_goals first
    | exact Decompose.tsize_lt ‹_› u.2
    | exact tsize_lt_of_mem_factors ‹_› (SMS.mem_elements.mp u.2)
    | exact (tsize_lt_of_mem_satoms f.2).1
    | exact (tsize_lt_of_mem_satoms f.2).2
    | exact (tsize_lt_of_mem_satoms ‹_›).1
    | exact (tsize_lt_of_mem_satoms ‹_›).2
    | (simp [Spec.tsize_eq_of_openKey_eq_some ‹_›]; omega)

#rocq_ignore cryptis.public_aux "Lean definitions are not unfolded unless asked"
#rocq_ignore cryptis.public_unseal "Lean definitions are not unfolded unless asked"
#rocq_ignore cryptis.public_pre_aux "The body of `isPublic`, stated by `isPublic_eq`"
#rocq_ignore cryptis.public_pre_aux_wf
  "Lean's well-founded recursion defines `isPublic` directly"
#rocq_ignore cryptis.size_rec_pred_aux
  "Lean's well-founded recursion defines `isPublic` directly"
#rocq_ignore cryptis.size_rec_pred "Lean's well-founded recursion defines `isPublic` directly"
#rocq_ignore cryptis.size_rec_pred_unfold
  "Lean's well-founded recursion defines `isPublic` directly"
#rocq_ignore cryptis.size_rec_pred_persistent
  "Lean's well-founded recursion defines `isPublic` directly"
#rocq_ignore cryptis.size_rec_pred_ne
  "Lean's well-founded recursion defines `isPublic` directly"

@[rocq_alias cryptis.public_eq]
theorem isPublic_eq (t : Term) :
    isPublic (GF := GF) t =
      iprop(minted t ∧
        ((∃ ts, ⌜Decompose ts t⌝ ∧ [∗list] u ∈ ts, isPublic u) ∨
         (∃ o, ⌜t.isProd o⌝ ∧ [∗multiset] u ∈ (t.factors o).elements, isPublic u) ∨
         (⌜t.isExp⌝ ∧
           ([∗multiset] f ∈ satoms t.exps, □ (isPublic ↑f → isPublic (t.exp ↑f⁻¹))) ∧
           ((∃ f, ⌜f ∈ satoms t.exps⌝ ∧ (isPublic ↑f ∨ expPred ↑f t) ∧
              isPublic (t.exp ↑f⁻¹)) ∨
            [∗multiset] f ∈ satoms t.exps, expPred ↑f t)) ∨
         publicAtom isPublic t)) := by
  rw [isPublic.eq_def]
  simp only [BigSepL.bigSepL_attach, (bigSepMultiset_attach _).to_eq, exists_prop.to_eq,
    (bigSepMultiset_attach (Φ := fun f : E =>
      iprop(□ (isPublic (GF := GF) ↑f → isPublic (t.exp ↑f⁻¹)))) _).to_eq]
  congr 4
  rcases t with _ | _ | _ | _ | ⟨k, m⟩ | _ | _ <;> try rfl
  simp only [publicAtom, sealCond, openCond]
  split <;> try rfl
  split <;> simp only [*]

#rocq_ignore cryptis.public_pre_aux_persistent "`isPublic_persistent`, by induction on the size"

@[rocq_alias cryptis.Persistent_public]
instance isPublic_persistent (t : Term) : Persistent (isPublic (GF := GF) t) where
  persistent := by
    induction t using tsizeRec with | h t ih
    rw [isPublic_eq]
    iintro ⟨#Hm, H⟩
    icases H with (⟨%ts, %hd, H⟩ | ⟨%o, %hm, H⟩ | ⟨%hx, #Hs, H⟩ | #H)
    · ihave #H : [∗list] u ∈ ts, <pers> isPublic u $$ [H]
      · iapply BigSepL.bigSepL_impl $$ H
        iintro !> %k %u %hu Hu
        iapply ih u (hd.tsize_lt (List.mem_of_getElem? hu)) $$ Hu
      imodintro
      isplit
      · iexact Hm
      ileft
      iexists ts
      isplit
      · ipureintro; exact hd
      iapply BigSepL.bigSepL_impl $$ H
      iintro !> %k %u - #Hu
      iexact Hu
    · ihave #H : [∗multiset] u ∈ (t.factors o).elements, <pers> isPublic u $$ [H]
      · iapply BigSepMS.bigSepMS_impl $$ H
        iintro !> %u %hu Hu
        iapply ih u (tsize_lt_of_mem_factors hm (SMS.mem_elements.mp
          (Multiset.mem_toIris.mp hu))) $$ Hu
      imodintro
      isplit
      · iexact Hm
      iright; ileft
      iexists o
      isplit
      · ipureintro; exact hm
      iapply BigSepMS.bigSepMS_impl $$ H
      iintro !> %u - #Hu
      iexact Hu
    · ihave #H : (∃ f, ⌜f ∈ satoms t.exps⌝ ∧ (<pers> isPublic ↑f ∨ expPred ↑f t) ∧
            <pers> isPublic (t.exp ↑f⁻¹)) ∨
          [∗multiset] f ∈ satoms t.exps, expPred ↑f t $$ [H]
      · icases H with (⟨%f, %hf, H⟩ | #H)
        · ileft
          iexists f
          isplit
          · ipureintro; exact hf
          isplit
          · icases H with ⟨(Hf | #Hf), -⟩
            · ileft; iapply ih _ (tsize_lt_of_mem_satoms hf).1 $$ Hf
            · iright; iexact Hf
          · icases H with ⟨-, Hp⟩
            iapply ih _ (tsize_lt_of_mem_satoms hf).2 $$ Hp
        · iright; iexact H
      imodintro
      isplit
      · iexact Hm
      iright; iright; ileft
      isplit
      · ipureintro; exact hx
      isplit
      · iexact Hs
      icases H with (⟨%f, %hf, #Hf, #Hp⟩ | #H)
      · ileft
        iexists f
        isplit
        · ipureintro; exact hf
        isplit
        · icases Hf with (#Hf | #Hf)
          · ileft; iexact Hf
          · iright; iexact Hf
        · iexact Hp
      · iright; iexact H
    · imodintro
      isplit
      · iexact Hm
      iright; iright; iright
      iexact H

variable {t t₁ t₂ k : Term} {s : SMS Term}

theorem publicAtom_eq_false {P : Term → IProp GF} (h : t.isProd .mul ∨ t.isProd .gmul ∨ t.isExp) :
    publicAtom P t = iprop(False) := by
  cases t <;> simp_all [isProd, isExp, publicAtom]

@[rocq_alias cryptis.public_minted]
theorem isPublic_minted (t : Term) : isPublic (GF := GF) t ⊢ minted t := by
  rw [isPublic_eq]
  exact and_elim_l

/-- A term that is not an exponential or a product is public when it can be built from public
terms or an honest party published it. -/
theorem isPublic_iff_of_free (hm : t.isProd .mul = false) (hg : t.isProd .gmul = false)
    (hx : t.isExp = false) :
    isPublic (GF := GF) t ⊣⊢
      minted t ∧ ((∃ ts, ⌜Decompose ts t⌝ ∧ [∗list] u ∈ ts, isPublic u) ∨
        publicAtom isPublic t) := by
  rw [isPublic_eq]
  constructor
  · iintro ⟨#Hm, (H | ⟨%o, %h, -⟩ | ⟨%h, -⟩ | H)⟩
    · isplit
      · iexact Hm
      · ileft; iexact H
    · cases o <;> simp_all
    · simp [hx] at h
    · isplit
      · iexact Hm
      · iright; iexact H
  · iintro ⟨#Hm, (H | H)⟩
    · isplit
      · iexact Hm
      · ileft; iexact H
    · isplit
      · iexact Hm
      · iright; iright; iright; iexact H

@[rocq_alias cryptis.public_TInt]
theorem isPublic_int (n : Int) : isPublic (GF := GF) (int n) ⊣⊢ True := by
  refine ⟨true_intro, ?_⟩
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq]
  iintro -
  isplit
  · iapply (minted_int n).mpr; itrivial
  · ileft
    iexists []
    isplit
    · ipureintro; exact .int n
    · iempintro

@[rocq_alias cryptis.public_TPair]
theorem isPublic_pair (t₁ t₂ : Term) :
    isPublic (GF := GF) (pair t₁ t₂) ⊣⊢ isPublic t₁ ∧ isPublic t₂ := by
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq]
  simp only [publicAtom]
  constructor
  · iintro ⟨-, (⟨%ts, %hd, H⟩ | %hf)⟩
    on_goal 2 => cases hf
    cases hd
    icases BigSepL.bigSepL_pair.mp $$ H with ⟨#H1, #H2⟩
    isplit <;> iassumption
  · iintro #H
    isplit
    · iapply (minted_pair t₁ t₂).mpr
      isplit
      · icases H with ⟨H, -⟩; iapply isPublic_minted $$ H
      · icases H with ⟨-, H⟩; iapply isPublic_minted $$ H
    · ileft
      iexists [t₁, t₂]
      isplit
      · ipureintro; exact .pair t₁ t₂
      · iapply BigSepL.bigSepL_pair.mpr
        icases H with ⟨H1, H2⟩
        isplitl [H1] <;> iassumption

@[rocq_alias cryptis.public_TNonce]
theorem isPublic_nonce (a : Nonce) :
    isPublic (GF := GF) (nonce a) ⊣⊢ ◇ pnonce a ∗ metaInfo a.loc (nroot.@"minted") () := by
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq, (minted_nonce a).to_eq]
  simp only [publicAtom]
  constructor
  · iintro ⟨#Hm, (⟨%ts, %hd, -⟩ | #H)⟩
    · cases hd
    · isplitl [] <;> iassumption
  · iintro ⟨#H, #Hm⟩
    isplit
    · iexact Hm
    · iright; iexact H

@[rocq_alias cryptis.public_mul_factors, rocq_alias cryptis.public_gmul_gfactors]
theorem isPublic_prod_factors {o : TermOpN} (h : t.isProd o) :
    isPublic (GF := GF) t ⊢ [∗multiset] u ∈ (t.factors o).elements, isPublic u := by
  rw [isPublic_eq]
  have hx := isExp_eq_false_of_isProd h
  rw [publicAtom_eq_false (by cases o <;> simp [h])]
  iintro ⟨-, (⟨%ts, %hd, -⟩ | ⟨%o', %h', H⟩ | ⟨%hx', -⟩ | %hf)⟩
  rotate_left 3
  · cases hf
  · simp [hd.isProd_eq_false] at h
  · obtain rfl : o' = o := by
      cases o <;> cases o' <;> first | rfl | simp [isProd_gmul_eq_false_of_isProd_mul, *] at *
    iexact H
  · simp [hx] at hx'

@[rocq_alias cryptis.public_factors, rocq_alias cryptis.public_gfactors]
theorem isPublic_factors (o : TermOpN) (t : Term) :
    isPublic (GF := GF) t ⊣⊢ minted t ∧ [∗multiset] u ∈ (t.factors o).elements, isPublic u := by
  cases hm : t.isProd o
  · rw [factors_eq_singleton hm, SMS.elements_singleton, (bigSepMultiset_singleton t).to_eq]
    exact ⟨and_intro (isPublic_minted t) .rfl, and_elim_r⟩
  · refine ⟨and_intro (isPublic_minted t) (isPublic_prod_factors hm), ?_⟩
    rw [isPublic_eq]
    iintro ⟨#Hm, H⟩
    isplit
    · iexact Hm
    · iright; ileft
      iexists o
      isplit
      · ipureintro; exact hm
      · iexact H

@[rocq_alias cryptis.public_TInv, rocq_alias cryptis.public_TGInv]
theorem isPublic_coe_inv {o : TermOpN} (a : ProdGroup o) :
    isPublic (GF := GF) ↑a⁻¹ ⊣⊢ isPublic ↑a := by
  rw [(isPublic_factors o ↑a⁻¹).to_eq, (isPublic_factors o ↑a).to_eq,
    (minted_coe_inv a).to_eq, ProdGroup.factors_coe_inv, SMS.elements_neg]
  exact .rfl

@[rocq_alias cryptis.public_TKey]
theorem isPublic_key (kt : KeyType) (t : Term) :
    isPublic (GF := GF) (key kt t) ⊣⊢ isPublic t ∨ minted t ∧ ⌜Spec.publicKeyType kt⌝ := by
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq, (minted_key kt t).to_eq]
  simp only [publicAtom]
  constructor
  · iintro ⟨#Hm, (⟨%ts, %hd, H⟩ | %H)⟩
    · cases hd
      ileft
      iapply BigSepL.bigSepL_singleton.mp $$ H
    · iright
      isplit
      · iexact Hm
      · ipureintro; exact H
  · iintro (#H | ⟨#Hm, %H⟩)
    · isplit
      · iapply isPublic_minted $$ H
      · ileft
        iexists [t]
        isplit
        · ipureintro; exact .key kt t
        · iapply BigSepL.bigSepL_singleton.mpr; iexact H
    · isplit
      · iexact Hm
      · iright; ipureintro; exact H

@[rocq_alias cryptis.public_TSeal]
theorem isPublic_sealed (k t : Term) :
    isPublic (GF := GF) (sealed k t) ⊣⊢
      isPublic k ∧ isPublic t ∨ minted (sealed k t) ∧ sealCond isPublic k t := by
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq]
  simp only [publicAtom]
  constructor
  · iintro ⟨#Hm, (⟨%ts, %hd, H⟩ | #H)⟩
    · cases hd
      ileft
      icases BigSepL.bigSepL_pair.mp $$ H with ⟨#H1, #H2⟩
      isplit <;> iassumption
    · iright
      isplit <;> iassumption
  · iintro (#H | ⟨#Hm, #H⟩)
    · isplit
      · iapply (minted_sealed k t).mpr
        isplit
        · icases H with ⟨H, -⟩; iapply isPublic_minted $$ H
        · icases H with ⟨-, H⟩; iapply isPublic_minted $$ H
      · ileft
        iexists [k, t]
        isplit
        · ipureintro; exact .sealed k t
        · iapply BigSepL.bigSepL_pair.mpr
          icases H with ⟨H1, H2⟩
          isplitl [H1] <;> iassumption
    · isplit
      · iexact Hm
      · iright; iexact H

@[rocq_alias cryptis.public_open]
theorem isPublic_opened {t' : Term} (h : Spec.opened k t = some t') :
    isPublic (GF := GF) k -∗ isPublic t -∗ isPublic t' := by
  obtain ⟨kt, hkt, rfl⟩ := Spec.opened_eq_some_iff.mp h
  iintro #Hk #Ht
  icases (isPublic_sealed kt t').mp $$ Ht with (⟨-, #H⟩ | ⟨-, #H⟩)
  · iexact H
  unfold sealCond
  split
  · icases H with ⟨-, -, #H⟩
    unfold openCond
    rw [hkt]
    iapply H $$ Hk
  · rename_i hF
    rcases kt with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [Spec.openKey, functionality]

@[rocq_alias cryptis.public_THash]
theorem isPublic_hash (t : Term) :
    isPublic (GF := GF) (hash t) ⊣⊢ isPublic t ∨ minted t ∧ wfHash t := by
  rw [(isPublic_iff_of_free rfl rfl rfl).to_eq, (minted_hash t).to_eq]
  simp only [publicAtom]
  constructor
  · iintro ⟨#Hm, (⟨%ts, %hd, H⟩ | #H)⟩
    · cases hd
      ileft
      iapply BigSepL.bigSepL_singleton.mp $$ H
    · iright
      isplit <;> iassumption
  · iintro (#H | ⟨#Hm, #H⟩)
    · isplit
      · iapply isPublic_minted $$ H
      · ileft
        iexists [t]
        isplit
        · ipureintro; exact .hash t
        · iapply BigSepL.bigSepL_singleton.mpr; iexact H
    · isplit
      · iexact Hm
      · iright; iexact H

@[rocq_alias cryptis.public_THashIS]
theorem isPublic_hash_intro {N : Namespace} {φ : Term → IProp GF} :
    hashPred N φ -∗ minted t -∗ ▷ □ φ t -∗ isPublic (hash (Spec.tag (ofNamespace N) t)) := by
  iintro #Hφ #Hm #H
  iapply (isPublic_hash _).mpr
  iright
  isplit
  · iapply (minted_tag N t).mpr; iexact Hm
  · unfold wfHash
    iexists N, t, φ
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hφ
    · iintro !>
      inext
      icases H with #H
      iexact H

/-! ### Exponentials -/

@[rocq_alias cryptis.public_exp_iff]
theorem isPublic_exp_iff (hx : t.isExp) :
    isPublic (GF := GF) t ⊣⊢ minted t ∧
      ([∗multiset] f ∈ satoms t.exps, □ (isPublic ↑f → isPublic (t.exp ↑f⁻¹))) ∧
      ((∃ f, ⌜f ∈ satoms t.exps⌝ ∧ (isPublic ↑f ∨ expPred ↑f t) ∧
          isPublic (t.exp ↑f⁻¹)) ∨
        [∗multiset] f ∈ satoms t.exps, expPred ↑f t) := by
  rw [isPublic_eq]
  rw [publicAtom_eq_false (.inr (.inr hx))]
  constructor
  · iintro ⟨#Hm, (⟨%ts, %hd, -⟩ | ⟨%o, %hm, -⟩ | ⟨-, H⟩ | %hf)⟩
    rotate_left 3
    · cases hf
    · simp [hd.isExp_eq_false] at hx
    · simp [isExp_eq_false_of_isProd hm] at hx
    · isplit
      · iexact Hm
      · iexact H
  · iintro ⟨#Hm, H⟩
    isplit
    · iexact Hm
    · iright; iright; ileft
      isplit
      · ipureintro; exact hx
      · iexact H

@[rocq_alias cryptis.public_TExp_iff]
theorem isPublic_exp_iff_of_atom (hx : t₁.isExp = false) (hg : t₁.isProd .gmul = false)
    (hm : t₂.isProd .mul = false) :
    isPublic (GF := GF) (t₁.exp t₂) ⊣⊢ minted t₁ ∧ minted t₂ ∧
      (isPublic t₂ ∨ expPred t₂ (t₁.exp t₂)) ∧ □ (isPublic t₂ → isPublic t₁) := by
  have hexps : (t₁.exp t₂).exps = {t₂} := by rw [exps_exp hx hg, factors_eq_singleton hm]
  have hsat : satoms (t₁.exp t₂).exps = {E.ofTerm t₂} := by simp [hexps, satoms]
  have hxt : (t₁.exp t₂).isExp := isExp_of_mem_exps (by rw [hexps]; exact SMS.mem_singleton.mpr rfl)
  rw [(isPublic_exp_iff hxt).to_eq, (minted_exp hx hg t₂).to_eq, hsat,
    (bigSepMultiset_singleton _).to_eq, (bigSepMultiset_singleton _).to_eq]
  simp only [Multiset.mem_singleton]
  constructor
  · iintro ⟨⟨#Hm1, #Hm2⟩, #Hs, #H⟩
    rw [coe_inv, coe_ofTerm, exp_exp_inv]
    isplit
    · iexact Hm1
    isplit
    · iexact Hm2
    isplit
    · icases H with (⟨%f, %hf, #H, -⟩ | #H)
      · rw [hf]; iexact H
      · iright; iexact H
    · iexact Hs
  · iintro ⟨#Hm1, #Hm2, #Hj, #Hp⟩
    isplit
    · isplit
      · iexact Hm1
      · iexact Hm2
    isplit
    · rw [coe_inv, coe_ofTerm, exp_exp_inv]
      iexact Hp
    icases Hj with (#Hj | #Hj)
    · ileft
      iexists E.ofTerm t₂
      rw [coe_inv, coe_ofTerm, exp_exp_inv]
      isplit
      · ipureintro; rfl
      isplit
      · ileft; iexact Hj
      · iapply Hp $$ Hj
    · iright; iexact Hj

@[rocq_alias cryptis.public_satoms]
theorem isPublic_satoms {f : Term.E} (h : f ∈ satoms t.exps) :
    isPublic (GF := GF) t -∗ □ (isPublic ↑f → isPublic (t.exp ↑f⁻¹)) := by
  iintro #Hp
  icases (isPublic_exp_iff (isExp_of_mem_satoms h)).mp $$ Hp with ⟨-, #Hs, -⟩
  iapply bigSepMultiset_mem h $$ Hs

/-- If `t₂` is public, one of the positive exponents `ts` of `t₂` is public, or its owner agreed to
publish an exponential with the same base that has all of `ts` as exponents. -/
@[rocq_alias cryptis.public_exp_inv_gen]
theorem isPublic_exp_inv_of_le {ts : Multiset Term} {t₁ : Term} (h₁ : t₁ ∈ ts) (t₂ : Term)
    (hts : ts ≤ t₂.exps.posPart) :
    isPublic (GF := GF) t₂ -∗ ∃ t, ⌜t ∈ ts⌝ ∧ (isPublic t ∨
      ∃ t₃, ⌜t₃.base = t₂.base⌝ ∧ ⌜ts ≤ t₃.exps.posPart⌝ ∧ expPred t t₃) := by
  induction t₂ using tsize_induction with | h t₂ IH => ?_
  have ht₁ : t₁ ∈ t₂.exps.posPart := Multiset.mem_of_le hts h₁
  have hx₂ := isExp_of_mem_exps (SMS.mem_of_mem_posPart ht₁)
  have hg₂ := isProd_eq_false_of_isExp .gmul hx₂
  iintro #Hp
  icases (isPublic_exp_iff hx₂).mp $$ Hp with ⟨-, -, (⟨%f, %hf, #Hj, #Hp⟩ | #Hall)⟩
  rotate_left
  · iexists t₁
    isplit
    · ipureintro; exact h₁
    iright
    iexists t₂
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; exact hts
    · iapply bigSepMultiset_mem (s := satoms t₂.exps)
        (Multiset.mem_add.mpr (.inl (Multiset.mem_map_of_mem _ ht₁))) $$ Hall
  by_cases hts' : ↑f ∈ ts
  · iexists ↑f
    isplit
    · ipureintro; exact hts'
    icases Hj with (#Hj | #Hj)
    · ileft; iexact Hj
    · iright
      iexists t₂
      isplit
      · ipureintro; rfl
      isplit
      · ipureintro; exact hts
      · iexact Hj
  have hcnt : ∀ u ∈ ts, count .mul u ↑f ≤ 0 := fun u hu => by
    have hut : E.ofTerm u ≠ f := fun e => hts' (e ▸ hu)
    have hum := isProd_of_mem_factors (SMS.mem_of_mem_posPart (Multiset.mem_of_le hts hu))
    have hat := isProd_or_of_mem_satoms hf
    rw [← coe_ofTerm (o := .mul) u, ← scount_of_isProd_eq_false (f := E.ofTerm u) hum]
    by_cases hui : E.ofTerm u = f⁻¹
    · rw [hui, scount_inv_left, scount_self hat]; omega
    · rw [scount_eq_zero hat hut hui]
  rw [← base_exp hg₂ ↑f⁻¹]
  iapply IH _ (tsize_lt_of_mem_satoms hf).2 ?_ $$ Hp
  refine Multiset.le_iff_count.mpr fun u => ?_
  have hle := Multiset.le_iff_count.mp hts u
  rw [count_posPart_exps] at hle ⊢
  rw [count_expo_exp hg₂, count_coe_inv]
  by_cases hu : u ∈ ts
  · have := hcnt u hu; omega
  · rw [Multiset.count_eq_zero_of_notMem hu]; omega

@[rocq_alias cryptis.public_exp_inv_gen_set]
theorem isPublic_exp_inv_of_subset {ts : Multiset Term} {t₁ : Term} (h₁ : t₁ ∈ ts) (t₂ : Term)
    (hts : ts ⊆ t₂.exps.posPart) :
    isPublic (GF := GF) t₂ -∗ ∃ t, ⌜t ∈ ts⌝ ∧ (isPublic t ∨
      ∃ t₃, ⌜t₃.base = t₂.base⌝ ∧ ⌜ts ⊆ t₃.exps.posPart⌝ ∧ expPred t t₃) := by
  iintro #Hp
  icases isPublic_exp_inv_of_le (Multiset.mem_dedup.mpr h₁) t₂
    ((Multiset.le_iff_subset (Multiset.nodup_dedup ts)).mpr
      (Multiset.Subset.trans (Multiset.dedup_subset ts) hts)) $$ Hp
    with ⟨%t, %ht, (#H | ⟨%t₃, %hb, %h₃, #H⟩)⟩
  · iexists t
    isplit
    · ipureintro; exact Multiset.mem_dedup.mp ht
    · ileft; iexact H
  · iexists t
    isplit
    · ipureintro; exact Multiset.mem_dedup.mp ht
    iright
    iexists t₃
    isplit
    · ipureintro; exact hb
    isplit
    · ipureintro
      exact Multiset.Subset.trans (Multiset.subset_dedup ts) (Multiset.subset_of_le h₃)
    · iexact H

@[rocq_alias cryptis.public_exp_inv]
theorem isPublic_exp_inv {t₁ : Term} (t₂ : Term) (h : t₁ ∈ t₂.exps.posPart) :
    isPublic (GF := GF) t₂ -∗ ∃ t, ⌜t ∈ t₂.exps.posPart⌝ ∧ (isPublic t ∨
      ∃ t₃, ⌜t₃.base = t₂.base⌝ ∧ ⌜t₂.exps.posPart ⊆ t₃.exps.posPart⌝ ∧ expPred t t₃) :=
  isPublic_exp_inv_of_subset h t₂ (Multiset.Subset.refl _)

@[rocq_alias cryptis.public_exp_inv_same]
theorem isPublic_exp_inv_same {t₁ : Term} (t₂ : Term) (h : t₁ ∈ t₂.exps.posPart) :
    isPublic (GF := GF) t₂ -∗ isPublic t₁ ∨
      ∃ t₂', ⌜t₂'.base = t₂.base⌝ ∗ ⌜t₁ ∈ t₂'.exps.posPart⌝ ∗ expPred t₁ t₂' := by
  iintro #Hp
  icases isPublic_exp_inv_of_subset (Multiset.mem_singleton_self t₁) t₂
    (Multiset.singleton_subset.mpr h) $$ Hp with ⟨%t, %ht, (#H | ⟨%t₃, %hb, %h₃, #H⟩)⟩
  · rw [Multiset.mem_singleton.mp ht]
    ileft; iexact H
  · rw [Multiset.mem_singleton.mp ht]
    iright
    iexists t₃
    isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact Multiset.singleton_subset.mp h₃
    · iexact H

/-- `f`, an atom or the inverse of one, is the last exponent of `t₁.exp f`, added by the attacker
or by the owner of `f`. Stripping exponents of `t₁` keeps its base, so the owner need only consent
for that base. -/
@[rocq_alias cryptis.public_TExp_last]
theorem isPublic_exp_last {f : Term.E}
    (hf : (f : Term).isProd .mul = false ∨ (↑f⁻¹ : Term).isProd .mul = false) (t₁ : Term)
    (hg : t₁.isProd .gmul = false) (hft : f⁻¹ ∉ satoms t₁.exps) :
    minted (GF := GF) ↑f -∗
    □ (∀ t, ⌜t.base = t₁.base⌝ -∗ isPublic t -∗
      isPublic ↑f ∨ expPred ↑f (t.exp ↑f)) -∗
    isPublic t₁ -∗ isPublic (t₁.exp ↑f) := by
  induction t₁ using tsize_induction with | h t₁ IH => ?_
  have hsc g : scount g (t₁.exp ↑f).expo = scount g t₁.expo + scount g ↑f :=
    scount_expo_exp hg g ↑f
  have hnn : 0 ≤ scount f t₁.expo := by
    have := mt mem_satoms.mpr hft
    rw [scount_inv_left] at this
    omega
  have hft' : f ∈ satoms (t₁.exp ↑f).exps :=
    mem_satoms.mpr (by rw [hsc, scount_self hf]; omega)
  iintro #Hmf #Hj #Hp₁
  iapply (isPublic_exp_iff (isExp_of_mem_satoms hft')).mpr
  isplit
  · iapply minted_exp_intro
    isplit
    · iapply isPublic_minted $$ Hp₁
    · iexact Hmf
  isplit
  rotate_left
  · ileft
    iexists f
    rw [exp_exp_coe_inv]
    isplit
    · ipureintro; exact hft'
    isplit
    · iapply Hj $$ %t₁ %rfl Hp₁
    · iexact Hp₁
  iapply bigSepMultiset_forall.mpr
  iintro %g %hg' !> #Hpg
  by_cases hgf : g = f
  · rw [hgf, exp_exp_coe_inv]
    iexact Hp₁
  have hgi : g ≠ f⁻¹ := by
    rintro rfl
    have := mem_satoms.mp hg'
    rw [hsc, scount_inv_left, scount_inv_left, scount_self hf] at this
    omega
  have hgt : g ∈ satoms t₁.exps := mem_satoms.mpr <| by
    have := mem_satoms.mp hg'
    rw [hsc, scount_eq_zero hf hgf hgi] at this
    omega
  have hfg : f⁻¹ ∉ satoms (t₁.exp ↑g⁻¹).exps := by
    have hfg₁ : f⁻¹ ≠ g := fun e => hft (e ▸ hgt)
    have hfg₂ : f⁻¹ ≠ g⁻¹ := inv_injective.ne (Ne.symm hgf)
    rw [exps, mem_satoms, scount_expo_exp hg, scount_inv_right,
      scount_eq_zero (isProd_or_of_mem_satoms hgt) hfg₁ hfg₂, scount_inv_left]
    omega
  ihave #Hp := isPublic_satoms hgt $$ Hp₁ Hpg
  rw [exp_right_comm]
  iapply IH _ (tsize_lt_of_mem_satoms hgt).2 (isProd_exp_eq_false hg _) hfg $$ Hmf [] Hp
  iintro !> %t %ht
  iapply Hj $$ %t %(ht.trans (base_exp hg _))

/-- The attacker raises a public term to a public atom or the inverse of one. -/
@[rocq_alias cryptis.public_TExp_satom]
theorem isPublic_exp_satom (hg : t₁.isProd .gmul = false) {f : Term.E}
    (hf : (f : Term).isProd .mul = false ∨ (↑f⁻¹ : Term).isProd .mul = false) :
    isPublic (GF := GF) t₁ -∗ isPublic ↑f -∗ isPublic (t₁.exp ↑f) := by
  iintro #Hp₁ #Hpf
  by_cases hft : f⁻¹ ∈ satoms t₁.exps
  · have : t₁.exp ↑f = t₁.exp ↑f⁻¹⁻¹ := by rw [inv_inv]
    rw [this]
    iapply isPublic_satoms hft $$ Hp₁
    iapply (isPublic_coe_inv f).mpr
    iexact Hpf
  · iapply isPublic_exp_last hf t₁ hg hft $$ [] [] Hp₁
    · iapply isPublic_minted $$ Hpf
    · iintro !> %t - -
      ileft
      iexact Hpf

@[rocq_alias cryptis.public_TExp_make_intro]
theorem isPublic_exp_prod_make (hg : t.isProd .gmul = false) (X Y : Multiset Term)
    (h : ∀ u ∈ X + Y, u.isProd .mul = false) :
    isPublic (GF := GF) t -∗ ([∗multiset] u ∈ X + Y, isPublic u) -∗
      isPublic (t.exp (prod .mul (.make X Y))) := by
  rw [bigSepMultiset_forall.to_eq]
  induction X using Multiset.induction_on with
  | empty =>
    induction Y using Multiset.induction_on with
    | empty =>
      rw [SMS.make_zero_zero, exp_unit]
      iintro #Hp -
      iexact Hp
    | cons y Y ih =>
      have hy : y.isProd .mul = false := h y (by simp)
      iintro #Hp #HY
      rw [exp_prod_make_cons_right]
      iapply isPublic_exp_satom (isProd_exp_eq_false hg _) (f := (E.ofTerm y)⁻¹)
        (.inr (by rw [inv_inv]; exact hy)) $$ [] []
      · iapply ih (fun u hu => h u (by simp_all)) $$ Hp
        iintro %u %hu
        iapply HY $$ %u %(by simp_all)
      · iapply (isPublic_coe_inv (E.ofTerm y)).mpr
        iapply HY $$ %y %(by simp)
  | cons x X ih =>
    have hx : x.isProd .mul = false := h x (by simp)
    iintro #Hp #HXY
    rw [exp_prod_make_cons_left]
    have := isPublic_exp_satom (GF := GF) (isProd_exp_eq_false hg (prod .mul (.make X Y)))
      (f := E.ofTerm x) (.inl hx)
    iapply this $$ [] []
    · iapply ih (fun u hu => h u (by simp_all)) $$ Hp
      iintro %u %hu
      iapply HXY $$ %u %(by simp_all)
    · iapply HXY $$ %x %(by simp)

/-- The attacker raises a public term to a public exponent. -/
theorem isPublic_exp (t₁ t₂ : Term) :
    isPublic (GF := GF) t₁ -∗ isPublic t₂ -∗ isPublic (t₁.exp t₂) := by
  induction t₁ using tsize_induction with | h t₁ IH => ?_
  iintro #Hp₁ #Hp₂
  cases hg : t₁.isProd .gmul
  · have he : t₁.exp t₂ =
        t₁.exp (prod .mul (.make (t₂.factors .mul).posPart (t₂.factors .mul).negPart)) := by
      rw [SMS.make_posPart_negPart, prod_factors]
    rw [he]
    icases (isPublic_factors .mul t₂).mp $$ Hp₂ with ⟨-, #Hfs⟩
    rw [SMS.elements]
    iapply isPublic_exp_prod_make hg _ _ (fun u hu => isProd_of_mem_factors hu) $$ Hp₁ Hfs
  · iapply (isPublic_factors .gmul _).mpr
    isplit
    · iapply minted_exp_intro
      isplit
      · iapply isPublic_minted $$ Hp₁
      · iapply isPublic_minted $$ Hp₂
    iapply bigSepMultiset_forall.mpr
    iintro %x %hx
    rw [factors_exp] at hx
    obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map hx
    icases (isPublic_factors .gmul t₁).mp $$ Hp₁ with ⟨-, #Hfs⟩
    iapply IH u (tsize_lt_of_mem_factors hg hu) $$ [] Hp₂
    iapply bigSepMultiset_mem hu $$ Hfs

/-- The attacker raises a public element of the group to a public exponent. -/
@[rocq_alias cryptis.public_TExp]
theorem isPublic_coe_smul (a : Term.E) (g : Term.G) :
    isPublic (GF := GF) ↑g -∗ isPublic ↑a -∗ isPublic ↑(a • g) :=
  isPublic_exp ↑g ↑a

/-- `t₁.exp t₂` is the group product of the `u.exp t₂` for the group factors `u` of `t₁`, so it is
public when they all are. -/
@[rocq_alias cryptis.public_TExp_gfactors]
theorem isPublic_exp_of_factors (t₁ t₂ : Term) :
    ([∗multiset] u ∈ (t₁.factors .gmul).elements, isPublic (GF := GF) (u.exp t₂)) ⊢
      isPublic (t₁.exp t₂) := by
  rw [bigSepMultiset_forall.to_eq]
  iintro #H
  iapply (isPublic_factors .gmul _).mpr
  isplit
  · iapply (minted_factors .gmul _).mpr
    iapply bigSepMultiset_forall.mpr
    iintro %x %hx
    rw [factors_exp] at hx
    obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map hx
    iapply isPublic_minted
    iapply H $$ %u %hu
  · iapply bigSepMultiset_forall.mpr
    iintro %x %hx
    rw [factors_exp] at hx
    obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map hx
    iapply H $$ %u %hu

/-! ### Products -/

@[rocq_alias cryptis.public_TMul_intro, rocq_alias cryptis.public_TGMul_intro]
theorem isPublic_prod_intro {o : TermOpN} (hs : ∀ u ∈ s, u.isProd o = false) :
    ([∗multiset] u ∈ s.elements, isPublic (GF := GF) u) ⊢ isPublic (prod o s) := by
  rw [(isPublic_factors o (prod o s)).to_eq, factors_prod_of_forall hs, (minted_prod hs).to_eq]
  iintro #H
  isplit
  · iapply BigSepMS.bigSepMS_impl $$ H
    iintro !> %u - #Hu
    iapply isPublic_minted $$ Hu
  · iexact H

@[rocq_alias cryptis.public_TMul2, rocq_alias cryptis.public_TGMul2]
theorem isPublic_coe_mul {o : TermOpN} (a b : ProdGroup o) :
    isPublic (GF := GF) ↑a -∗ isPublic ↑b -∗ isPublic ↑(a * b) := by
  iintro #H1 #H2
  icases (isPublic_factors o _).mp $$ H1 with ⟨#Hm1, #Hf1⟩
  icases (isPublic_factors o _).mp $$ H2 with ⟨#Hm2, #Hf2⟩
  iapply (isPublic_factors o _).mpr
  isplit
  · iapply (minted_factors o _).mpr
    iapply bigSepMultiset_factors_coe_mul $$ [] []
    · iapply (minted_factors o _).mp $$ Hm1
    · iapply (minted_factors o _).mp $$ Hm2
  · iapply bigSepMultiset_factors_coe_mul $$ Hf1 Hf2

@[rocq_alias cryptis.public_TMul0, rocq_alias cryptis.public_TGMul0]
theorem isPublic_coe_one (o : TermOpN) : ⊢ isPublic (GF := GF) ↑(1 : ProdGroup o) :=
  bigSepMultiset_zero.2.trans <|
    isPublic_prod_intro (s := 0) fun u hu => absurd hu (by simp [← SMS.mem_elements])

/-! ### Further rules -/

/-- A minted term is public if the logic is inconsistent. -/
@[rocq_alias cryptis.False_public]
theorem isPublic_of_later_false (t : Term) : minted (GF := GF) t -∗ ▷ False -∗ isPublic t := by
  induction t with
  | int n =>
    iintro - -
    iapply (isPublic_int n).mpr
    itrivial
  | pair t₁ t₂ ih₁ ih₂ =>
    iintro #Hm #Hf
    icases (minted_pair t₁ t₂).mp $$ Hm with ⟨#Hm₁, #Hm₂⟩
    iapply (isPublic_pair t₁ t₂).mpr
    isplit
    · iapply ih₁ $$ Hm₁ Hf
    · iapply ih₂ $$ Hm₂ Hf
  | nonce a =>
    iintro #Hm #Hf
    iapply (isPublic_nonce a).mpr
    isplitl []
    · unfold BIBase.except0; ileft; iexact Hf
    · iapply (minted_nonce a).mp $$ Hm
  | key kt t ih =>
    iintro #Hm #Hf
    iapply (isPublic_key kt t).mpr
    ileft
    iapply ih $$ [] Hf
    iapply (minted_key kt t).mp $$ Hm
  | sealed k t ihk iht =>
    iintro #Hm #Hf
    icases (minted_sealed k t).mp $$ Hm with ⟨#Hmk, #Hmt⟩
    iapply (isPublic_sealed k t).mpr
    ileft
    isplit
    · iapply ihk $$ Hmk Hf
    · iapply iht $$ Hmt Hf
  | hash t ih =>
    iintro #Hm #Hf
    iapply (isPublic_hash t).mpr
    ileft
    iapply ih $$ [] Hf
    iapply (minted_hash t).mp $$ Hm
  | exp b e hx hg _ ihb ihe =>
    iintro #Hm #Hf
    icases (minted_exp hx hg e).mp $$ Hm with ⟨#Hmb, #Hme⟩
    iapply isPublic_exp $$ [] []
    · iapply ihb $$ Hmb Hf
    · iapply ihe $$ Hme Hf
  | prod o s hs _ ih =>
    iintro #Hm #Hf
    iapply isPublic_prod_intro hs
    iapply bigSepMultiset_forall.mpr
    iintro %u %hu
    iapply ih u hu $$ [] Hf
    ihave #Hms := (minted_prod hs).mp $$ Hm
    iapply bigSepMultiset_mem hu $$ Hms

@[rocq_alias cryptis.except_0_public]
theorem isPublic_of_except0 (t : Term) : minted (GF := GF) t -∗ ◇ isPublic t -∗ isPublic t := by
  unfold BIBase.except0
  iintro #Hm (#Hf | #H)
  · iapply isPublic_of_later_false $$ Hm Hf
  · iexact H

/-- Negative exponents have no owner, so they are public when the exponential is. -/
@[rocq_alias cryptis.public_exps_neg]
theorem isPublic_of_mem_negPart_exps (t₁ : Term) (h : t₂ ∈ t₁.exps.negPart) :
    isPublic (GF := GF) t₁ -∗ isPublic t₂ := by
  induction t₁ using tsize_induction with | h t₁ IH => ?_
  have hm₂ := isProd_of_mem_factors (SMS.mem_of_mem_negPart h)
  have h₂ : (E.ofTerm t₂)⁻¹ ∈ satoms t₁.exps := (inv_mem_satoms hm₂).mpr h
  have hg₁ := isProd_eq_false_of_isExp .gmul (isExp_of_mem_satoms h₂)
  iintro #Hp
  ihave #Hm₂ : minted t₂ $$ [Hp]
  · icases (minted_base_exps t₁).mp $$ [Hp] with ⟨-, #Hms⟩
    · iapply isPublic_minted $$ Hp
    iapply bigSepMultiset_mem (SMS.mem_of_mem_negPart h) $$ Hms
  icases (isPublic_exp_iff (isExp_of_mem_satoms h₂)).mp $$ Hp with
    ⟨-, -, (⟨%f, %hf, #Hj, #Hp'⟩ | #Hall)⟩
  rotate_left
  · iapply isPublic_of_later_false $$ Hm₂
    iapply (expPred_inv (f := E.ofTerm t₂) hm₂ t₁).mp
    iapply bigSepMultiset_mem h₂ $$ Hall
  by_cases hfe : f = (E.ofTerm t₂)⁻¹
  · rw [hfe]
    icases Hj with (#Hj | #Hj)
    · iapply (isPublic_coe_inv (GF := GF) (E.ofTerm t₂)).mp $$ Hj
    · iapply isPublic_of_later_false $$ Hm₂
      iapply (expPred_inv (f := E.ofTerm t₂) hm₂ t₁).mp $$ Hj
  have hne₁ : (E.ofTerm t₂)⁻¹ ≠ f := Ne.symm hfe
  have hne₂ : (E.ofTerm t₂)⁻¹ ≠ f⁻¹ := by
    intro e
    have h₁ := mem_satoms.mp hf
    have h₃ := mem_satoms.mp h₂
    rw [inv_injective e, scount_inv_left] at h₃
    omega
  iapply IH _ (tsize_lt_of_mem_satoms hf).2 ?_ $$ Hp'
  rw [exps, ← inv_mem_satoms hm₂, mem_satoms, scount_expo_exp hg₁, scount_inv_right,
    scount_eq_zero (isProd_or_of_mem_satoms hf) hne₁ hne₂]
  simpa using mem_satoms.mp h₂

/-- The owner of `t₂` raises a public term to `t₂`, as in an oblivious PRF. It need only consent
for the terms with the base of a group factor of `t₁`. -/
@[rocq_alias cryptis.public_TExp_consent]
theorem isPublic_exp_consent (hm₂ : t₂.isProd .mul = false) :
    minted (GF := GF) t₂ -∗
    □ (∀ t, ⌜∃ u ∈ t₁.factors .gmul, u.base = t.base⌝ -∗ isPublic t -∗ expPred t₂ (t.exp t₂)) -∗
    isPublic t₁ -∗ isPublic (t₁.exp t₂) := by
  iintro #Hm₂ #Hc #Hp₁
  icases (isPublic_factors .gmul t₁).mp $$ Hp₁ with ⟨-, #Hfs⟩
  iapply isPublic_exp_of_factors
  iapply bigSepMultiset_forall.mpr
  iintro %u %hu
  have hgu := isProd_of_mem_factors hu
  ihave #Hpu := bigSepMultiset_mem hu $$ Hfs
  by_cases h₂u : (E.ofTerm t₂)⁻¹ ∈ satoms u.exps
  · iapply isPublic_exp_satom (GF := GF) hgu (f := E.ofTerm t₂) (.inl hm₂) $$ Hpu
    iapply isPublic_of_mem_negPart_exps u ((inv_mem_satoms hm₂).mp h₂u) $$ Hpu
  · iapply isPublic_exp_last (GF := GF) (f := E.ofTerm t₂) (.inl hm₂) u hgu h₂u $$ Hm₂ [] Hpu
    iintro !> %t %ht #Hp
    iright
    iapply Hc $$ %t %⟨u, hu, ht.symm⟩ Hp

/-! ### Lists and tags -/

@[rocq_alias cryptis.public_of_list]
theorem isPublic_ofList (ts : List Term) :
    isPublic (GF := GF) (Spec.ofList ts) ⊣⊢ [∗list] t ∈ ts, isPublic t := by
  induction ts with
  | nil => exact (isPublic_int 0).trans true_emp
  | cons t ts ih =>
    exact (isPublic_pair _ _).trans <| (and_congr .rfl ih).trans persistent_and_sep

/-! The next three equations rewrite the publicity of a list literal into a conjunction, with
`simp only` or `rw`. -/

theorem isPublic_ofList_nil : isPublic (GF := GF) (Spec.ofList []) = iprop(True) :=
  (isPublic_int 0).to_eq

theorem isPublic_ofList_singleton (t : Term) :
    isPublic (GF := GF) (Spec.ofList [t]) = isPublic t :=
  ((isPublic_pair _ _).trans <| (and_congr .rfl (isPublic_int 0)).trans and_true).to_eq

theorem isPublic_ofList_cons_cons (t t' : Term) (ts : List Term) :
    isPublic (GF := GF) (Spec.ofList (t :: t' :: ts)) =
      iprop(isPublic t ∧ isPublic (Spec.ofList (t' :: ts))) :=
  (isPublic_pair _ _).to_eq

@[rocq_alias cryptis.public_to_list]
theorem isPublic_of_toList_eq_some {ts : List Term} (h : Spec.toList t = some ts) :
    isPublic (GF := GF) t -∗ [∗list] u ∈ ts, isPublic u := by
  rw [Spec.toList_eq_some_iff.mp h]
  exact entails_wand (isPublic_ofList ts).1

@[rocq_alias cryptis.public_Tag]
theorem isPublic_ofNamespace (N : Namespace) :
    isPublic (GF := GF) (ofNamespace N) ⊣⊢ True :=
  isPublic_int _

@[rocq_alias cryptis.public_tag]
theorem isPublic_tag (N : Namespace) (t : Term) :
    isPublic (GF := GF) (Spec.tag (ofNamespace N) t) ⊣⊢ isPublic t :=
  (isPublic_pair _ _).trans <| (and_congr (isPublic_ofNamespace N) .rfl).trans true_and

@[rocq_alias cryptis.public_THashE]
theorem isPublic_hash_elim {N : Namespace} {φ : Term → IProp GF} :
    hashPred N φ -∗ isPublic (hash (Spec.tag (ofNamespace N) t)) -∗
      isPublic t ∨ minted t ∗ ▷ □ φ t := by
  iintro #Hφ #Hp
  icases (isPublic_hash _).mp $$ Hp with (#H | ⟨#Hm, #Hw⟩)
  · ileft
    iapply (isPublic_tag N t).mp $$ H
  · iright
    isplitl []
    · iapply (minted_tag N t).mp $$ Hm
    · ihave #H := wfHash_elim $$ Hw Hφ
      inext
      iintro !>
      iexact H

/-! ### Sealed messages -/

theorem openCond_tag (N : Namespace) (k t : Term) :
    openCond (GF := GF) isPublic k (Spec.tag (ofNamespace N) t) ⊣⊢ openCond isPublic k t := by
  unfold openCond
  split
  · exact intuitionistically_congr (imp_congr .rfl (isPublic_tag N t))
  · exact .rfl

@[rocq_alias cryptis.public_TSeal_tag]
theorem isPublic_sealed_tag (k : Term) (N : Namespace) (t : Term) :
    isPublic (GF := GF) (sealed k (Spec.tag (ofNamespace N) t)) ⊣⊢
      isPublic k ∧ isPublic t ∨ minted k ∧ minted t ∧
        match k.functionality with
        | some F => ∃ Φ : Term → Term → IProp GF, ⌜Spec.isSealKey k⌝ ∧ sealPred F N Φ ∧
            □ ▷ Φ (Spec.skey k) t ∧ openCond isPublic k t
        | none => True := by
  refine (isPublic_sealed _ _).trans <| or_congr (and_congr .rfl (isPublic_tag N t)) ?_
  refine (and_congr ((minted_sealed _ _).trans (and_congr .rfl (minted_tag N t))) .rfl).trans
    and_assoc |>.trans (and_congr .rfl (and_congr .rfl ?_))
  unfold sealCond
  split
  · rw [(openCond_tag N k t).to_eq]
    constructor
    · iintro ⟨%hk, #Hw, #Ho⟩
      unfold wfSeal
      icases Hw with ⟨%N', %t', %Φ, %ht, #HΦ, #H⟩
      obtain ⟨hN, rfl⟩ := Spec.tag_inj.mp ht
      rw [ofNamespace_inj.mp hN]
      iexists Φ
      isplit
      · ipureintro; exact hk
      isplit
      · iexact HΦ
      isplit
      · iexact H
      · iexact Ho
    · iintro ⟨%Φ, %hk, #HΦ, #H, #Ho⟩
      isplit
      · ipureintro; exact hk
      isplit
      · unfold wfSeal
        iexists N, t, Φ
        isplit
        · ipureintro; rfl
        isplit
        · iexact HΦ
        · iexact H
      · iexact Ho
  · exact .rfl

@[rocq_alias cryptis.public_TSealE]
theorem isPublic_sealed_elim {F : Functionality} {N : Namespace} {Φ : Term → Term → IProp GF}
    (hk : k.functionality = some F ∧ Spec.isSealKey k) :
    isPublic (GF := GF) (sealed k (Spec.tag (ofNamespace N) t)) -∗ sealPred F N Φ -∗
      isPublic k ∧ isPublic t ∨ □ ▷ Φ (Spec.skey k) t ∧ openCond isPublic k t := by
  iintro #Hp #HΦ
  icases (isPublic_sealed _ _).mp $$ Hp with (⟨#Hk, #Ht⟩ | ⟨-, #H⟩)
  · ileft
    isplit
    · iexact Hk
    · iapply (isPublic_tag N t).mp $$ Ht
  · iright
    unfold sealCond
    rw [hk.1]
    icases H with ⟨-, #Hw, #Ho⟩
    isplit
    · iapply wfSeal_elim $$ Hw HΦ
    · iapply (openCond_tag N k t).mp $$ Ho

@[rocq_alias cryptis.public_TSealIS]
theorem isPublic_sealed_intro {F : Functionality} {N : Namespace} {Φ : Term → Term → IProp GF}
    (hk : k.functionality = some F ∧ Spec.isSealKey k) :
    sealPred F N Φ -∗ □ Φ (Spec.skey k) t -∗ minted k -∗ minted t -∗
      openCond isPublic k t -∗ isPublic (sealed k (Spec.tag (ofNamespace N) t)) := by
  iintro #HΦ #H #Hmk #Hmt #Ho
  iapply (isPublic_sealed _ _).mpr
  iright
  isplit
  · iapply (minted_sealed _ _).mpr
    isplit
    · iexact Hmk
    · iapply (minted_tag N t).mpr $$ Hmt
  unfold sealCond
  rw [hk.1]
  isplit
  · ipureintro; exact hk.2
  isplit
  · unfold wfSeal
    iexists N, t, Φ
    isplit
    · ipureintro; rfl
    isplit
    · iexact HΦ
    · iintro !>; inext; iexact H
  · iapply (openCond_tag N k t).mpr $$ Ho

@[rocq_alias cryptis.public_TSealIP]
theorem isPublic_sealed_of_isPublic (k t : Term) :
    isPublic (GF := GF) k -∗ isPublic t -∗ isPublic (sealed k t) := by
  iintro #Hk #Ht
  iapply (isPublic_sealed k t).mpr
  ileft
  isplit
  · iexact Hk
  · iexact Ht

/-! ### Nonces -/

@[rocq_alias cryptis.nonce_alloc]
theorem nonce_alloc (P : Nonce → IProp GF) (Q : Term → IProp GF) (a : Nonce) :
    metaToken a.loc ⊤ -∗
      (minted (GF := GF) (nonce a) -∗ False) ∧
      |==> (minted (nonce a) ∗ □ (isPublic (nonce a) ↔ ▷ □ P a) ∗
        □ (∀ t, expPred (nonce a) t ↔ ▷ □ Q t)) := by
  have hdh : (↑(nroot.@"dh") : CoPset) ⊆ ⊤ \ ↑(nroot.@"nonce") :=
    nclose_subset_diff CoPset.subseteq_top (ndot_ne_disjoint nroot (by decide))
  have hmt : (↑(nroot.@"minted") : CoPset) ⊆ (⊤ \ ↑(nroot.@"nonce")) \ ↑(nroot.@"dh") :=
    nclose_subset_diff (nclose_subset_diff CoPset.subseteq_top
      (ndot_ne_disjoint nroot (by decide))) (ndot_ne_disjoint nroot (by decide))
  iintro Htok
  isplit
  · iintro #Hm
    ihave #Hm := (minted_nonce a).mp $$ Hm
    iapply meta_metaToken_valid' CoPset.subseteq_top $$ Hm Htok
  imod iOwn_alloc (F := DFracAgree.DFracAgreeRF (DiscreteFunOF fun _ : Nonce => LaterOF IdOF))
    (savedPred .discard P) (savedPred_valid.mpr DFrac.valid_discard) with ⟨%γP, #HP⟩
  imod iOwn_alloc (F := DFracAgree.DFracAgreeRF (DiscreteFunOF fun _ : Term => LaterOF IdOF))
    (savedPred .discard Q) (savedPred_valid.mpr DFrac.valid_discard) with ⟨%γQ, #HQ⟩
  icases (metaToken_difference CoPset.subseteq_top).mp $$ Htok with ⟨Hn, Htok⟩
  imod meta_set γP LawfulSet.subset_refl $$ Hn with #Hn
  icases (metaToken_difference hdh).mp $$ Htok with ⟨Hd, Htok⟩
  imod meta_set γQ LawfulSet.subset_refl $$ Hd with #Hd
  icases (metaToken_difference hmt).mp $$ Htok with ⟨Hmt, -⟩
  imod meta_set () LawfulSet.subset_refl $$ Hmt with #Hmt
  imodintro
  isplitl []
  · iapply (minted_nonce a).mpr $$ Hmt
  isplitl []
  · iintro !>
    isplit
    · iintro #Hp
      icases (isPublic_nonce a).mp $$ Hp with ⟨#Hpn, -⟩
      unfold BIBase.except0 pnonce
      icases Hpn with (#Hf | ⟨%γ', %P', #Hn', #HP', #H⟩)
      · inext; iexfalso; iexact Hf
      icases meta_agree $$ Hn Hn' with %rfl
      ihave Hv := iOwn_cmraValid_op $$ [HP HP']
      · isplitl []
        · iexact HP
        · iexact HP'
      icases (savedPred_op_validI (φ := P) (ψ := P')).mp $$ Hv with ⟨-, #Heq⟩
      ispecialize Heq $$ %a
      inext
      iintro !>
      irewrite [Heq]
      · exact OFE.id_ne
      iexact H
    · iintro #H
      iapply (isPublic_nonce a).mpr
      isplitl []
      · unfold BIBase.except0 pnonce
        iright
        iexists γP, P
        isplit
        · iexact Hn
        isplit
        · iexact HP
        · iexact H
      · iexact Hmt
  · iintro !> %t
    unfold expPred
    isplit
    · iintro ⟨%γ', %Q', #Hd', #HQ', #H⟩
      icases meta_agree $$ Hd Hd' with %rfl
      ihave Hv := iOwn_cmraValid_op $$ [HQ HQ']
      · isplitl []
        · iexact HQ
        · iexact HQ'
      icases (savedPred_op_validI (φ := Q) (ψ := Q')).mp $$ Hv with ⟨-, #Heq⟩
      ispecialize Heq $$ %t
      inext
      iintro !>
      irewrite [Heq]
      · exact OFE.id_ne
      iexact H
    · iintro #H
      iexists γQ, Q
      isplit
      · iexact Hd
      isplit
      · iexact HQ
      · iexact H

/-! ### Keys -/

@[rocq_alias cryptis.public_pkey]
theorem isPublic_pkey (k : Term) : isPublic (GF := GF) k ⊢ isPublic (Spec.pkey k) := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, k⟩ <;> simp only [Spec.pkey] <;> try exact .rfl
  all_goals
    iintro #Hp
    iapply (isPublic_key _ k).mpr
    iright
    isplit
    · iapply (minted_key _ k).mp
      iapply isPublic_minted $$ Hp
    · ipureintro; rfl

@[rocq_alias cryptis.public_adec_key, rocq_alias cryptis.public_adec_key',
  rocq_alias cryptis.public_sign_key, rocq_alias cryptis.public_sign_key',
  rocq_alias cryptis.public_senc_key, rocq_alias cryptis.public_senc_key']
theorem isPublic_coe_key {F : Functionality} (k : Key F) :
    isPublic (GF := GF) k ⊣⊢ isPublic k.seed := by
  refine (isPublic_key _ _).trans ⟨?_, or_intro_l⟩
  iintro (#H | ⟨-, %h⟩)
  · iexact H
  · cases F <;> simp [Spec.publicKeyType] at h

@[rocq_alias cryptis.public_aenc_key]
theorem isPublic_pkey_aenc (sk : Key .aenc) :
    isPublic (GF := GF) (Spec.pkey sk) ⊣⊢ minted sk := by
  refine (isPublic_key _ _).trans <| .trans ?_ (minted_coe_key sk).symm
  constructor
  · iintro (#H | ⟨#Hm, -⟩)
    · iapply isPublic_minted $$ H
    · iexact Hm
  · iintro #Hm
    iright
    isplit
    · iexact Hm
    · ipureintro; rfl

@[rocq_alias cryptis.public_verify_key]
theorem isPublic_pkey_sign (sk : Key .sign) :
    isPublic (GF := GF) (Spec.pkey sk) ⊣⊢ minted sk := by
  refine (isPublic_key _ _).trans <| .trans ?_ (minted_coe_key sk).symm
  constructor
  · iintro (#H | ⟨#Hm, -⟩)
    · iapply isPublic_minted $$ H
    · iexact Hm
  · iintro #Hm
    iright
    isplit
    · iexact Hm
    · ipureintro; rfl

/-! ### Secrets -/

/-- A one-shot ghost name that has not been set yet. -/
@[rocq_alias cryptis.pending]
def pending (γ : GName) : IProp GF := gmetaToken γ ⊤

/-- The one-shot ghost name `γ` has been set to `x`. -/
@[rocq_alias cryptis.shot]
def shot (γ : GName) (x : Pos) : IProp GF := gmeta γ nroot x

@[rocq_alias cryptis.persistent_shot]
instance shot_persistent (γ : GName) (x : Pos) : Persistent (shot (GF := GF) γ x) := by
  unfold shot; infer_instance

@[rocq_alias cryptis.timeless_shot]
instance shot_timeless (γ : GName) (x : Pos) : Timeless (shot (GF := GF) γ x) := by
  unfold shot; infer_instance

@[rocq_alias cryptis.pending_alloc]
theorem pending_alloc : ⊢ |==> ∃ γ, pending (GF := GF) γ := gmetaToken_alloc

@[rocq_alias cryptis.shot_alloc]
theorem shot_alloc (γ : GName) (x : Pos) : pending (GF := GF) γ ==∗ shot γ x :=
  gmeta_set x CoPset.subseteq_top

@[rocq_alias cryptis.pending_shot]
theorem pending_shot (γ : GName) (x : Pos) : pending (GF := GF) γ -∗ shot γ x -∗ False :=
  gmetaToken_gmeta CoPset.subseteq_top

@[rocq_alias cryptis.shot_agree]
theorem shot_agree (γ : GName) (x y : Pos) : shot (GF := GF) γ x -∗ shot γ y -∗ ⌜x = y⌝ :=
  gmeta_agree

/-- `t` is not public yet, and can be made public or secret forever. -/
@[rocq_alias cryptis.secret]
def secret (t : Term) : IProp GF :=
  iprop((|==> isPublic t) ∧ (|==> □ (isPublic t ↔ ▷ False)) ∧ (isPublic t -∗ ▷ False))

@[rocq_alias cryptis.secret_alloc]
theorem secret_alloc (t : Term) (γ : GName) :
    □ (isPublic (GF := GF) t ↔ ▷ shot γ 1) -∗ pending γ -∗ secret t := by
  unfold secret
  iintro #Hs Hp
  isplit
  · imod shot_alloc γ 1 $$ Hp with #Hsh
    imodintro
    icases Hs with ⟨-, #H⟩
    iapply H
    inext
    iexact Hsh
  isplit
  · imod shot_alloc γ 2 $$ Hp with #Hsh
    imodintro
    iintro !>
    isplit
    · iintro #Hpt
      icases Hs with ⟨#H, -⟩
      ihave #Hsh' := H $$ Hpt
      inext
      icases shot_agree γ 2 1 $$ Hsh Hsh' with %h
      exact absurd h (by decide)
    · iintro #Hf
      icases Hs with ⟨-, #H⟩
      iapply H
      inext
      iexfalso
      iexact Hf
  · iintro #Hpt
    icases Hs with ⟨#H, -⟩
    ihave #Hsh := H $$ Hpt
    inext
    iapply pending_shot γ 1 $$ Hp Hsh

@[rocq_alias cryptis.secret_not_public]
theorem secret_not_isPublic (t : Term) : secret (GF := GF) t -∗ isPublic t -∗ ▷ False :=
  entails_wand (and_elim_r.trans and_elim_r)

@[rocq_alias cryptis.secret_public]
theorem secret_isPublic (t : Term) : secret (GF := GF) t ==∗ isPublic t :=
  entails_wand and_elim_l

@[rocq_alias cryptis.freeze_secret]
theorem freeze_secret (t : Term) : secret (GF := GF) t ==∗ □ (isPublic t ↔ ▷ False) :=
  entails_wand (and_elim_r.trans and_elim_l)

/-! ### Sealing with key records -/

@[rocq_alias cryptis.public_aencIS]
theorem isPublic_aenc_intro (sk : Key .aenc) (N : Namespace) (Φ : Key .aenc → Term → IProp GF)
    (t : Term) :
    keyPred .aenc N Φ -∗ minted sk -∗ minted t -∗ □ Φ sk t -∗ □ (isPublic sk → isPublic t) -∗
      isPublic (sealed (Spec.pkey sk) (Spec.tag (ofNamespace N) t)) := by
  iintro #HΦ #Hmk #Hmt #H #Ho
  iunfold keyPred at HΦ
  iapply isPublic_sealed_intro (F := .aenc) ⟨rfl, rfl⟩ $$ HΦ [] [] Hmt
  · iintro !>
    iexists sk
    isplitl []
    · ipureintro; rfl
    · iexact H
  · iapply (minted_pkey _).mpr $$ Hmk
  · unfold openCond
    rw [Spec.openKey_pkey_aenc]
    iexact Ho

@[rocq_alias cryptis.public_sencIS]
theorem isPublic_senc_intro (k : Key .senc) (N : Namespace) (Φ : Key .senc → Term → IProp GF)
    (t : Term) :
    keyPred .senc N Φ -∗ minted k -∗ minted t -∗ □ Φ k t -∗ □ (isPublic k → isPublic t) -∗
      isPublic (sealed k (Spec.tag (ofNamespace N) t)) := by
  iintro #HΦ #Hmk #Hmt #H #Ho
  iunfold keyPred at HΦ
  iapply isPublic_sealed_intro (F := .senc) ⟨rfl, rfl⟩ $$ HΦ [] Hmk Hmt
  · iintro !>
    iexists k
    isplitl []
    · ipureintro; rfl
    · iexact H
  · unfold openCond
    rw [Spec.openKey_senc]
    iexact Ho

@[rocq_alias cryptis.public_signIS]
theorem isPublic_sign_intro (sk : Key .sign) (N : Namespace) (Φ : Key .sign → Term → IProp GF)
    (t : Term) :
    keyPred .sign N Φ -∗ minted sk -∗ isPublic t -∗ □ Φ sk t -∗
      isPublic (sealed sk (Spec.tag (ofNamespace N) t)) := by
  iintro #HΦ #Hmk #Hpt #H
  iunfold keyPred at HΦ
  iapply isPublic_sealed_intro (F := .sign) ⟨rfl, rfl⟩ $$ HΦ [] Hmk []
  · iintro !>
    iexists sk
    isplitl []
    · ipureintro; rfl
    · iexact H
  · iapply isPublic_minted $$ Hpt
  · unfold openCond
    rw [Spec.openKey_sign]
    iintro !> -
    iexact Hpt

@[rocq_alias cryptis.public_aencE]
theorem isPublic_aenc_elim (sk : Key .aenc) (N : Namespace) (Φ : Key .aenc → Term → IProp GF)
    (t : Term) :
    isPublic (sealed (Spec.pkey sk) (Spec.tag (ofNamespace N) t)) -∗ keyPred .aenc N Φ -∗
      minted t ∧ (isPublic t ∨ □ ▷ Φ sk t ∧ □ (isPublic sk → isPublic t)) := by
  iintro #Hp #HΦ
  isplit
  · icases (minted_sealed _ _).mp $$ [Hp] with ⟨-, #Hm⟩
    · iapply isPublic_minted $$ Hp
    iapply (minted_tag N t).mp $$ Hm
  iunfold keyPred at HΦ
  icases isPublic_sealed_elim (F := .aenc) ⟨rfl, rfl⟩ $$ Hp HΦ with (⟨-, #H⟩ | ⟨#H, #Ho⟩)
  · ileft; iexact H
  iright
  isplit
  · iintro !>
    inext
    icases H with ⟨%k', %e, #H⟩
    rw [Key.toTerm_injective (F := .aenc) e]
    iexact H
  · unfold openCond
    rw [Spec.openKey_pkey_aenc]
    iexact Ho

@[rocq_alias cryptis.public_signE]
theorem isPublic_sign_elim (sk : Key .sign) (N : Namespace) (Φ : Key .sign → Term → IProp GF)
    (t : Term) :
    isPublic (sealed sk (Spec.tag (ofNamespace N) t)) -∗ keyPred .sign N Φ -∗
      isPublic t ∧ (isPublic sk ∨ □ ▷ Φ sk t) := by
  iintro #Hp #HΦ
  ihave #Hmk : minted sk $$ [Hp]
  · icases (minted_sealed _ _).mp $$ [Hp] with ⟨#Hm, -⟩
    · iapply isPublic_minted $$ Hp
    iexact Hm
  iunfold keyPred at HΦ
  icases isPublic_sealed_elim (F := .sign) ⟨rfl, rfl⟩ $$ Hp HΦ with
    (⟨#Hk, #Ht⟩ | ⟨#H, #Ho⟩)
  · isplit
    · iexact Ht
    · ileft; iexact Hk
  unfold openCond
  rw [Spec.openKey_sign]
  isplit
  · iapply Ho
    iapply (isPublic_pkey_sign sk).mpr $$ Hmk
  · iright
    iintro !>
    inext
    icases H with ⟨%k', %e, #H⟩
    rw [Key.toTerm_injective e]
    iexact H

@[rocq_alias cryptis.public_sencE]
theorem isPublic_senc_elim (k : Key .senc) (N : Namespace) (Φ : Key .senc → Term → IProp GF)
    (t : Term) :
    isPublic (sealed k (Spec.tag (ofNamespace N) t)) -∗ keyPred .senc N Φ -∗
      minted t ∧ (isPublic k ∨ □ ▷ Φ k t) ∧ □ (isPublic k → isPublic t) := by
  iintro #Hp #HΦ
  isplit
  · icases (minted_sealed _ _).mp $$ [Hp] with ⟨-, #Hm⟩
    · iapply isPublic_minted $$ Hp
    iapply (minted_tag N t).mp $$ Hm
  iunfold keyPred at HΦ
  icases isPublic_sealed_elim (F := .senc) ⟨rfl, rfl⟩ $$ Hp HΦ with
    (⟨#Hk, #Ht⟩ | ⟨#H, #Ho⟩)
  · isplit
    · ileft; iexact Hk
    · iintro !> -
      iexact Ht
  unfold openCond
  rw [Spec.openKey_senc]
  isplit
  · iright
    iintro !>
    inext
    icases H with ⟨%k', %e, #H⟩
    rw [Key.toTerm_injective e]
    iexact H
  · iexact Ho

omit [PublicGS GF] in
@[rocq_alias cryptis.publicGS_alloc]
theorem publicGS_alloc [PublicGpreS GF] (E : CoPset) :
    ⊢ |={E}=> ∃ _ : PublicGS GF, sealPredToken .aenc ⊤ ∗ sealPredToken .sign ⊤ ∗
      sealPredToken .senc ⊤ ∗ hashPredToken ⊤ := by
  imod gmetaToken_alloc with ⟨%γa, Ha⟩
  imod gmetaToken_alloc with ⟨%γs, Hs⟩
  imod gmetaToken_alloc with ⟨%γe, He⟩
  imod gmetaToken_alloc with ⟨%γh, Hh⟩
  let G : PublicGS GF := ⟨γh, γa, γs, γe⟩
  imodintro
  iexists G
  unfold sealPredToken hashPredToken Functionality.name
  iframe

end Cryptis
