module

public import Cryptis.Core.Term
public import Cryptis.Lib.BaseLogic
public import Cryptis.Upstream.Iris.BigSepMultiset
public import Iris.HeapLang.PrimitiveLaws

/-! Minted terms.

A term is minted when all of its nonces have been created by the program. A nonce is minted once
its heap location carries the meta data `nroot.@"minted"`, which the spec of nonce creation sets.
Public terms are minted, and mintedness is persistent: a minted term stays minted. Mintedness
only depends on the nonces of a term, and the lemmas below reduce it to the parts of each kind of
term. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.HeapLang Term Term.ProdGroup BigSepMultiset BigSepFinset

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

/-- All the nonces of `t` have been minted. -/
@[rocq_alias cryptis.minted]
def minted (t : Term) : IProp GF :=
  iprop([∗finset] a ∈ t.nonces, metaInfo a.loc (nroot.@"minted") ())

@[rocq_alias cryptis.Persistent_minted]
instance minted_persistent (t : Term) : Persistent (minted (GF := GF) t) := by
  unfold minted; infer_instance

@[rocq_alias cryptis.Timeless_minted]
instance minted_timeless (t : Term) : Timeless (minted (GF := GF) t) := by
  unfold minted; infer_instance

variable {o : TermOpN} {t t₁ t₂ k : Term} {s : SMS Term}

theorem minted_eq_forall (t : Term) :
    minted (GF := GF) t ⊣⊢ ∀ a, ⌜a ∈ t.nonces⌝ → metaInfo a.loc (nroot.@"minted") () :=
  bigSepFinset_forall

/-- `minted t` only depends on the nonces of `t`. -/
theorem minted_mono (h : t₁.nonces ⊆ t₂.nonces) : minted (GF := GF) t₂ ⊢ minted t₁ := by
  rw [(minted_eq_forall t₂).to_eq, (minted_eq_forall t₁).to_eq]
  iintro #H %a %ha
  iapply H $$ %a %(h ha)

/-- A term is minted when the terms that cover its nonces are. -/
theorem minted_iff_forall {p : Term → Prop} (h : ∀ a, a ∈ t.nonces ↔ ∃ u, p u ∧ a ∈ u.nonces) :
    minted (GF := GF) t ⊣⊢ ∀ u, ⌜p u⌝ → minted u := by
  simp only [(minted_eq_forall _).to_eq]
  constructor
  · iintro #H %u %hu %a %ha
    iapply H $$ %a %((h a).mpr ⟨u, hu, ha⟩)
  · iintro #H %a %ha
    obtain ⟨u, hu, hau⟩ := (h a).mp ha
    iapply H $$ %u %hu %a %hau

theorem minted_iff_bigSep (h : t.nonces = s.elements.toFinset.biUnion nonces) :
    minted (GF := GF) t ⊣⊢ [∗multiset] u ∈ s.elements, minted u :=
  (minted_iff_forall fun a => by simp [h]).trans bigSepMultiset_forall.symm

@[rocq_alias cryptis.subterm_minted]
theorem Term.Subterm.minted (h : t₁.Subterm t₂) :
    Cryptis.minted (GF := GF) t₂ -∗ Cryptis.minted t₁ :=
  entails_wand (minted_mono h.nonces_subset)

@[rocq_alias cryptis.minted_TInt]
theorem minted_int (n : Int) : minted (GF := GF) (int n) ⊣⊢ True := by
  rw [minted, nonces_int]
  exact bigSepFinset_empty.trans true_emp.symm

theorem minted_iff_and (h : t.nonces = t₁.nonces ∪ t₂.nonces) :
    minted (GF := GF) t ⊣⊢ minted t₁ ∧ minted t₂ :=
  (minted_iff_forall (p := fun u => u = t₁ ∨ u = t₂) fun a => by simp [h]).trans <|
    (forall_pure_or_imp _ _ _).trans (and_congr (forall_pure_eq_imp _ _) (forall_pure_eq_imp _ _))

@[rocq_alias cryptis.minted_TPair]
theorem minted_pair (t₁ t₂ : Term) : minted (GF := GF) (pair t₁ t₂) ⊣⊢ minted t₁ ∧ minted t₂ :=
  minted_iff_and (nonces_pair t₁ t₂)

@[rocq_alias cryptis.minted_TNonce]
theorem minted_nonce (a : Nonce) :
    minted (GF := GF) (nonce a) ⊣⊢ metaInfo a.loc (nroot.@"minted") () := by
  rw [minted, nonces_nonce]
  exact bigSepFinset_singleton a

@[rocq_alias cryptis.minted_TKey]
theorem minted_key (kt : KeyType) (t : Term) : minted (GF := GF) (key kt t) ⊣⊢ minted t := by
  simp [minted]

@[rocq_alias cryptis.minted_TSeal]
theorem minted_sealed (k t : Term) : minted (GF := GF) (sealed k t) ⊣⊢ minted k ∧ minted t :=
  minted_iff_and (nonces_sealed k t)

@[rocq_alias cryptis.minted_THash]
theorem minted_hash (t : Term) : minted (GF := GF) (hash t) ⊣⊢ minted t := by
  simp [minted]

@[rocq_alias cryptis.minted_TInv, rocq_alias cryptis.minted_TGInv]
theorem minted_coe_inv (a : ProdGroup o) : minted (GF := GF) ↑a⁻¹ ⊣⊢ minted ↑a := by
  simp [minted]

@[rocq_alias cryptis.minted_TMul, rocq_alias cryptis.minted_TGMul]
theorem minted_prod (hs : ∀ u ∈ s, u.isProd o = false) :
    minted (GF := GF) (prod o s) ⊣⊢ [∗multiset] u ∈ s.elements, minted u :=
  minted_iff_bigSep (nonces_prod hs)

@[rocq_alias cryptis.minted_factors, rocq_alias cryptis.minted_gfactors]
theorem minted_factors (o : TermOpN) (t : Term) :
    minted (GF := GF) t ⊣⊢ [∗multiset] u ∈ (t.factors o).elements, minted u :=
  minted_iff_bigSep (nonces_eq_biUnion_factors o t)

@[rocq_alias cryptis.minted_base_exps]
theorem minted_base_exps (t : Term) :
    minted (GF := GF) t ⊣⊢ minted t.base ∧ [∗multiset] u ∈ t.exps.elements, minted u :=
  (minted_iff_forall (p := fun u => u = t.base ∨ u ∈ t.exps.elements) fun a => by
    simp [nonces_eq_base_union_exps t]).trans <|
    (forall_pure_or_imp _ _ _).trans (and_congr (forall_pure_eq_imp _ _) bigSepMultiset_forall.symm)

@[rocq_alias cryptis.all_minted_TMul, rocq_alias cryptis.all_minted_TGMul]
theorem minted_prod_intro (o : TermOpN) (s : SMS Term) :
    ([∗multiset] u ∈ s.elements, minted u) ⊢ minted (GF := GF) (prod o s) := by
  simp only [bigSepMultiset_forall.to_eq, (minted_eq_forall _).to_eq]
  iintro #H %a %ha
  obtain ⟨u, hu, hau⟩ : ∃ u ∈ s, a ∈ u.nonces := by
    simpa [SMS.mem_elements] using nonces_prod_subset o s ha
  iapply H $$ %u %hu %a %hau

@[rocq_alias cryptis.all_minted_TMul2, rocq_alias cryptis.all_minted_TGMul2]
theorem minted_coe_mul_intro (a b : ProdGroup o) :
    minted ↑a ∧ minted ↑b ⊢ minted (GF := GF) ↑(a * b) := by
  refine .trans ?_ (bigSepMultiset_forall.2.trans (minted_prod_intro o _))
  iintro #H %u %hu
  rcases SMS.mem_or_mem_of_mem_add hu with h | h <;> rw [SMS.mem_singleton.mp h]
  · icases H with ⟨H, -⟩; iexact H
  · icases H with ⟨-, H⟩; iexact H

@[rocq_alias cryptis.minted_TExp]
theorem minted_exp (hx : t₁.isExp = false) (hg : t₁.isProd .gmul = false) (t₂ : Term) :
    minted (GF := GF) (t₁.exp t₂) ⊣⊢ minted t₁ ∧ minted t₂ :=
  (minted_iff_forall (p := fun u => u = t₁ ∨ u ∈ (t₂.factors .mul).elements) fun a => by
    simp [nonces_exp hx hg]).trans <|
    (forall_pure_or_imp _ _ _).trans <| and_congr (forall_pure_eq_imp _ _) <|
      bigSepMultiset_forall.symm.trans (minted_factors .mul t₂).symm

theorem minted_exp_intro (t₁ t₂ : Term) :
    minted t₁ ∧ minted t₂ ⊢ minted (GF := GF) (t₁.exp t₂) := by
  simp only [(minted_eq_forall _).to_eq]
  iintro #H %a %ha
  rcases Finset.mem_union.mp (nonces_exp_subset t₁ t₂ ha) with h | h
  · icases H with ⟨H, -⟩; iapply H $$ %a %h
  · icases H with ⟨-, H⟩; iapply H $$ %a %h

@[rocq_alias cryptis.all_minted_TExp]
theorem minted_coe_smul_intro (a : E) (g : G) :
    minted ↑g ∧ minted ↑a ⊢ minted (GF := GF) ↑(a • g) :=
  minted_exp_intro ↑g ↑a

@[rocq_alias cryptis.minted_nonces_of_term]
theorem minted_iff_nonces (t : Term) :
    minted (GF := GF) t ⊣⊢ [∗finset] a ∈ t.nonces, minted (nonce a) :=
  bigSepFinset_congr fun a _ => (minted_nonce a).symm

@[rocq_alias cryptis.minted_of_list]
theorem minted_ofList (ts : List Term) :
    minted (GF := GF) (Spec.ofList ts) ⊣⊢ [∗list] u ∈ ts, minted u := by
  induction ts with
  | nil => exact (minted_int 0).trans true_emp
  | cons t ts ih => exact (minted_pair _ _).trans <| (and_congr .rfl ih).trans persistent_and_sep

/-! The next three equations rewrite the mintedness of a list literal into a conjunction, with
`simp only` or `rw`. -/

theorem minted_ofList_nil : minted (GF := GF) (Spec.ofList []) = iprop(True) :=
  (minted_int 0).to_eq

theorem minted_ofList_singleton (t : Term) : minted (GF := GF) (Spec.ofList [t]) = minted t :=
  ((minted_pair _ _).trans <| (and_congr .rfl (minted_int 0)).trans and_true).to_eq

theorem minted_ofList_cons_cons (t t' : Term) (ts : List Term) :
    minted (GF := GF) (Spec.ofList (t :: t' :: ts)) =
      iprop(minted t ∧ minted (Spec.ofList (t' :: ts))) :=
  (minted_pair _ _).to_eq

@[rocq_alias cryptis.minted_to_list]
theorem minted_of_toList_eq_some {ts : List Term} (h : Spec.toList t = some ts) :
    minted (GF := GF) t -∗ [∗list] u ∈ ts, minted u := by
  rw [Spec.toList_eq_some_iff.mp h]
  exact entails_wand (minted_ofList ts).1

@[rocq_alias cryptis.minted_Tag]
theorem minted_ofNamespace (N : Namespace) : ⊢ minted (GF := GF) (ofNamespace N) :=
  true_intro.trans (minted_int _).mpr

@[rocq_alias cryptis.minted_tag]
theorem minted_tag (N : Namespace) (t : Term) :
    minted (GF := GF) (Spec.tag (ofNamespace N) t) ⊣⊢ minted t := by
  simp [minted, Spec.tag, ofNamespace]

@[rocq_alias cryptis.minted_pkey]
theorem minted_pkey (k : Term) : minted (GF := GF) (Spec.pkey k) ⊣⊢ minted k := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp [Spec.pkey, minted]

@[rocq_alias cryptis.minted_aenc, rocq_alias cryptis.minted_senc,
  rocq_alias cryptis.minted_sign]
theorem minted_coe_key {F : Functionality} (k : Key F) : minted (GF := GF) k ⊣⊢ minted k.seed :=
  minted_key _ _

end Cryptis
