module

public import Mathlib.Data.Finset.Union
public import Cryptis.Core.Term.Algebra

/-! The nonces of terms.

The nonces of a term are those of its pre-term. A product has the nonces of its factors, and an
exponential those of its base and of the factors of its exponent. The smart constructors can only
lose nonces, through cancellation. -/

@[expose] public section
namespace Cryptis

namespace PreTerm

variable {o : TermOpN} {e u : PreTerm} {s : SMS PreTerm}

@[rocq_alias cryptis.nonces_elements_make_sub]
theorem biUnion_nonces_make_subset (X Y : Multiset PreTerm) :
    (SMS.make X Y).elements.toFinset.biUnion nonces ⊆ (X + Y).toFinset.biUnion nonces :=
  Finset.biUnion_subset_biUnion_of_subset_left _ fun _ h =>
    Multiset.mem_toFinset.mpr (SMS.mem_of_mem_make (Multiset.mem_toFinset.mp h))

theorem nonces_subset_of_mem_factors (h : u ∈ e.factors o) : u.nonces ⊆ e.nonces := by
  by_cases hm : e.isProd o
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp hm
    intro a ha
    rw [factors_opN] at h
    rw [mem_nonces_opN]
    rcases Multiset.mem_add.mp (SMS.mem_of_mem_make h) with h | h
    exacts [.inl ⟨u, Multiset.mem_coe.mp h, ha⟩, .inr ⟨u, Multiset.mem_coe.mp h, ha⟩]
  · rw [factors_eq_singleton (by simpa using hm), SMS.mem_singleton] at h
    rw [h]

@[rocq_alias cryptis.nonces_of_pre_term_factors_sub,
  rocq_alias cryptis.nonces_of_pre_term_gfactors_sub]
theorem biUnion_nonces_factors_subset (o : TermOpN) (e : PreTerm) :
    (e.factors o).elements.toFinset.biUnion nonces ⊆ e.nonces :=
  Finset.biUnion_subset.mpr fun _ h =>
    nonces_subset_of_mem_factors (SMS.mem_elements.mp (Multiset.mem_toFinset.mp h))

@[rocq_alias cryptis.nonces_of_pre_term_factors, rocq_alias cryptis.nonces_of_pre_term_gfactors]
theorem nonces_eq_biUnion_factors (o : TermOpN) (h : e.wf) :
    e.nonces = (e.factors o).elements.toFinset.biUnion nonces := by
  refine Finset.Subset.antisymm (fun a ha => ?_) (biUnion_nonces_factors_subset o e)
  by_cases hm : e.isProd o
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp hm
    rw [factors_opN, SMS.make_of_disjoint (wf_opN.mp h).2.1.disjoint]
    simpa [SMS.elements, or_and_right, exists_or] using ha
  · simpa [factors_eq_singleton (by simpa using hm)] using ha

@[rocq_alias cryptis.nonces_bind_factors_sub, rocq_alias cryptis.nonces_bind_gfactors_sub]
theorem biUnion_nonces_bind_factors_subset (o : TermOpN) (s : SMS PreTerm) :
    (s.bind (factors o)).elements.toFinset.biUnion nonces ⊆
      s.elements.toFinset.biUnion nonces := by
  refine Finset.biUnion_subset.mpr fun u hu => ?_
  obtain ⟨v, hv, hu⟩ :=
    SMS.exists_mem_of_mem_bind (SMS.mem_elements.mp (Multiset.mem_toFinset.mp hu))
  exact (nonces_subset_of_mem_factors hu).trans
    (Finset.subset_biUnion_of_mem _ (Multiset.mem_toFinset.mpr (SMS.mem_elements.mpr hv)))

@[rocq_alias cryptis.nonces_of_pre_term_mul_aux, rocq_alias cryptis.nonces_of_pre_term_gmul_aux]
theorem nonces_prodAux (o : TermOpN) (s : SMS PreTerm) :
    (prodAux o s).nonces = s.elements.toFinset.biUnion nonces := by
  cases hs : single (toLists s)
  · ext a
    simp [prodAux_of_single_eq_false hs, toLists, SMS.elements, or_and_right, exists_or]
  · obtain ⟨t, rfl⟩ := single_toLists.mp hs
    simp

@[rocq_alias cryptis.nonces_of_pre_term_mul_sub, rocq_alias cryptis.nonces_of_pre_term_gmul_sub]
theorem nonces_prod_subset (o : TermOpN) (s : SMS PreTerm) :
    (prod o s).nonces ⊆ s.elements.toFinset.biUnion nonces :=
  (nonces_prodAux o _).subset.trans (biUnion_nonces_bind_factors_subset o s)

@[rocq_alias cryptis.nonces_of_pre_term_base_expo]
theorem nonces_eq_base_union_expo (pt : PreTerm) : pt.nonces = pt.base.nonces ∪ pt.expo.nonces := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> simp [base, expo, nonces]

theorem biUnion_nonces_pair (u v : PreTerm) :
    ({u} + {v} : SMS PreTerm).elements.toFinset.biUnion nonces ⊆ u.nonces ∪ v.nonces :=
  Finset.biUnion_subset.mpr fun w hw => by
    rcases SMS.mem_or_mem_of_mem_add (SMS.mem_elements.mp (Multiset.mem_toFinset.mp hw)) with
      h | h <;> rw [SMS.mem_singleton.mp h]
    exacts [Finset.subset_union_left, Finset.subset_union_right]

@[rocq_alias cryptis.nonces_of_pre_term_exp_aux_sub]
theorem nonces_expAux_subset (pt pe : PreTerm) : (expAux pt pe).nonces ⊆ pt.nonces ∪ pe.nonces := by
  have hmul := (nonces_prod_subset .mul _).trans (biUnion_nonces_pair pt.expo pe)
  rw [nonces_eq_base_union_expo pt]
  unfold expAux mkExp
  split_ifs
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · simp only [nonces, Finset.union_subset_iff]
    exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
      hmul.trans (Finset.union_subset_union_left Finset.subset_union_right)⟩

@[rocq_alias cryptis.nonces_of_pre_term_exp_sub]
theorem nonces_exp_subset (pb pe : PreTerm) : (exp pb pe).nonces ⊆ pb.nonces ∪ pe.nonces := by
  refine (nonces_prod_subset .gmul _).trans (Finset.biUnion_subset.mpr fun u hu => ?_)
  obtain ⟨v, hv, rfl⟩ := SMS.exists_of_mem_map (SMS.mem_elements.mp (Multiset.mem_toFinset.mp hu))
  exact (nonces_expAux_subset v pe).trans
    (Finset.union_subset_union_left (nonces_subset_of_mem_factors (o := .gmul) hv))

end PreTerm

namespace Term

variable {o : TermOpN} {t e : Term} {s : SMS Term} {pt : PreTerm}

/-- The nonces that occur in a term. -/
@[rocq_alias cryptis.nonces_of_term]
def nonces (t : Term) : Finset Nonce := t.unfold.nonces

@[simp] theorem nonces_int (n : Int) : (int n).nonces = ∅ := by
  simp [nonces, unfold, PreTerm.nonces, TermOp0.nonces]

@[simp] theorem nonces_nonce (a : Nonce) : (nonce a).nonces = {a} := by
  simp [nonces, unfold, PreTerm.nonces, TermOp0.nonces]

@[simp] theorem nonces_pair (t₁ t₂ : Term) : (pair t₁ t₂).nonces = t₁.nonces ∪ t₂.nonces := by
  simp [nonces, unfold, PreTerm.nonces]

@[simp] theorem nonces_key (kt : KeyType) (t : Term) : (key kt t).nonces = t.nonces := by
  simp [nonces, unfold, PreTerm.nonces]

@[simp] theorem nonces_sealed (k t : Term) : (sealed k t).nonces = k.nonces ∪ t.nonces := by
  simp [nonces, unfold, PreTerm.nonces]

@[simp] theorem nonces_hash (t : Term) : (hash t).nonces = t.nonces := by
  simp [nonces, unfold, PreTerm.nonces]

#rocq_ignore cryptis.nonces_of_termE'
  "Split into the simp lemmas Term.nonces_int, …, Term.nonces_hash"
#rocq_ignore cryptis.nonces_of_termE "A rewriting set; use the Term.nonces_* lemmas directly"
#rocq_ignore cryptis.union_list_map_unfold "Term.biUnion_nonces_eq"

@[simp, rocq_alias cryptis.nonces_of_term_fold]
theorem nonces_fold (h : pt.wf) : (fold pt).nonces = pt.nonces := by
  rw [nonces, unfold_fold_of_wf h]

theorem biUnion_nonces_eq (X : Multiset Term) :
    (X.map unfold).toFinset.biUnion PreTerm.nonces = X.toFinset.biUnion nonces := by
  ext
  simp [nonces]

@[rocq_alias cryptis.nonces_of_term_factors, rocq_alias cryptis.nonces_of_term_gfactors]
theorem nonces_eq_biUnion_factors (o : TermOpN) (t : Term) :
    t.nonces = (t.factors o).elements.toFinset.biUnion nonces := by
  rw [← biUnion_nonces_eq, map_unfold_elements_factors, nonces,
    PreTerm.nonces_eq_biUnion_factors o (wf_unfold t)]

@[rocq_alias cryptis.nonces_of_term_base_exps]
theorem nonces_eq_base_union_exps (t : Term) :
    t.nonces = t.base.nonces ∪ t.exps.elements.toFinset.biUnion nonces := by
  rw [exps, ← nonces_eq_biUnion_factors, nonces, nonces, nonces, unfold_base, unfold_expo]
  exact PreTerm.nonces_eq_base_union_expo _

@[simp, rocq_alias cryptis.nonces_of_term_TInv, rocq_alias cryptis.nonces_of_term_TGInv]
theorem nonces_prod_neg_singleton (o : TermOpN) (t : Term) :
    (prod o (-{t})).nonces = t.nonces := by
  rw [nonces_eq_biUnion_factors o, factors_prod, SMS.bind_neg, SMS.bind_singleton,
    SMS.elements_neg, ← nonces_eq_biUnion_factors]

@[rocq_alias cryptis.nonces_of_term_TMul_subseteq, rocq_alias cryptis.nonces_of_term_TGMul_subseteq]
theorem nonces_prod_subset (o : TermOpN) (s : SMS Term) :
    (prod o s).nonces ⊆ s.elements.toFinset.biUnion nonces := by
  rw [nonces, unfold_prod, ← biUnion_nonces_eq, ← SMS.elements_map_of_injective unfold_injective]
  exact PreTerm.nonces_prod_subset o _

@[rocq_alias cryptis.nonces_of_term_TExp_subseteq]
theorem nonces_exp_subset (t e : Term) : (t.exp e).nonces ⊆ t.nonces ∪ e.nonces := by
  rw [nonces, unfold_exp]
  exact PreTerm.nonces_exp_subset _ _

@[rocq_alias cryptis.nonces_of_term_TMul, rocq_alias cryptis.nonces_of_term_TGMul]
theorem nonces_prod (hs : ∀ u ∈ s, u.isProd o = false) :
    (prod o s).nonces = s.elements.toFinset.biUnion nonces := by
  rw [nonces_eq_biUnion_factors o, factors_prod_of_forall hs]

@[rocq_alias cryptis.nonces_of_term_TExp]
theorem nonces_exp (hx : t.isExp = false) (hg : t.isProd .gmul = false) (e : Term) :
    (t.exp e).nonces = t.nonces ∪ (e.factors .mul).elements.toFinset.biUnion nonces := by
  rw [nonces_eq_base_union_exps, base_exp hg, base_eq_self hx, exps_exp hx hg]

@[rocq_alias cryptis.nonces_of_term_TExp_TMul]
theorem nonces_exp_prod (hx : t.isExp = false) (hg : t.isProd .gmul = false)
    (hs : ∀ u ∈ s, u.isProd .mul = false) :
    (t.exp (prod .mul s)).nonces = t.nonces ∪ s.elements.toFinset.biUnion nonces := by
  rw [nonces_exp hx hg, factors_prod_of_forall hs]

end Term
end Cryptis
