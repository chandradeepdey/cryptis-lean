module

public import Mathlib.Algebra.Order.Group.Nat
public import Cryptis.Core.Term.Algebra

/-! The size of terms, and well-founded recursion on it.

The size of a term is the number of operators in its pre-term. The base of an exponential, the
factors of its exponent and the factors of a product are smaller than the whole, so recursion on
terms can go under exponentials and products. `tsizeRec` is recursion on the size, and the
`tsize_*_lt` lemmas are its termination arguments. -/

@[expose] public section
namespace Cryptis
namespace Term

variable {o : TermOpN} {t t' t₁ t₂ u e a f : Term} {s : SMS Term}

open ProdGroup

/-- The number of constructors in the pre-term of a term. -/
@[rocq_alias cryptis.tsize]
def tsize (t : Term) : Nat := t.unfold.tsize

@[rocq_alias cryptis.tsize_gt0]
theorem tsize_pos (t : Term) : 0 < t.tsize := by
  rw [tsize]
  cases t.unfold <;> simp [PreTerm.tsize]

@[simp] theorem tsize_int (n : Int) : (int n).tsize = 1 := by simp [tsize, unfold, PreTerm.tsize]

@[simp] theorem tsize_nonce (a : Nonce) : (nonce a).tsize = 1 := by
  simp [tsize, unfold, PreTerm.tsize]

@[simp] theorem tsize_pair (t₁ t₂ : Term) : (pair t₁ t₂).tsize = t₁.tsize + t₂.tsize + 1 := by
  simp [tsize, unfold, PreTerm.tsize]

@[simp] theorem tsize_key (kt : KeyType) (t : Term) : (key kt t).tsize = t.tsize + 1 := by
  simp [tsize, unfold, PreTerm.tsize]

@[simp] theorem tsize_sealed (k t : Term) : (sealed k t).tsize = k.tsize + t.tsize + 1 := by
  simp [tsize, unfold, PreTerm.tsize]

@[simp] theorem tsize_hash (t : Term) : (hash t).tsize = t.tsize + 1 := by
  simp [tsize, unfold, PreTerm.tsize]

#rocq_ignore cryptis.tsize_eq "Split into the simp lemmas Term.tsize_int, …, Term.tsize_hash"
#rocq_ignore cryptis.sum_list_with_fold "Term.map_tsize"

theorem map_tsize (X : Multiset Term) : X.map tsize = (X.map unfold).map PreTerm.tsize := by
  rw [Multiset.map_map]
  rfl

/-! ### Products -/

@[rocq_alias cryptis.tsize_factorsE, rocq_alias cryptis.tsize_gfactorsE]
theorem tsize_eq_sum_factors (o : TermOpN) (t : Term) :
    t.tsize = (if t.isProd o then 1 else 0) + ((t.factors o).elements.map tsize).sum := by
  cases h : t.isProd o
  · simp [factors_eq_singleton h]
  · obtain ⟨ps, ns, hpt⟩ := PreTerm.isProd_iff.mp (by rwa [isProd_unfold])
    have hw := PreTerm.wf_opN.mp (hpt ▸ wf_unfold t)
    rw [map_tsize, map_unfold_elements_factors, tsize, hpt, PreTerm.factors_opN,
      SMS.make_of_disjoint hw.2.1.disjoint]
    simp [SMS.elements, PreTerm.tsize]
    omega

@[rocq_alias cryptis.tsize_factors_le, rocq_alias cryptis.tsize_gfactors_le]
theorem tsize_le_of_mem_factors (h : t ∈ t'.factors o) : t.tsize ≤ t'.tsize := by
  rw [tsize_eq_sum_factors o t']
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem tsize (SMS.mem_elements.mpr h))
  omega

@[rocq_alias cryptis.tsize_factors_lt, rocq_alias cryptis.tsize_gfactors_lt]
theorem tsize_lt_of_mem_factors (hm : t.isProd o) (h : t' ∈ t.factors o) :
    t'.tsize < t.tsize := by
  rw [tsize_eq_sum_factors o t, hm]
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem tsize (SMS.mem_elements.mpr h))
  simp only [ite_true]
  omega

@[rocq_alias cryptis.tsize_TInv, rocq_alias cryptis.tsize_TGInv]
theorem tsize_prod_neg_singleton (h : t.isProd o = false) :
    (prod o (-{t})).tsize = t.tsize + 1 := by
  rw [tsize_eq_sum_factors o (prod o (-{t})), isProd_prod_neg_singleton h, factors_prod,
    SMS.bind_neg, SMS.bind_singleton, SMS.elements_neg, factors_eq_singleton h]
  simp [add_comm]

@[rocq_alias cryptis.tsize_TMul]
theorem tsize_prod (hs : ∀ u ∈ s, u.isProd o = false) :
    (prod o s).tsize = (if (prod o s).isProd o then 1 else 0) + (s.elements.map tsize).sum := by
  rw [tsize_eq_sum_factors o, factors_prod_of_forall hs]

/-! ### Exponentials -/

/-- The base must not be a group product: exponentiation distributes over those. -/
@[rocq_alias cryptis.tsize_TExp]
theorem tsize_exp (hx : t₁.isExp = false) (hg : t₁.isProd .gmul = false)
    (he : t₂ ≠ prod .mul 0) : (t₁.exp t₂).tsize = t₁.tsize + t₂.tsize + 1 := by
  have hx' : t₁.unfold.isExp = false := by rwa [isExp_unfold]
  have he' : t₂.unfold ≠ .opN .mul [] [] := by rwa [← unfold_prod_zero, ne_eq, unfold_inj]
  rw [tsize, unfold_exp, PreTerm.exp_eq_expAux (wf_unfold _) (wf_unfold _)
      (by rwa [← isProd_unfold] at hg),
    PreTerm.expAux, PreTerm.base_eq_self hx', PreTerm.expo_eq_unit hx', PreTerm.prod_unit_left,
    PreTerm.prod_singleton (wf_unfold _), PreTerm.mkExp]
  simp [he', PreTerm.tsize, tsize]

/-- A scalar product in a base is an atom, unlike a group product, which every exponent
distributes over. -/
@[rocq_alias cryptis.tsize_TExp_TMul2]
theorem tsize_exp_prod_pair (h₁ : t₁.isProd .mul = false) (h₂ : t₂.isProd .mul = false)
    (he : e ≠ prod .mul 0) :
    ((prod .mul ({t₁} + {t₂})).exp e).tsize = (prod .mul ({t₁} + {t₂})).tsize + e.tsize + 1 :=
  have hm := isProd_prod_pair h₁ h₂
  tsize_exp (isExp_eq_false_of_isProd hm) (isProd_gmul_eq_false_of_isProd_mul hm) he

#rocq_ignore cryptis.tsizeE
  "A rewriting set; use Term.tsize_prod_neg_singleton, Term.tsize_exp, … directly"

/-! ### Growing and shrinking exponents -/

@[rocq_alias cryptis.elements_factors_TMul2]
theorem elements_factors_mul (h : t.isProd .mul = false) (ht : t ∉ (e.factors .mul).negPart) :
    ((prod .mul ({e} + {t})).factors .mul).elements = t ::ₘ (e.factors .mul).elements := by
  rw [← coe_mul (E.ofTerm e), factors_coe_mul, coe_ofTerm, coe_ofTerm, factors_eq_singleton h,
    SMS.elements_add disjoint_bot_right (by simpa [Multiset.disjoint_singleton] using ht)]
  simp [add_comm]

@[rocq_alias cryptis.elements_factors_TMul2_inv]
theorem elements_factors_mul_inv (h : t.isProd .mul = false) (ht : t ∉ (e.factors .mul).posPart) :
    ((prod .mul ({e} + {prod .mul (-{t})})).factors .mul).elements =
      t ::ₘ (e.factors .mul).elements := by
  rw [← coe_inv (E.ofTerm t), ← coe_mul (E.ofTerm e), factors_coe_mul, factors_coe_inv, coe_ofTerm,
    coe_ofTerm, factors_eq_singleton h,
    SMS.elements_add (by simpa [Multiset.disjoint_singleton] using ht) disjoint_bot_right]
  simp [add_comm]

@[rocq_alias cryptis.elements_factors_nil]
theorem eq_prod_zero_of_elements_factors (h : (e.factors o).elements = 0) : e = prod o 0 :=
  factors_eq_zero_iff.mp (SMS.eq_zero_of_elements_eq_zero h)

@[rocq_alias cryptis.tsize_factors_cons_lt]
theorem tsize_lt_of_elements_factors_eq_cons
    (h : (u.factors .mul).elements = t ::ₘ (e.factors .mul).elements) :
    t.tsize ≤ u.tsize ∧ (e ≠ prod .mul 0 → e.tsize < u.tsize) := by
  refine ⟨tsize_le_of_mem_factors (SMS.mem_elements.mp (h ▸ Multiset.mem_cons_self _ _)),
    fun he => ?_⟩
  have hu := tsize_eq_sum_factors .mul u
  have he' := tsize_eq_sum_factors .mul e
  have := tsize_pos t
  rw [h, Multiset.map_cons, Multiset.sum_cons] at hu
  cases hm : u.isProd .mul
  · rw [factors_eq_singleton hm, SMS.elements_singleton] at h
    have := congrArg Multiset.card h
    simp only [Multiset.card_singleton, Multiset.card_cons, right_eq_add,
      Multiset.card_eq_zero] at this
    exact absurd (eq_prod_zero_of_elements_factors this) he
  · simp only [hm, ite_true] at hu
    split_ifs at he' <;> omega

/-- The base must not be a group product, which every exponent distributes over. -/
@[rocq_alias cryptis.tsize_lt_TExp_gen]
theorem tsize_lt_exp_of_elements_exps (h₁ : t₁.isProd .gmul = false)
    (h : (t₁.exp e).exps.elements = a ::ₘ t₁.exps.elements) :
    t₁.tsize < (t₁.exp e).tsize ∧ a.tsize + 1 < (t₁.exp e).tsize := by
  obtain ⟨hle, hlt⟩ := tsize_lt_of_elements_factors_eq_cons h
  have hx : (t₁.exp e).expo ≠ prod .mul 0 := fun he => by simp [exps, he] at h
  have hb := isExp_base t₁
  have hg : t₁.base.isProd .gmul = false := by rwa [isProd_base]
  have hsize : (t₁.exp e).tsize = t₁.base.tsize + (t₁.exp e).expo.tsize + 1 := by
    conv_lhs => rw [← exp_base_expo (t₁.exp e), base_exp h₁]
    exact tsize_exp hb hg hx
  have := tsize_pos t₁.base
  rw [hsize]
  refine ⟨?_, by omega⟩
  by_cases he : t₁.expo = prod .mul 0
  · conv_lhs => rw [← exp_base_expo t₁, he, exp_unit]
    omega
  · conv_lhs => rw [← exp_base_expo t₁, tsize_exp hb hg he]
    have := hlt he
    omega

@[rocq_alias cryptis.tsize_lt_TExp]
theorem tsize_lt_exp (h₁ : t₁.isProd .gmul = false) (h₂ : t₂.isProd .mul = false)
    (h : t₂ ∉ t₁.exps.negPart) :
    t₁.tsize < (t₁.exp t₂).tsize ∧ t₂.tsize < (t₁.exp t₂).tsize := by
  have := tsize_lt_exp_of_elements_exps h₁ (e := t₂) (a := t₂)
    (by rw [exps, expo_exp h₁]; exact elements_factors_mul h₂ h)
  exact ⟨this.1, by omega⟩

@[rocq_alias cryptis.tsize_lt_TExp_inv]
theorem tsize_lt_exp_inv (h₁ : t₁.isProd .gmul = false) (h₂ : t₂.isProd .mul = false)
    (h : t₂ ∉ t₁.exps.posPart) :
    t₁.tsize < (t₁.exp (prod .mul (-{t₂}))).tsize ∧
      (prod .mul (-{t₂})).tsize < (t₁.exp (prod .mul (-{t₂}))).tsize := by
  have := tsize_lt_exp_of_elements_exps h₁ (e := prod .mul (-{t₂})) (a := t₂)
    (by rw [exps, expo_exp h₁]; exact elements_factors_mul_inv h₂ h)
  rw [tsize_prod_neg_singleton h₂]
  exact this

/-- Removing a positive exponent factor shrinks an exponential. -/
@[rocq_alias cryptis.tsize_TExp_pos]
theorem tsize_lt_of_mem_posPart_exps (h : f ∈ t.exps.posPart) :
    f.tsize < t.tsize ∧ (t.exp (prod .mul (-{f}))).tsize < t.tsize := by
  obtain ⟨t, rfl⟩ : ∃ t' : Term, t = t'.exp f := ⟨_, (exp_inv_exp t f).symm⟩
  obtain ⟨hf, hg, hnn⟩ := count_expo_exp_self_pos_iff.mp (count_pos_iff.mpr h)
  have := tsize_lt_exp hg hf fun h' => (count_neg_iff.mpr h').not_ge hnn
  rw [exp_exp_inv]
  exact ⟨this.2, this.1⟩

/-- Removing a negative exponent factor shrinks an exponential. -/
@[rocq_alias cryptis.tsize_TExp_neg]
theorem tsize_lt_of_mem_negPart_exps (h : f ∈ t.exps.negPart) :
    (prod .mul (-{f})).tsize < t.tsize ∧ (t.exp f).tsize < t.tsize := by
  obtain ⟨t, rfl⟩ : ∃ t' : Term, t = t'.exp (prod .mul (-{f})) := ⟨_, (exp_exp_inv t f).symm⟩
  have hf := isProd_of_mem_factors (SMS.mem_of_mem_negPart h)
  have hg : t.isProd .gmul = false := by
    rw [← isProd_exp t (prod .mul (-{f}))]
    exact isProd_eq_false_of_isExp _ (isExp_of_mem_exps (SMS.mem_of_mem_negPart h))
  have hneg := count_neg_iff.mpr h
  rw [count_expo_exp hg, count_prod_neg_singleton, count_self_of_isProd_eq_false hf] at hneg
  have := tsize_lt_exp_inv hg hf fun h' => by have := count_pos_iff.mpr h'; omega
  rw [exp_inv_exp]
  exact ⟨this.2, this.1⟩

@[rocq_alias cryptis.tsize_satoms]
theorem tsize_lt_of_mem_satoms {f : E} (h : f ∈ satoms t.exps) :
    (f : Term).tsize < t.tsize ∧ (t.exp ↑f⁻¹).tsize < t.tsize := by
  rcases Multiset.mem_add.mp h with h | h <;> obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp h
  · exact tsize_lt_of_mem_posPart_exps hn
  · simpa using tsize_lt_of_mem_negPart_exps hn

@[rocq_alias cryptis.tsize_base_lt]
theorem tsize_base_lt (h : t.isExp) : t.base.tsize < t.tsize := by
  rw [← isExp_unfold] at h
  obtain ⟨b, e, he⟩ := PreTerm.isExp_iff.mp h
  rw [tsize, unfold_base, tsize, he]
  simp [PreTerm.base, PreTerm.tsize]
  omega

@[rocq_alias cryptis.tsize_expo_lt]
theorem tsize_expo_lt (h : t.isExp) : t.expo.tsize < t.tsize := by
  rw [← isExp_unfold] at h
  obtain ⟨b, e, he⟩ := PreTerm.isExp_iff.mp h
  rw [tsize, unfold_expo, tsize, he]
  simp [PreTerm.expo, PreTerm.tsize]
  omega

@[rocq_alias cryptis.tsize_exps_lt]
theorem tsize_lt_of_mem_exps (h : t' ∈ t.exps) : t'.tsize < t.tsize :=
  (tsize_le_of_mem_factors h).trans_lt (tsize_expo_lt (isExp_of_mem_exps h))

@[rocq_alias cryptis.count_expo_gfactors_big]
theorem count_expo_eq_zero_of_tsize_le {T x : Term} (hu : u ∈ T.factors .gmul)
    (hle : T.tsize ≤ x.tsize) : count .mul x u.expo = 0 := by
  by_contra hne
  have := tsize_lt_of_mem_exps (count_ne_zero_iff.mp hne)
  have := tsize_le_of_mem_factors hu
  omega

/-! ### Recursion on the size -/

/-- Well-founded recursion on the size of terms. -/
@[elab_as_elim, rocq_alias cryptis.term_lt_rect]
def tsizeRec {motive : Term → Sort _} (h : ∀ t, (∀ t', t'.tsize < t.tsize → motive t') → motive t)
    (t : Term) : motive t :=
  h t fun t' _ => tsizeRec h t'
termination_by t.tsize

@[elab_as_elim, rocq_alias cryptis.term_lt_ind]
theorem tsize_induction {motive : Term → Prop}
    (h : ∀ t, (∀ t', t'.tsize < t.tsize → motive t') → motive t) (t : Term) : motive t :=
  tsizeRec h t

end Term
end Cryptis
