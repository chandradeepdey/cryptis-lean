module

public import Cryptis.Core.Term.TSize
public import Cryptis.Core.Term.Nonces

/-! Subterms.

A term occurs in another when it is reached by taking apart free constructors, exponentials and
products. An exponential is taken apart into its base and the factors of its exponent, and a
product into its factors. `Subterm t₁ t₂` is this relation, and `subterms t` is the finite set of
subterms of `t`, computed on its pre-term; `subterm_iff_mem_subterms` relates the two. A nonce
occurs in a term exactly when it is one of its nonces (`subterm_nonce_iff`). -/

@[expose] public section
namespace Cryptis

/-- `Subterm t₁ t₂`: `t₁` occurs in `t₂`. -/
@[rocq_alias cryptis.subterm]
inductive Term.Subterm (t : Term) : Term → Prop where
  | refl : Subterm t t
  | pairLeft {t₁ t₂ : Term} : Subterm t t₁ → Subterm t (.pair t₁ t₂)
  | pairRight {t₁ t₂ : Term} : Subterm t t₂ → Subterm t (.pair t₁ t₂)
  | key {kt : KeyType} {t' : Term} : Subterm t t' → Subterm t (.key kt t')
  | sealedLeft {k t' : Term} : Subterm t k → Subterm t (.sealed k t')
  | sealedRight {k t' : Term} : Subterm t t' → Subterm t (.sealed k t')
  | hash {t' : Term} : Subterm t t' → Subterm t (.hash t')
  | expBase {b e : Term} : b.isExp = false → b.isProd .gmul = false → Subterm t b →
      Subterm t (b.exp e)
  | expFactor {b u e : Term} : b.isExp = false → b.isProd .gmul = false → Subterm t u →
      u ∈ e.factors .mul → Subterm t (b.exp e)
  | prod {o : TermOpN} {u : Term} {s : SMS Term} : (∀ x ∈ s, x.isProd o = false) →
      Subterm t u → u ∈ s → Subterm t (.prod o s)

attribute [rocq_alias cryptis.STRefl] Term.Subterm.refl
attribute [rocq_alias cryptis.STPair1] Term.Subterm.pairLeft
attribute [rocq_alias cryptis.STPair2] Term.Subterm.pairRight
attribute [rocq_alias cryptis.STKey] Term.Subterm.key
attribute [rocq_alias cryptis.STSeal1] Term.Subterm.sealedLeft
attribute [rocq_alias cryptis.STSeal2] Term.Subterm.sealedRight
attribute [rocq_alias cryptis.STHash] Term.Subterm.hash
attribute [rocq_alias cryptis.STExp1] Term.Subterm.expBase
attribute [rocq_alias cryptis.STExp2] Term.Subterm.expFactor
attribute [rocq_alias cryptis.STMul, rocq_alias cryptis.STGMul] Term.Subterm.prod

namespace PreTerm

mutual

/-- The strict subterms of a pre-term, as terms. The exponent of an exponential contributes the
subterms of its factors. -/
@[rocq_alias cryptis.ssubterms_pre_def]
def ssubterms : PreTerm → Finset Term
  | op0 _ => ∅
  | op1 _ t => insert (Term.fold t) t.ssubterms
  | ptExp b (ptMul ps ns) =>
    insert (Term.fold b) b.ssubterms ∪ (ssubtermsList ps ∪ ssubtermsList ns)
  | op2 _ t₁ t₂ => insert (Term.fold t₁) t₁.ssubterms ∪ insert (Term.fold t₂) t₂.ssubterms
  | opN _ ps ns => ssubtermsList ps ∪ ssubtermsList ns

/-- The subterms of a list of pre-terms. -/
def ssubtermsList : List PreTerm → Finset Term
  | [] => ∅
  | t :: ts => insert (Term.fold t) t.ssubterms ∪ ssubtermsList ts

end

end PreTerm

namespace Term

variable {o : TermOpN} {t t₁ t₂ t₃ u b e : Term} {s : SMS Term} {pt : PreTerm}

/-! ### The subterm relation -/

namespace Subterm

attribute [refl] refl

@[trans]
theorem trans (h₁ : Subterm t₁ t₂) (h₂ : Subterm t₂ t₃) : Subterm t₁ t₃ := by
  induction h₂ with
  | refl => exact h₁
  | pairLeft _ ih => exact pairLeft ih
  | pairRight _ ih => exact pairRight ih
  | key _ ih => exact key ih
  | sealedLeft _ ih => exact sealedLeft ih
  | sealedRight _ ih => exact sealedRight ih
  | hash _ ih => exact hash ih
  | expBase hx hg _ ih => exact expBase hx hg ih
  | expFactor hx hg _ hu ih => exact expFactor hx hg ih hu
  | prod hs _ hu ih => exact prod hs ih hu

@[rocq_alias cryptis.subterm_refl, rocq_alias cryptis.subterm_trans]
instance : IsPreorder Term Subterm where
  refl _ := refl
  trans _ _ _ := trans

@[rocq_alias cryptis.subterm_factors, rocq_alias cryptis.subterm_gfactors]
theorem of_mem_factors (hu : u ∈ b.factors o) (h : Subterm t u) : Subterm t b := by
  rw [← prod_factors o b]
  exact prod (fun _ hx => isProd_of_mem_factors hx) h hu

end Subterm

/-! ### The set of subterms -/

/-- The subterms of a normal pre-term, as terms. -/
@[rocq_alias cryptis.subterms_pre]
def subtermsPre (pt : PreTerm) : Finset Term := insert (fold pt) pt.ssubterms

/-- The subterms of a term. -/
@[rocq_alias cryptis.subterms]
def subterms (t : Term) : Finset Term := insert t t.unfold.ssubterms

theorem mem_ssubtermsList {ps : List PreTerm} :
    t ∈ PreTerm.ssubtermsList ps ↔ ∃ p ∈ ps, t ∈ subtermsPre p := by
  induction ps with
  | nil => simp [PreTerm.ssubtermsList]
  | cons p ps ih => simp [PreTerm.ssubtermsList, ih, subtermsPre, or_assoc]

@[rocq_alias cryptis.subterms_via_pre]
theorem subterms_eq_subtermsPre (t : Term) : t.subterms = subtermsPre t.unfold := by
  rw [subtermsPre, fold_unfold, subterms]

@[rocq_alias cryptis.subterms_fold]
theorem subterms_fold (h : pt.wf) : (fold pt).subterms = subtermsPre pt := by
  rw [subterms_eq_subtermsPre, unfold_fold_of_wf h]

@[rocq_alias cryptis.union_list_map_subterms_fold]
theorem biUnion_subtermsPre_map_unfold (X : Multiset Term) :
    (X.map unfold).toFinset.biUnion subtermsPre = X.toFinset.biUnion subterms := by
  ext
  simp [subterms_eq_subtermsPre]

theorem mem_subtermsPre_self (pt : PreTerm) : fold pt ∈ subtermsPre pt := Finset.mem_insert_self _ _

@[simp]
theorem mem_subterms_self (t : Term) : t ∈ t.subterms := Finset.mem_insert_self _ _

@[rocq_alias cryptis.subterms_pre_factors, rocq_alias cryptis.subterms_pre_gfactors]
theorem subtermsPre_eq_factors (o : TermOpN) (h : pt.wf) :
    subtermsPre pt = insert (fold pt) ((pt.factors o).elements.toFinset.biUnion subtermsPre) := by
  by_cases hm : pt.isProd o
  · obtain ⟨ps, ns, rfl⟩ := PreTerm.isProd_iff.mp hm
    rw [PreTerm.factors_opN, SMS.make_of_disjoint (PreTerm.wf_opN.mp h).2.1.disjoint]
    ext
    simp [subtermsPre, PreTerm.ssubterms, mem_ssubtermsList, SMS.elements, or_and_right,
      exists_or]
  · simp [PreTerm.factors_eq_singleton (by simpa using hm), mem_subtermsPre_self]

theorem ssubterms_ptExp {pb pe : PreTerm} (h : pe.wf) :
    (PreTerm.ptExp pb pe).ssubterms =
      subtermsPre pb ∪ (pe.factors .mul).elements.toFinset.biUnion subtermsPre := by
  by_cases hm : pe.isProd .mul
  · obtain ⟨ps, ns, rfl⟩ := PreTerm.isProd_iff.mp hm
    rw [PreTerm.factors_opN, SMS.make_of_disjoint (PreTerm.wf_opN.mp h).2.1.disjoint]
    ext
    simp [subtermsPre, PreTerm.ssubterms, mem_ssubtermsList, SMS.elements, or_and_right,
      exists_or]
  · rw [PreTerm.factors_eq_singleton (by simpa using hm)]
    rcases pe with _ | _ | _ | ⟨_ | _⟩
    case opN.mul => simp [PreTerm.isProd] at hm
    all_goals simp [PreTerm.ssubterms, subtermsPre]

#rocq_ignore cryptis.subterms_preE "Term.ssubterms_ptExp, Term.subtermsPre_eq_factors"

@[rocq_alias cryptis.subterms_pre_base_exps]
theorem subtermsPre_eq_base_exps (h : pt.wf) :
    subtermsPre pt = insert (fold pt)
      (subtermsPre pt.base ∪ (pt.expo.factors .mul).elements.toFinset.biUnion subtermsPre) := by
  by_cases hx : pt.isExp
  · obtain ⟨pb, pe, rfl⟩ := PreTerm.isExp_iff.mp hx
    rw [subtermsPre, ssubterms_ptExp (PreTerm.wf_ptExp.mp h).2.2.1]
    rfl
  · have hx : pt.isExp = false := by simpa using hx
    rw [PreTerm.base_eq_self hx, PreTerm.expo_eq_unit hx, PreTerm.factors_opN]
    simp [mem_subtermsPre_self]

@[rocq_alias cryptis.subterms_base_exps]
theorem subterms_eq_base_exps (t : Term) :
    t.subterms = insert t (t.base.subterms ∪ t.exps.elements.toFinset.biUnion subterms) := by
  rw [subterms_eq_subtermsPre, subtermsPre_eq_base_exps (wf_unfold t), fold_unfold, ← unfold_base,
    ← subterms_eq_subtermsPre, ← unfold_expo, ← map_unfold_elements_factors,
    biUnion_subtermsPre_map_unfold, exps]

@[simp] theorem subterms_int (n : Int) : (int n).subterms = {int n} := by
  simp [subterms, unfold, PreTerm.ssubterms]

@[simp] theorem subterms_nonce (a : Nonce) : (nonce a).subterms = {nonce a} := by
  simp [subterms, unfold, PreTerm.ssubterms]

@[simp]
theorem subterms_pair (t₁ t₂ : Term) :
    (pair t₁ t₂).subterms = insert (pair t₁ t₂) (t₁.subterms ∪ t₂.subterms) := by
  simp [subterms, unfold, PreTerm.ssubterms]

@[simp]
theorem subterms_key (kt : KeyType) (t : Term) :
    (key kt t).subterms = insert (key kt t) t.subterms := by
  simp [subterms, unfold, PreTerm.ssubterms]

@[simp]
theorem subterms_sealed (k t : Term) :
    (sealed k t).subterms = insert (sealed k t) (k.subterms ∪ t.subterms) := by
  simp [subterms, unfold, PreTerm.ssubterms]

@[simp]
theorem subterms_hash (t : Term) : (hash t).subterms = insert (hash t) t.subterms := by
  simp [subterms, unfold, PreTerm.ssubterms]

#rocq_ignore cryptis.subtermsE'
  "Split into the simp lemmas Term.subterms_int, …, Term.subterms_hash"
#rocq_ignore cryptis.subtermsE "A rewriting set; use the Term.subterms_* lemmas directly"

@[rocq_alias cryptis.subterms_TMul, rocq_alias cryptis.subterms_TGMul]
theorem subterms_prod (hs : ∀ u ∈ s, u.isProd o = false) :
    (prod o s).subterms = insert (prod o s) (s.elements.toFinset.biUnion subterms) := by
  rw [subterms_eq_subtermsPre, subtermsPre_eq_factors o (wf_unfold _), fold_unfold,
    ← map_unfold_elements_factors, factors_prod_of_forall hs, biUnion_subtermsPre_map_unfold]

@[rocq_alias cryptis.subterms_TInv, rocq_alias cryptis.subterms_TGInv]
theorem subterms_prod_neg_singleton (h : t.isProd o = false) :
    (prod o (-{t})).subterms = insert (prod o (-{t})) t.subterms := by
  have hs : ∀ x ∈ (-{t} : SMS Term), x.isProd o = false := fun x hx => by
    rw [← SMS.mem_elements, SMS.elements_neg, SMS.elements_singleton, Multiset.mem_singleton] at hx
    rwa [hx]
  rw [subterms_prod hs]
  simp

@[rocq_alias cryptis.subterms_TExp]
theorem subterms_exp (hx : t.isExp = false) (hg : t.isProd .gmul = false) (e : Term) :
    (t.exp e).subterms =
      insert (t.exp e) (t.subterms ∪ (e.factors .mul).elements.toFinset.biUnion subterms) := by
  rw [subterms_eq_base_exps, base_exp hg, base_eq_self hx, exps_exp hx hg]

@[rocq_alias cryptis.subterms_TExp_TMul]
theorem subterms_exp_prod (hx : t.isExp = false) (hg : t.isProd .gmul = false)
    (hs : ∀ u ∈ s, u.isProd .mul = false) :
    (t.exp (prod .mul s)).subterms =
      insert (t.exp (prod .mul s)) (t.subterms ∪ s.elements.toFinset.biUnion subterms) := by
  rw [subterms_exp hx hg, factors_prod_of_forall hs]

@[rocq_alias cryptis.subterms_nonce]
theorem subterms_of_isNonce (h : t.isNonce) : t.subterms = {t} := by
  cases t <;> simp_all [isNonce]

/-! ### Subterms and the subterm relation -/

/-- Induction on terms through their immediate parts: the arguments of the free constructors,
the base and exponent factors of exponentials, and the factors of products. -/
theorem induction_parts {motive : Term → Prop}
    (exp : ∀ t, t.isExp → motive t.base → (∀ u ∈ t.exps, motive u) → motive t)
    (prod : ∀ o t, t.isProd o → (∀ u ∈ t.factors o, motive u) → motive t)
    (int : ∀ n, motive (.int n))
    (pair : ∀ t₁ t₂, motive t₁ → motive t₂ → motive (.pair t₁ t₂))
    (nonce : ∀ a, motive (.nonce a))
    (key : ∀ kt t, motive t → motive (.key kt t))
    (sealed : ∀ k t, motive k → motive t → motive (.sealed k t))
    (hash : ∀ t, motive t → motive (.hash t)) (t : Term) : motive t := by
  induction t using tsize_induction with
  | h t ih =>
  by_cases hx : t.isExp
  · exact exp t hx (ih _ (tsize_base_lt hx)) fun u hu => ih u (tsize_lt_of_mem_exps hu)
  by_cases hm : t.isProd .mul
  · exact prod .mul t hm fun u hu => ih u (tsize_lt_of_mem_factors hm hu)
  by_cases hg : t.isProd .gmul
  · exact prod .gmul t hg fun u hu => ih u (tsize_lt_of_mem_factors hg hu)
  cases t with
  | nonFree pt _ nf =>
    simp only [isExp, isProd, Bool.not_eq_true] at hx hm hg
    simp [PreTerm.isNonFree, hx, hm, hg] at nf
  | int n => exact int n
  | pair t₁ t₂ => exact pair _ _ (ih t₁ (by simp; omega)) (ih t₂ (by simp; omega))
  | nonce a => exact nonce a
  | key kt t => exact key _ _ (ih t (by simp))
  | sealed k t => exact sealed _ _ (ih k (by simp; omega)) (ih t (by simp; omega))
  | hash t => exact hash _ (ih t (by simp))

@[rocq_alias cryptis.subterm_base]
theorem Subterm.base (t : Term) : Subterm t.base t := by
  by_cases hx : t.isExp
  · conv_rhs => rw [← exp_base_expo t]
    exact expBase (isExp_base t) (by rw [isProd_base]; exact isProd_eq_false_of_isExp _ hx) refl
  · rw [base_eq_self (by simpa using hx)]

@[rocq_alias cryptis.subterm_exps]
theorem Subterm.of_mem_exps (h : t₁ ∈ t₂.exps) : Subterm t₁ t₂ := by
  rw [← exp_base_expo t₂]
  exact expFactor (isExp_base t₂)
    (by rw [isProd_base]; exact isProd_eq_false_of_isExp _ (isExp_of_mem_exps h)) refl h

@[rocq_alias cryptis.subtermsP]
theorem subterm_iff_mem_subterms : Subterm t₁ t₂ ↔ t₁ ∈ t₂.subterms := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | refl => exact mem_subterms_self _
    | expBase hx hg _ ih => simp [subterms_exp hx hg, ih]
    | expFactor hx hg _ hu ih =>
      simp only [subterms_exp hx hg, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
        Multiset.mem_toFinset, SMS.mem_elements]
      exact .inr (.inr ⟨_, hu, ih⟩)
    | prod hs _ hu ih =>
      simp only [subterms_prod hs, Finset.mem_insert, Finset.mem_biUnion, Multiset.mem_toFinset,
        SMS.mem_elements]
      exact .inr ⟨_, hu, ih⟩
    | _ => simp_all
  · induction t₂ using induction_parts with
    | exp t hx hb he =>
      simp only [subterms_eq_base_exps t, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
        Multiset.mem_toFinset, SMS.mem_elements] at h
      rcases h with rfl | h | ⟨u, hu, h⟩
      exacts [.refl, (hb h).trans (.base t), (he u hu h).trans (.of_mem_exps hu)]
    | prod o t hm ih =>
      rw [← prod_factors o t, subterms_prod fun _ hx => isProd_of_mem_factors hx] at h
      simp only [Finset.mem_insert, Finset.mem_biUnion, Multiset.mem_toFinset,
        SMS.mem_elements, prod_factors] at h
      rcases h with rfl | ⟨u, hu, h⟩
      exacts [.refl, .of_mem_factors hu (ih u hu h)]
    | int | nonce => simp_all [Subterm.refl]
    | pair _ _ ih₁ ih₂ =>
      simp only [subterms_pair, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | h | h
      exacts [.refl, .pairLeft (ih₁ h), .pairRight (ih₂ h)]
    | key _ _ ih =>
      simp only [subterms_key, Finset.mem_insert] at h
      rcases h with rfl | h
      exacts [.refl, .key (ih h)]
    | sealed _ _ ih₁ ih₂ =>
      simp only [subterms_sealed, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | h | h
      exacts [.refl, .sealedLeft (ih₁ h), .sealedRight (ih₂ h)]
    | hash _ ih =>
      simp only [subterms_hash, Finset.mem_insert] at h
      rcases h with rfl | h
      exacts [.refl, .hash (ih h)]

@[rocq_alias cryptis.subterm_TExp_g]
theorem Subterm.nonce_exp {g : Term} (a : Nonce) (hx : g.isExp = false)
    (hg : g.isProd .gmul = false) :
    Subterm (nonce a) (g.exp (nonce a)) :=
  expFactor hx hg refl ((mem_factors_iff_eq rfl).mpr rfl)

@[rocq_alias cryptis.nonces_of_termP]
theorem subterm_nonce_iff {a : Nonce} : Subterm (nonce a) t ↔ a ∈ t.nonces := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | refl => simp
    | expBase hx hg _ ih => simp [nonces_exp hx hg, ih]
    | expFactor hx hg _ hu ih =>
      simp only [nonces_exp hx hg, Finset.mem_union, Finset.mem_biUnion, Multiset.mem_toFinset,
        SMS.mem_elements]
      exact .inr ⟨_, hu, ih⟩
    | prod hs _ hu ih =>
      simp only [nonces_prod hs, Finset.mem_biUnion, Multiset.mem_toFinset, SMS.mem_elements]
      exact ⟨_, hu, ih⟩
    | _ => simp_all
  · induction t using induction_parts with
    | exp t hx hb he =>
      simp only [nonces_eq_base_union_exps t, Finset.mem_union, Finset.mem_biUnion,
        Multiset.mem_toFinset, SMS.mem_elements] at h
      rcases h with h | ⟨u, hu, h⟩
      exacts [(hb h).trans (.base t), (he u hu h).trans (.of_mem_exps hu)]
    | prod o t hm ih =>
      rw [nonces_eq_biUnion_factors o] at h
      simp only [Finset.mem_biUnion, Multiset.mem_toFinset, SMS.mem_elements] at h
      obtain ⟨u, hu, h⟩ := h
      exact .of_mem_factors hu (ih u hu h)
    | int => simp at h
    | nonce => simp_all [Subterm.refl]
    | pair _ _ ih₁ ih₂ =>
      rcases Finset.mem_union.mp (nonces_pair _ _ ▸ h) with h | h
      exacts [.pairLeft (ih₁ h), .pairRight (ih₂ h)]
    | key _ _ ih => exact .key (ih (nonces_key _ _ ▸ h))
    | sealed _ _ ih₁ ih₂ =>
      rcases Finset.mem_union.mp (nonces_sealed _ _ ▸ h) with h | h
      exacts [.sealedLeft (ih₁ h), .sealedRight (ih₂ h)]
    | hash _ ih => exact .hash (ih (nonces_hash _ ▸ h))

@[rocq_alias cryptis.subterm_nonces_of_term]
theorem Subterm.nonces_subset (h : Subterm t₁ t₂) : t₁.nonces ⊆ t₂.nonces :=
  fun _ ha => subterm_nonce_iff.mp ((subterm_nonce_iff.mpr ha).trans h)

end Term
end Cryptis
