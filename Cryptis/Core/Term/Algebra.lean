module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Cryptis.Core.Term.Base

/-! The algebra of terms.

Terms under each of the two products form a commutative group. The exponents `E` are the terms
under the scalar product, and the Diffie–Hellman group `G` is the terms under the group product.
Each group is free: a term is determined by its factors, the terms that are not products of that
kind, each with an integer multiplicity. The laws of products are proved by comparing factors or
multiplicities.

Exponentiation is an action of the exponents on the Diffie–Hellman group: `a • g` raises `g` to
the exponent `a`. It distributes over group products, multiplies iterated exponents, and is
injective in both arguments: in the base because the inverse exponent undoes it, and in the
exponent whenever the base is not the unit of `G`.

- Products: the factors and multiplicities of products.
- The groups of products: `E` and `G` as Mathlib commutative groups. An element is a term in a
  wrapper, to which it coerces; simp lemmas push the coercion down to `prod` and `exp`, and
  `norm_cast` lifts it back up.
- Bases and exponents: every term is its base raised to its exponent.
- Exponentiation distributes over group products, and iterated exponentials merge their
  exponents.
- Exponentiation as a group action of `E` on `G`, by automorphisms.
- Signed atoms: the factors of an exponent as elements of `E`, inverted when they occur
  negatively.
- Group factors of powers: exponentiation is injective in the exponent. -/

@[expose] public section
namespace Cryptis
namespace Term

variable {o : TermOpN} {t t' t₁ t₂ x b e e₁ e₂ u : Term} {s s₁ s₂ : SMS Term}

/-! ### Products -/

@[rocq_alias cryptis.count_unfold, rocq_alias cryptis.gcount_unfold]
theorem count_unfold (o : TermOpN) (x t : Term) :
    count o x t = (t.unfold.factors o).count x.unfold := by
  rw [count, ← map_unfold_factors, SMS.count_map_of_injective unfold_injective]

@[simp, rocq_alias cryptis.factors_TMul_empty, rocq_alias cryptis.gfactors_TGMul_empty]
theorem factors_prod_zero (o : TermOpN) : (prod o 0).factors o = 0 := by simp

@[simp, rocq_alias cryptis.TMul_singleton, rocq_alias cryptis.TGMul_singleton]
theorem prod_singleton (o : TermOpN) (t : Term) : prod o {t} = t :=
  factors_injective o (by simp)

@[rocq_alias cryptis.count_TMul, rocq_alias cryptis.gcount_TGMul]
theorem count_prod (o : TermOpN) (x : Term) (s : SMS Term) :
    count o x (prod o s) = (s.bind (factors o)).count x := by
  rw [count, factors_prod]

@[simp, rocq_alias cryptis.count_TMul_empty, rocq_alias cryptis.gcount_TGMul_empty]
theorem count_prod_zero (o : TermOpN) (x : Term) : count o x (prod o 0) = 0 := by
  simp [count_prod]

@[simp, rocq_alias cryptis.count_TMul2]
theorem count_prod_pair (o : TermOpN) (x t₁ t₂ : Term) :
    count o x (prod o ({t₁} + {t₂})) = count o x t₁ + count o x t₂ := by
  simp [count]

@[simp, rocq_alias cryptis.count_TInv, rocq_alias cryptis.gcount_TGInv]
theorem count_prod_neg_singleton (o : TermOpN) (x t : Term) :
    count o x (prod o (-{t})) = -count o x t := by
  simp [count]

@[rocq_alias cryptis.tunitP, rocq_alias cryptis.gtunitP]
theorem factors_eq_zero_iff : t.factors o = 0 ↔ t = prod o 0 :=
  (factors_injective o).eq_iff' (factors_prod_zero o)

theorem factors_prod_zsmul (o : TermOpN) (n : ℤ) (t : Term) :
    (prod o (n • {t})).factors o = n • t.factors o := by
  rw [factors_prod]
  exact (map_zsmul (AddMonoidHom.mk' _ (SMS.bind_add (factors o))) n {t}).trans
    (congrArg _ (SMS.bind_singleton _ _))

@[rocq_alias cryptis.is_mul_TInv_atom, rocq_alias cryptis.is_gmul_TGInv_atom]
theorem isProd_prod_neg_singleton (h : t.isProd o = false) : (prod o (-{t})).isProd o := by
  by_contra h'
  have := congrArg SMS.posPart
    ((factors_eq_singleton (by simpa using h')).symm.trans (factors_prod o (-{t})))
  simp [factors_eq_singleton h] at this

@[rocq_alias cryptis.is_mul_TMul2]
theorem isProd_prod_pair (h₁ : t₁.isProd o = false) (h₂ : t₂.isProd o = false) :
    (prod o ({t₁} + {t₂})).isProd o := by
  by_contra h
  have hf := factors_prod_of_forall (s := {t₁} + {t₂}) (o := o) fun x hx => by
    rcases SMS.mem_or_mem_of_mem_add hx with hx | hx <;> rw [SMS.mem_singleton.mp hx] <;>
      assumption
  rw [factors_eq_singleton (by simpa using h)] at hf
  have := congrArg (fun s => Multiset.card (SMS.elements s)) hf
  simp [SMS.elements_add (s := {t₁}) (t := {t₂}) (by simp) (by simp)] at this

@[rocq_alias cryptis.count_diag, rocq_alias cryptis.gcount_diag]
theorem count_self (o : TermOpN) (t : Term) : count o t t = if t.isProd o then 0 else 1 := by
  cases h : t.isProd o
  · simp [count, factors_eq_singleton h]
  · exact count_of_isProd h t

@[rocq_alias cryptis.count_neq0, rocq_alias cryptis.gcount_neq0]
theorem count_ne_zero_iff : count o t t' ≠ 0 ↔ t ∈ t'.factors o :=
  SMS.mem_iff_count_ne_zero.symm

@[rocq_alias cryptis.count_gt0, rocq_alias cryptis.gcount_gt0]
theorem count_pos_iff : 0 < count o t t' ↔ t ∈ (t'.factors o).posPart := SMS.count_pos_iff

@[rocq_alias cryptis.count_lt0, rocq_alias cryptis.gcount_lt0]
theorem count_neg_iff : count o t t' < 0 ↔ t ∈ (t'.factors o).negPart := SMS.count_neg_iff

@[rocq_alias cryptis.not_elem_of_count, rocq_alias cryptis.not_elem_of_gcount]
theorem count_eq_zero_of_not_mem (h : t ∉ t'.factors o) : count o t t' = 0 :=
  SMS.count_eq_zero_of_not_mem h

@[rocq_alias cryptis.count_atom_ne]
theorem count_of_ne (h : t₂.isProd o = false) (hne : t₁ ≠ t₂) : count o t₁ t₂ = 0 := by
  simp [count, factors_eq_singleton h, hne]

@[rocq_alias cryptis.count_atom_ge0, rocq_alias cryptis.gcount_atom_ge0]
theorem count_nonneg (h : t₂.isProd o = false) (t₁ : Term) : 0 ≤ count o t₁ t₂ := by
  simp only [count, factors_eq_singleton h, SMS.count_singleton]
  split <;> omega

@[rocq_alias cryptis.count_TMul_atoms]
theorem count_prod_of_forall (hs : ∀ u ∈ s, u.isProd o = false) (x : Term) :
    count o x (prod o s) = s.count x := by
  rw [count, factors_prod_of_forall hs]

@[rocq_alias cryptis.count_TMul_atoms_ne]
theorem count_prod_eq_zero (h : ∀ u ∈ s, u.isProd o = false ∧ t ≠ u) :
    count o t (prod o s) = 0 := by
  rw [count_prod_of_forall fun u hu => (h u hu).1]
  exact SMS.count_eq_zero_of_not_mem fun ht => (h t ht).2 rfl

@[rocq_alias cryptis.not_elem_of_factors_TMul]
theorem not_mem_factors_prod (h : ∀ u ∈ s, u.isProd o = false ∧ t ≠ u) :
    t ∉ (prod o s).factors o :=
  fun ht => count_ne_zero_iff.mpr ht (count_prod_eq_zero h)

@[rocq_alias cryptis.not_elem_of_factors_atom]
theorem not_mem_factors_of_ne (h : t₂.isProd o = false) (hne : t₁ ≠ t₂) : t₁ ∉ t₂.factors o :=
  fun ht => count_ne_zero_iff.mpr ht (count_of_ne h hne)

@[rocq_alias cryptis.count_atom_diag]
theorem count_self_of_isProd_eq_false (h : t.isProd o = false) : count o t t = 1 := by
  simp [count_self, h]

@[rocq_alias cryptis.elem_of_factors_Nmul, rocq_alias cryptis.elem_of_gfactors_Ngmul]
theorem mem_factors_iff_eq (h : t.isProd o = false) : x ∈ t.factors o ↔ x = t := by
  rw [factors_eq_singleton h, SMS.mem_singleton]

@[rocq_alias cryptis.Ngmul_neq_unit]
theorem ne_prod_zero (h : t.isProd o = false) : t ≠ prod o 0 := by
  rintro rfl
  rw [← isProd_unfold, unfold_prod_zero, PreTerm.isProd_opN] at h
  cases h

@[rocq_alias cryptis.gfactors_nonempty]
theorem exists_mem_factors (h : t ≠ prod o 0) : ∃ u, u ∈ t.factors o := by
  by_contra! h'
  exact h (factors_eq_zero_iff.mp (SMS.eq_zero_of_elements_eq_zero
    (Multiset.eq_zero_of_forall_notMem h')))

@[rocq_alias cryptis.TGMul_bind]
theorem prod_bind (o : TermOpN) (f : Term → SMS Term) (s : SMS Term) :
    prod o (s.bind f) = prod o (s.map fun x => prod o (f x)) :=
  factors_injective o <| by
    rw [factors_prod, factors_prod, SMS.bind_bind, SMS.bind_map]
    exact SMS.bind_congr fun x _ => (factors_prod o (f x)).symm

/-! ### The groups of products -/

/-- Terms under the product of kind `o`: a commutative group, free on the terms that are not
products of that kind. -/
@[ext]
structure ProdGroup (o : TermOpN) where
  /-- A term as an element of `ProdGroup o`. -/
  ofTerm ::
  /-- The underlying term. -/
  toTerm : Term
deriving DecidableEq

/-- Exponents: terms under the scalar product. -/
abbrev E : Type := ProdGroup .mul

/-- The Diffie-Hellman group: terms under the group product. -/
abbrev G : Type := ProdGroup .gmul

/-- A term as an exponent. -/
abbrev E.ofTerm (t : Term) : E := ProdGroup.ofTerm t

/-- A term as an element of the Diffie-Hellman group. -/
abbrev G.ofTerm (t : Term) : G := ProdGroup.ofTerm t

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- Shows `ProdGroup .mul` and `ProdGroup .gmul` as `E` and `G`. -/
@[delab app.Cryptis.Term.ProdGroup]
meta def delabProdGroup : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard (e.getAppNumArgs == 1)
  let n ← match e.appArg!.constName? with
    | some ``TermOpN.mul => pure ``E
    | some ``TermOpN.gmul => pure ``G
    | _ => failure
  withTheReader SubExpr ({ · with expr := .const n [] }) delabConst

/-- Shows `ProdGroup.ofTerm t` as `E.ofTerm t` or `G.ofTerm t`. -/
@[delab app.Cryptis.Term.ProdGroup.ofTerm]
meta def delabProdGroupOfTerm : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let n ← match (e.getArg! 0).constName? with
    | some ``TermOpN.mul => pure ``E.ofTerm
    | some ``TermOpN.gmul => pure ``G.ofTerm
    | _ => failure
  let f ← withTheReader SubExpr ({ · with expr := .const n [] }) delabConst
  let t ← withAppArg delab
  `($f $t)

end Delab

namespace ProdGroup

instance : CoeOut (ProdGroup o) Term := ⟨toTerm⟩

attribute [coe] toTerm

variable {a b : ProdGroup o}

@[simp, norm_cast]
theorem coe_ofTerm (t : Term) : ((ofTerm t : ProdGroup o) : Term) = t := rfl

@[simp]
theorem ofTerm_coe (a : ProdGroup o) : ofTerm (a : Term) = a := rfl

theorem coe_injective : Function.Injective ((↑) : ProdGroup o → Term) := fun _ _ => ProdGroup.ext

@[simp, norm_cast]
theorem coe_inj : (a : Term) = b ↔ a = b := coe_injective.eq_iff

theorem coe_surjective : Function.Surjective ((↑) : ProdGroup o → Term) := fun t => ⟨ofTerm t, rfl⟩

theorem ofTerm_injective : Function.Injective (ofTerm : Term → ProdGroup o) :=
  fun _ _ h => congrArg toTerm h

@[simp]
theorem ofTerm_inj {t₁ t₂ : Term} : (ofTerm t₁ : ProdGroup o) = ofTerm t₂ ↔ t₁ = t₂ :=
  ofTerm_injective.eq_iff

instance : One (ProdGroup o) := ⟨ofTerm (prod o 0)⟩

instance : Mul (ProdGroup o) := ⟨fun a b => ofTerm (prod o ({↑a} + {↑b}))⟩

instance : Inv (ProdGroup o) := ⟨fun a => ofTerm (prod o (-{↑a}))⟩

instance : Div (ProdGroup o) := ⟨fun a b => ofTerm (prod o ({↑a} - {↑b}))⟩

instance : Pow (ProdGroup o) ℕ := ⟨fun a n => ofTerm (prod o (n • {↑a}))⟩

instance : Pow (ProdGroup o) ℤ := ⟨fun a n => ofTerm (prod o (n • {↑a}))⟩

@[simp, norm_cast]
theorem coe_one : ((1 : ProdGroup o) : Term) = prod o 0 := rfl

@[simp, norm_cast]
theorem coe_mul (a b : ProdGroup o) : (↑(a * b) : Term) = prod o ({↑a} + {↑b}) := rfl

@[simp, norm_cast]
theorem coe_inv (a : ProdGroup o) : (↑a⁻¹ : Term) = prod o (-{↑a}) := rfl

@[simp, norm_cast]
theorem coe_div (a b : ProdGroup o) : (↑(a / b) : Term) = prod o ({↑a} - {↑b}) := rfl

@[simp, norm_cast]
theorem coe_pow (a : ProdGroup o) (n : ℕ) : (↑(a ^ n) : Term) = prod o (n • {↑a}) := rfl

@[simp, norm_cast]
theorem coe_zpow (a : ProdGroup o) (n : ℤ) : (↑(a ^ n) : Term) = prod o (n • {↑a}) := rfl

theorem factors_coe_one : (↑(1 : ProdGroup o) : Term).factors o = 0 := factors_prod_zero o

theorem factors_coe_mul (a b : ProdGroup o) :
    (↑(a * b) : Term).factors o = (↑a : Term).factors o + (↑b : Term).factors o := by
  simp

theorem factors_coe_inv (a : ProdGroup o) :
    (↑a⁻¹ : Term).factors o = -(↑a : Term).factors o := by
  simp

theorem factors_coe_div (a b : ProdGroup o) :
    (↑(a / b) : Term).factors o = (↑a : Term).factors o - (↑b : Term).factors o := by
  simp [sub_eq_add_neg]

theorem factors_coe_zpow (a : ProdGroup o) (n : ℤ) :
    (↑(a ^ n) : Term).factors o = n • (↑a : Term).factors o :=
  factors_prod_zsmul o n a

theorem factors_coe_pow (a : ProdGroup o) (n : ℕ) :
    (↑(a ^ n) : Term).factors o = n • (↑a : Term).factors o := by
  rw [← natCast_zsmul, ← factors_coe_zpow]
  simp

theorem isProd_coe_inv (h : (a : Term).isProd o = false) : (↑a⁻¹ : Term).isProd o :=
  isProd_prod_neg_singleton h

theorem factors_coe_injective :
    Function.Injective fun a : ProdGroup o => (a : Term).factors o :=
  (factors_injective o).comp coe_injective

@[rocq_alias cryptis.TMul_disj_union, rocq_alias cryptis.TMul_unit_l,
  rocq_alias cryptis.TMul_unit_r, rocq_alias cryptis.TMul_inv_r,
  rocq_alias cryptis.TGMul_disj_union, rocq_alias cryptis.TGMul_unit_l,
  rocq_alias cryptis.TGMul_unit_r, rocq_alias cryptis.TGMul_inv_r]
instance : CommGroup (ProdGroup o) :=
  Function.Injective.commGroup (fun a : ProdGroup o => Multiplicative.ofAdd ((a : Term).factors o))
    (Multiplicative.ofAdd.injective.comp factors_coe_injective)
    (congrArg Multiplicative.ofAdd factors_coe_one)
    (fun a b => congrArg Multiplicative.ofAdd (factors_coe_mul a b))
    (fun a => congrArg Multiplicative.ofAdd (factors_coe_inv a))
    (fun a b => congrArg Multiplicative.ofAdd (factors_coe_div a b))
    (fun a n => congrArg Multiplicative.ofAdd (factors_coe_pow a n))
    (fun a n => congrArg Multiplicative.ofAdd (factors_coe_zpow a n))

/-- `factors` as a homomorphism into the free abelian group on terms. -/
@[simps]
def factorsHom : ProdGroup o →* Multiplicative (SMS Term) where
  toFun a := .ofAdd ((a : Term).factors o)
  map_one' := congrArg _ factors_coe_one
  map_mul' := factors_coe_mul

theorem factorsHom_injective : Function.Injective (factorsHom (o := o)) :=
  Multiplicative.ofAdd.injective.comp factors_coe_injective

/-- `ProdGroup o` is the free abelian group on the terms that are not products of kind `o`. -/
theorem mem_range_factorsHom {s : Multiplicative (SMS Term)} :
    s ∈ (factorsHom (o := o)).range ↔ ∀ x ∈ s.toAdd, x.isProd o = false := by
  refine ⟨?_, fun h =>
    ⟨ofTerm (prod o s.toAdd), congrArg Multiplicative.ofAdd (factors_prod_of_forall h)⟩⟩
  rintro ⟨a, rfl⟩ x hx
  exact isProd_of_mem_factors hx

@[rocq_alias cryptis.count_TMul_disj_union, rocq_alias cryptis.gcount_TGMul_disj_union]
theorem count_coe_mul (x : Term) (a b : ProdGroup o) :
    count o x ↑(a * b) = count o x ↑a + count o x ↑b :=
  count_prod_pair o x a b

@[rocq_alias cryptis.count_TMul_inv, rocq_alias cryptis.gcount_TGMul_inv]
theorem count_coe_inv (x : Term) (a : ProdGroup o) : count o x ↑a⁻¹ = -count o x ↑a :=
  count_prod_neg_singleton o x a

theorem count_coe_one (x : Term) : count o x ↑(1 : ProdGroup o) = 0 := count_prod_zero o x

/-- The product of kind `o` of the elements of a signed multiset is their product in
`ProdGroup o`. -/
@[simp]
theorem ofTerm_prod (o : TermOpN) (s : SMS Term) :
    (ofTerm (prod o s) : ProdGroup o) = s.prod ofTerm :=
  factorsHom_injective <| by
    induction s using SMS.induction with
    | zero => simp [SMS.prod_zero]
    | add x s ih =>
      rw [SMS.prod_add, SMS.prod_singleton, map_mul, ← ih]
      simp [ofAdd_add]
    | sub x s ih =>
      rw [SMS.prod_add, SMS.prod_neg, SMS.prod_singleton, map_mul, map_inv, ← ih]
      simp [ofAdd_add, ofAdd_neg]

theorem coe_prod (s : SMS Term) : (↑(s.prod ofTerm : ProdGroup o) : Term) = prod o s := by
  rw [← ofTerm_prod, coe_ofTerm]

@[rocq_alias cryptis.elem_of_factors_TInv]
theorem mem_factors_coe_inv {x : Term} :
    x ∈ (↑a⁻¹ : Term).factors o ↔ x ∈ (↑a : Term).factors o := by
  simp only [← count_ne_zero_iff, count_coe_inv, neg_ne_zero]

@[rocq_alias cryptis.elem_of_factors_TMul2, rocq_alias cryptis.elem_of_gfactors_TGMul2]
theorem mem_factors_coe_mul {x : Term} (h : x ∈ (↑(a * b) : Term).factors o) :
    x ∈ (↑a : Term).factors o ∨ x ∈ (↑b : Term).factors o := by
  simp only [← count_ne_zero_iff, count_coe_mul] at h ⊢
  omega

@[rocq_alias cryptis.TInv_fixed, rocq_alias cryptis.TGInv_fixed]
theorem inv_eq_self_iff : a⁻¹ = a ↔ a = 1 := by
  refine ⟨fun h => coe_injective (ext_count (o := o) fun x _ => ?_), fun h => h ▸ inv_one⟩
  have := congrArg (fun a : ProdGroup o => count o x a) h
  simp only [count_coe_inv, count_coe_one] at this ⊢
  omega

end ProdGroup

open ProdGroup

attribute [rocq_alias cryptis.TInv, rocq_alias cryptis.TGInv] ProdGroup.instInv
attribute [rocq_alias cryptis.factors_TInv, rocq_alias cryptis.gfactors_TGInv]
  ProdGroup.factors_coe_inv

#rocq_ignore cryptis.TInvK "Mathlib's inv_inv on Term.ProdGroup"
#rocq_ignore cryptis.TGInvK "Mathlib's inv_inv on Term.ProdGroup"
#rocq_ignore cryptis.TInv_inj "Mathlib's inv_injective on Term.ProdGroup"
#rocq_ignore cryptis.TGInv_inj "Mathlib's inv_injective on Term.ProdGroup"
#rocq_ignore cryptis.TInv_TMul "Mathlib's mul_inv on Term.ProdGroup, with ofTerm_prod"
#rocq_ignore cryptis.TGInv_TGMul "Mathlib's mul_inv on Term.ProdGroup, with ofTerm_prod"
#rocq_ignore cryptis.TMulK "Mathlib's mul_inv_cancel_right on Term.E"
#rocq_ignore cryptis.TMulKV "Mathlib's inv_mul_cancel_right on Term.E"

/-! ### Bases and exponents -/

@[rocq_alias cryptis.Ngmul_TExp]
theorem isProd_exp_eq_false (h : b.isProd .gmul = false) (e : Term) :
    (b.exp e).isProd .gmul = false := by
  rw [← isProd_unfold, unfold_exp]
  exact PreTerm.isProd_gmul_exp (wf_unfold b) (wf_unfold e) (by rwa [← isProd_unfold] at h)

@[simp, rocq_alias cryptis.base_Nexp]
theorem isExp_base (t : Term) : t.base.isExp = false := by
  rw [← isExp_unfold, unfold_base]
  exact PreTerm.isExp_base (wf_unfold t)

@[simp, rocq_alias cryptis.is_gmul_base]
theorem isProd_base (t : Term) : t.base.isProd .gmul = t.isProd .gmul := by
  rw [← isProd_unfold, unfold_base, ← isProd_unfold]
  exact PreTerm.isProd_gmul_base (wf_unfold t)

@[rocq_alias cryptis.base_expN]
theorem base_eq_self (h : t.isExp = false) : t.base = t :=
  unfold_injective (by rw [unfold_base, PreTerm.base_eq_self (by rwa [isExp_unfold])])

@[simp, rocq_alias cryptis.base_idem]
theorem base_base (t : Term) : t.base.base = t.base := base_eq_self (isExp_base t)

@[rocq_alias cryptis.expo_expN]
theorem expo_eq_unit (h : t.isExp = false) : t.expo = prod .mul 0 :=
  unfold_injective <| by
    rw [unfold_expo, unfold_prod_zero, PreTerm.expo_eq_unit (by rwa [isExp_unfold])]

/-! A term is at most one of an exponential, a scalar product and a group product. -/

@[rocq_alias cryptis.is_exp_Nmul, rocq_alias cryptis.is_exp_Ngmul]
theorem isProd_eq_false_of_isExp (o : TermOpN) (h : t.isExp) : t.isProd o = false := by
  rw [← isExp_unfold] at h
  obtain ⟨_, _, h⟩ := PreTerm.isExp_iff.mp h
  rw [← isProd_unfold, h, PreTerm.isProd_ptExp]

@[rocq_alias cryptis.is_mul_Nexp]
theorem isExp_eq_false_of_isProd (h : t.isProd o) : t.isExp = false := by
  rw [← isProd_unfold] at h
  obtain ⟨_, _, h⟩ := PreTerm.isProd_iff.mp h
  rw [← isExp_unfold, h]
  rfl

@[rocq_alias cryptis.is_mul_Ngmul]
theorem isProd_gmul_eq_false_of_isProd_mul (h : t.isProd .mul) : t.isProd .gmul = false := by
  rw [← isProd_unfold] at h
  obtain ⟨_, _, h⟩ := PreTerm.isProd_iff.mp h
  rw [← isProd_unfold, h]
  rfl

@[rocq_alias cryptis.base_TExp]
theorem base_exp (h : b.isProd .gmul = false) (e : Term) : (b.exp e).base = b.base :=
  unfold_injective <| by
    rw [unfold_base, unfold_exp, PreTerm.base_exp (wf_unfold b) (wf_unfold e)
      (by rwa [← isProd_unfold] at h), unfold_base]

@[rocq_alias cryptis.expo_TExp]
theorem expo_exp (h : b.isProd .gmul = false) (e : Term) :
    (b.exp e).expo = prod .mul ({b.expo} + {e}) :=
  unfold_injective <| by
    rw [unfold_expo, unfold_exp, PreTerm.expo_exp (wf_unfold b) (wf_unfold e)
      (by rwa [← isProd_unfold] at h), unfold_prod_pair, unfold_expo]

@[rocq_alias cryptis.expo_TExp_expN]
theorem expo_exp_of_isExp_eq_false (hx : b.isExp = false) (hg : b.isProd .gmul = false)
    (e : Term) : (b.exp e).expo = e := by
  rw [expo_exp hg, expo_eq_unit hx]
  exact congrArg ProdGroup.toTerm (one_mul (E.ofTerm e))

/-- A base that is neither an exponential nor a product determines the exponent. -/
theorem exp_right_injective (hx : b.isExp = false) (hg : b.isProd .gmul = false) :
    Function.Injective b.exp := fun e₁ e₂ h => by
  simpa [expo_exp_of_isExp_eq_false hx hg] using congrArg expo h

/-- Diffie–Hellman shares of different nonces differ. -/
theorem nonce_eq_of_exp_eq (hx : b.isExp = false) (hg : b.isProd .gmul = false) {a₁ a₂ : Nonce}
    (h : b.exp a₁ = b.exp a₂) : a₁ = a₂ := by
  simpa using exp_right_injective hx hg h

@[simp, rocq_alias cryptis.TExp_base_expo]
theorem exp_base_expo (t : Term) : t.base.exp t.expo = t :=
  unfold_injective <| by
    rw [unfold_exp, unfold_base, unfold_expo, PreTerm.exp_base_expo (wf_unfold t)]

@[simp, rocq_alias cryptis.TExp_unit]
theorem exp_unit (b : Term) : b.exp (prod .mul 0) = b :=
  unfold_injective <| by
    rw [unfold_exp, unfold_prod_zero]
    exact PreTerm.exp_unit (wf_unfold b)

/-! ### Exponentiation distributes over group products -/

@[rocq_alias cryptis.TExp_gfactors]
theorem exp_eq_prod_factors (b e : Term) :
    b.exp e = prod .gmul ((b.factors .gmul).map (·.exp e)) := by
  apply unfold_injective
  rw [unfold_exp, unfold_prod, PreTerm.exp, ← map_unfold_factors, SMS.map_map, SMS.map_map]
  refine congrArg _ (SMS.map_congr fun u hu => ?_)
  simp only [Function.comp_apply, unfold_exp]
  exact (PreTerm.exp_eq_expAux (wf_unfold u) (wf_unfold e)
    (by rw [isProd_unfold]; exact isProd_of_mem_factors hu)).symm

@[rocq_alias cryptis.gfactors_TExp]
theorem factors_exp (b e : Term) : (b.exp e).factors .gmul = (b.factors .gmul).map (·.exp e) := by
  rw [exp_eq_prod_factors, factors_prod_of_forall]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map hx
  exact isProd_exp_eq_false (isProd_of_mem_factors hu) e

@[rocq_alias cryptis.TExp_TGMul]
theorem exp_prod (s : SMS Term) (e : Term) :
    (prod .gmul s).exp e = prod .gmul (s.map (·.exp e)) := by
  refine factors_injective .gmul ?_
  rw [factors_exp, factors_prod, factors_prod, SMS.map_bind, SMS.bind_map]
  exact SMS.bind_congr fun u _ => (factors_exp u e).symm

@[simp]
theorem exp_prod_zero (e : Term) : (prod .gmul 0).exp e = prod .gmul 0 := by
  rw [exp_prod, SMS.map_zero]

/-! ### Iterated exponentials -/

/-- The scalar factors of the exponent. -/
@[rocq_alias cryptis.exps]
def exps (t : Term) : SMS Term := t.expo.factors .mul

@[rocq_alias cryptis.count_mem_exps_pos]
theorem count_posPart_exps (x t : Term) :
    t.exps.posPart.count x = (count .mul x t.expo).toNat :=
  SMS.count_posPart _ _

@[rocq_alias cryptis.exps_TExp_expN]
theorem exps_exp (hx : b.isExp = false) (hg : b.isProd .gmul = false) (e : Term) :
    (b.exp e).exps = e.factors .mul := by
  rw [exps, expo_exp_of_isExp_eq_false hx hg]

theorem exp_exp_of_isProd_eq_false (h : b.isProd .gmul = false) (e₁ e₂ : Term) :
    (b.exp e₁).exp e₂ = b.exp (prod .mul ({e₁} + {e₂})) := by
  have h₁ := isProd_exp_eq_false h e₁
  rw [← exp_base_expo ((b.exp e₁).exp e₂), ← exp_base_expo (b.exp (prod .mul ({e₁} + {e₂})))]
  simp only [base_exp h₁, base_exp h, expo_exp h₁, expo_exp h]
  exact congrArg _ (factors_injective .mul (by simp [add_assoc]))

/-- Iterated exponents multiply. -/
@[rocq_alias cryptis.TExpA]
theorem exp_exp (b e₁ e₂ : Term) : (b.exp e₁).exp e₂ = b.exp (prod .mul ({e₁} + {e₂})) := by
  rw [exp_eq_prod_factors b e₁, exp_prod, exp_eq_prod_factors b, SMS.map_map]
  exact congrArg _ (SMS.map_congr fun u hu =>
    exp_exp_of_isProd_eq_false (isProd_of_mem_factors hu) e₁ e₂)

@[rocq_alias cryptis.TExpE]
theorem exp_eq_exp_base (b e : Term) : b.exp e = b.base.exp (prod .mul ({b.expo} + {e})) := by
  conv_lhs => rw [← exp_base_expo b]
  rw [exp_exp]

@[rocq_alias cryptis.base_expsK]
theorem exp_base_prod_exps (t : Term) : t.base.exp (prod .mul t.exps) = t := by
  rw [exps, prod_factors, exp_base_expo]

/-! ### Exponentiation as a group action -/

/-- Exponentiation: `a • g` raises `g` to the exponent `a`. -/
instance : SMul E G := ⟨fun a g => G.ofTerm ((g : Term).exp a)⟩

@[simp, norm_cast]
theorem ProdGroup.coe_smul (a : E) (g : G) : (↑(a • g) : Term) = (g : Term).exp a := rfl

@[rocq_alias cryptis.TExp_TGInv, rocq_alias cryptis.TExp_gunit]
instance : MulDistribMulAction E G where
  one_smul g := coe_injective (exp_unit g)
  mul_smul a b g := coe_injective <| by
    rw [coe_smul, coe_smul, coe_smul, exp_exp, add_comm]
    rfl
  smul_mul a x y := coe_injective <| by
    rw [coe_smul, coe_mul, exp_prod, SMS.map_add, SMS.map_singleton, SMS.map_singleton]
    rfl
  smul_one a := coe_injective (exp_prod_zero a)

#rocq_ignore cryptis.TExp_injl "MulAction.injective on Term.G"

@[simp, rocq_alias cryptis.TExpK]
theorem exp_exp_inv (u v : Term) : (u.exp v).exp (prod .mul (-{v})) = u :=
  congrArg ProdGroup.toTerm (inv_smul_smul (E.ofTerm v) (G.ofTerm u))

@[simp, rocq_alias cryptis.TExpKV]
theorem exp_inv_exp (u v : Term) : (u.exp (prod .mul (-{v}))).exp v = u :=
  congrArg ProdGroup.toTerm (smul_inv_smul (E.ofTerm v) (G.ofTerm u))

theorem exp_exp_coe_inv (u : Term) (a : E) : (u.exp a).exp ↑a⁻¹ = u := exp_exp_inv u a

theorem exp_coe_inv_exp (u : Term) (a : E) : (u.exp ↑a⁻¹).exp a = u := exp_inv_exp u a

@[rocq_alias cryptis.TExpC]
theorem exp_right_comm (g a b : Term) : (g.exp a).exp b = (g.exp b).exp a :=
  congrArg ProdGroup.toTerm (smul_comm (E.ofTerm b) (E.ofTerm a) (G.ofTerm g))

/-- The exponent of an exponential, as an element of `E`. -/
theorem ofTerm_expo_exp (h : b.isProd .gmul = false) (e : Term) :
    E.ofTerm (b.exp e).expo = E.ofTerm b.expo * E.ofTerm e := by
  rw [expo_exp h]
  rfl

@[simp, rocq_alias cryptis.is_gmul_TExp]
theorem isProd_exp (b e : Term) : (b.exp e).isProd .gmul = b.isProd .gmul := by
  cases h : b.isProd .gmul
  · exact isProd_exp_eq_false h e
  · by_contra h'
    have := isProd_exp_eq_false (b := b.exp e) (by simpa using h') (prod .mul (-{e}))
    rw [exp_exp_inv, h] at this
    cases this

@[rocq_alias cryptis.count_expo_TExp]
theorem count_expo_exp (h : b.isProd .gmul = false) (x e : Term) :
    count .mul x (b.exp e).expo = count .mul x b.expo + count .mul x e := by
  have := count_coe_mul x (E.ofTerm b.expo) (E.ofTerm e)
  rwa [← ofTerm_expo_exp h] at this

@[rocq_alias cryptis.count_expo_TExp_eq]
theorem count_expo_exp_self (hx : x.isProd .mul = false) (h : b.isProd .gmul = false) :
    count .mul x (b.exp x).expo = count .mul x b.expo + 1 := by
  simp [count_expo_exp h, count_self, hx]

@[rocq_alias cryptis.is_expE]
theorem isExp_iff_expo_ne : t.isExp ↔ t.expo ≠ prod .mul 0 := by
  rw [← isExp_unfold, ne_eq, ← unfold_inj, unfold_expo, unfold_prod_zero]
  have := wf_unfold t
  generalize t.unfold = pt at this
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> simp_all [PreTerm.isExp, PreTerm.expo]

@[rocq_alias cryptis.is_expNE]
theorem isExp_eq_false_iff : t.isExp = false ↔ t.expo = prod .mul 0 := by
  simpa using isExp_iff_expo_ne.not

@[rocq_alias cryptis.is_exp_of_exps]
theorem isExp_of_mem_exps (h : t' ∈ t.exps) : t.isExp := by
  refine isExp_iff_expo_ne.mpr fun he => ?_
  rw [exps, he, factors_prod_zero] at h
  simp [← SMS.mem_elements] at h

@[rocq_alias cryptis.count_expo_TExp_gt0]
theorem count_expo_exp_self_pos_iff :
    0 < count .mul x (b.exp x).expo ↔
      x.isProd .mul = false ∧ b.isProd .gmul = false ∧ 0 ≤ count .mul x b.expo := by
  constructor
  · intro h
    have hm : x ∈ (b.exp x).exps := count_ne_zero_iff.mp h.ne'
    have hx := isProd_of_mem_factors hm
    have hb : b.isProd .gmul = false := by
      rw [← isProd_exp b x]
      exact isProd_eq_false_of_isExp _ (isExp_of_mem_exps hm)
    rw [count_expo_exp_self hx hb] at h
    exact ⟨hx, hb, by omega⟩
  · rintro ⟨hx, hb, h⟩
    rw [count_expo_exp_self hx hb]
    omega

@[rocq_alias cryptis.TExp_TMul_cons_l]
theorem exp_prod_make_cons_left (t x : Term) (X Y : Multiset Term) :
    t.exp (prod .mul (.make (x ::ₘ X) Y)) = (t.exp (prod .mul (.make X Y))).exp x := by
  rw [exp_exp]
  exact congrArg _ (factors_injective .mul (by simp [SMS.bind_make_cons_left, add_comm]))

@[rocq_alias cryptis.TExp_TMul_cons_r]
theorem exp_prod_make_cons_right (t y : Term) (X Y : Multiset Term) :
    t.exp (prod .mul (.make X (y ::ₘ Y))) =
      (t.exp (prod .mul (.make X Y))).exp (prod .mul (-{y})) := by
  rw [exp_exp]
  exact congrArg _ (factors_injective .mul (by simp [SMS.bind_make_cons_right, add_comm]))

@[rocq_alias cryptis.exps_TExp_TMul]
theorem exps_exp_prod (hx : t.isExp = false) (hg : t.isProd .gmul = false)
    (hs : ∀ u ∈ s, u.isProd .mul = false) : (t.exp (prod .mul s)).exps = s := by
  rw [exps_exp hx hg, factors_prod_of_forall hs]

/-! ### Signed atoms -/

/-- The elements of `s` as signed atoms: `x` for a positive occurrence of `x`, and `x⁻¹` for a
negative one. -/
@[rocq_alias cryptis.satoms]
def satoms (s : SMS Term) : Multiset E :=
  s.posPart.map E.ofTerm + s.negPart.map fun x => (E.ofTerm x)⁻¹

/-- The multiplicity of the signed atom `f` in `t`. -/
@[rocq_alias cryptis.scount]
def scount (f : E) (t : Term) : ℤ := count .mul f t - count .mul ↑f⁻¹ t

variable {f g : E}

@[simp, rocq_alias cryptis.scount_TInv_l]
theorem scount_inv_left (f : E) (t : Term) : scount f⁻¹ t = -scount f t := by
  simp only [scount, inv_inv]
  omega

@[simp, rocq_alias cryptis.scount_TInv_r]
theorem scount_inv_right (f a : E) : scount f ↑a⁻¹ = -scount f a := by
  simp only [scount, count_coe_inv]
  omega

@[rocq_alias cryptis.scount_Nmul]
theorem scount_of_isProd_eq_false (h : (f : Term).isProd .mul = false) (t : Term) :
    scount f t = count .mul f t := by
  rw [scount, count_of_isProd (isProd_coe_inv h), sub_zero]

@[rocq_alias cryptis.scount_expo_TExp]
theorem scount_expo_exp (h : b.isProd .gmul = false) (f : E) (e : Term) :
    scount f (b.exp e).expo = scount f b.expo + scount f e := by
  simp only [scount, count_expo_exp h]
  omega

@[rocq_alias cryptis.elem_of_satoms]
theorem mem_satoms : f ∈ satoms (t.factors .mul) ↔ 0 < scount f t := by
  rw [satoms, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map, scount]
  cases hf : (f : Term).isProd .mul
  · rw [count_of_isProd (isProd_coe_inv hf), sub_zero, count_pos_iff]
    refine ⟨?_, fun h => .inl ⟨_, h, rfl⟩⟩
    rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hx
    · simp [isProd_prod_neg_singleton (isProd_of_mem_factors (SMS.mem_of_mem_negPart hx))] at hf
  · rw [count_of_isProd hf, zero_sub, neg_pos, count_neg_iff]
    refine ⟨?_, fun h => .inr ⟨↑f⁻¹, h, inv_inv f⟩⟩
    rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · simp [isProd_of_mem_factors (SMS.mem_of_mem_posPart hx)] at hf
    · rwa [inv_inv]

@[rocq_alias cryptis.elem_of_satoms_TInv]
theorem inv_mem_satoms (h : x.isProd .mul = false) :
    (E.ofTerm x)⁻¹ ∈ satoms (t.factors .mul) ↔ x ∈ (t.factors .mul).negPart := by
  rw [mem_satoms, scount_inv_left, scount_of_isProd_eq_false (f := E.ofTerm x) h, neg_pos,
    coe_ofTerm, count_neg_iff]

@[rocq_alias cryptis.is_exp_of_satoms]
theorem isExp_of_mem_satoms (h : f ∈ satoms t.exps) : t.isExp := by
  rcases Multiset.mem_add.mp h with h | h <;> obtain ⟨x, hx, -⟩ := Multiset.mem_map.mp h
  exacts [isExp_of_mem_exps (SMS.mem_of_mem_posPart hx),
    isExp_of_mem_exps (SMS.mem_of_mem_negPart hx)]

@[rocq_alias cryptis.satoms_satom]
theorem isProd_or_of_mem_satoms (h : f ∈ satoms (t.factors .mul)) :
    (f : Term).isProd .mul = false ∨ (↑f⁻¹ : Term).isProd .mul = false := by
  rcases Multiset.mem_add.mp h with h | h <;> obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp h
  · exact .inl (isProd_of_mem_factors (SMS.mem_of_mem_posPart hx))
  · exact .inr (by rw [inv_inv]; exact isProd_of_mem_factors (SMS.mem_of_mem_negPart hx))

@[rocq_alias cryptis.scount_satom_diag]
theorem scount_self (h : (f : Term).isProd .mul = false ∨ (↑f⁻¹ : Term).isProd .mul = false) :
    scount f f = 1 := by
  rcases h with h | h
  · rw [scount_of_isProd_eq_false h, count_self_of_isProd_eq_false h]
  · rw [← inv_inv f, scount_inv_left, scount_inv_right, neg_neg, scount_of_isProd_eq_false h,
      count_self_of_isProd_eq_false h]

@[rocq_alias cryptis.scount_satom_ne]
theorem scount_eq_zero (hf : (f : Term).isProd .mul = false ∨ (↑f⁻¹ : Term).isProd .mul = false)
    (h₁ : g ≠ f) (h₂ : g ≠ f⁻¹) : scount g f = 0 := by
  rcases hf with hf | hf
  · rw [scount, count_of_ne hf (coe_injective.ne h₁),
      count_of_ne hf (coe_injective.ne fun h => h₂ (by rw [← h, inv_inv])), sub_zero]
  · rw [← inv_inv f, scount_inv_right, scount, count_of_ne hf (coe_injective.ne h₂),
      count_of_ne hf (coe_injective.ne (inv_injective.ne h₁)), sub_zero, neg_zero]

/-! ### Group factors of powers -/

theorem exp_left_injective (e : Term) : Function.Injective fun t : Term => t.exp e :=
  fun _ _ h => ofTerm_injective (o := .gmul) <| MulAction.injective (E.ofTerm e) <|
    coe_injective h

@[simp, rocq_alias cryptis.gcount_TExp_cong]
theorem count_exp_exp (z u c : Term) : count .gmul (z.exp c) (u.exp c) = count .gmul z u := by
  rw [count, factors_exp, SMS.count_map_of_injective (exp_left_injective c), count]

@[rocq_alias cryptis.gcount_TExp_no_preimage]
theorem count_exp_eq_zero {Y c : Term} (h : ∀ u ∈ Y.factors .gmul, u.exp c ≠ t) :
    count .gmul t (Y.exp c) = 0 := by
  refine SMS.count_eq_zero_of_not_mem fun ht => ?_
  rw [factors_exp] at ht
  obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map ht
  exact h u hu rfl

/-- A group factor of `Y` whose exponent has the most occurrences of `x` cannot be the image of
another factor under an exponent with fewer occurrences of `x`. -/
@[rocq_alias cryptis.gcount_TExp_max]
theorem exists_count_exp_eq_zero (x : Term) {Y : Term} (h : Y ≠ prod .gmul 0) :
    ∃ w ∈ Y.factors .gmul, ∀ e₁ e₂, count .mul x e₁ < count .mul x e₂ →
      count .gmul (w.exp e₂) (Y.exp e₁) = 0 := by
  rcases SMS.exists_max_or_eq_zero (fun u => count .mul x u.expo) (Y.factors .gmul) with
    ⟨w, hw, hmax⟩ | h0
  · refine ⟨w, hw, fun e₁ e₂ hlt => count_exp_eq_zero fun u hu he => ?_⟩
    have := congrArg (fun v => count .mul x v.expo) he
    simp only [count_expo_exp (isProd_of_mem_factors hu),
      count_expo_exp (isProd_of_mem_factors hw)] at this
    have := hmax u hu
    omega
  · exact absurd (factors_eq_zero_iff.mp h0) h

/-- Exponentiation is injective in the exponent, except at the unit of `G`, which every exponent
fixes. -/
@[rocq_alias cryptis.TExp_injr]
theorem G.smul_left_injective {g : G} (h : g ≠ 1) : Function.Injective fun a : E => a • g := by
  intro e₁ e₂ he
  refine coe_injective (ext_count (o := .mul) fun x _ => ?_)
  obtain ⟨w, hw, hmax⟩ := exists_count_exp_eq_zero x (coe_injective.ne h)
  have hne : count .gmul w g ≠ 0 := count_ne_zero_iff.mpr hw
  have he : (g : Term).exp e₁ = (g : Term).exp e₂ := congrArg ProdGroup.toTerm he
  rcases lt_trichotomy (count .mul x e₁) (count .mul x e₂) with hlt | heq | hgt
  · exact absurd (by rw [← count_exp_exp w g e₂, ← he, hmax _ _ hlt]) hne
  · exact heq
  · exact absurd (by rw [← count_exp_exp w g e₁, he, hmax _ _ hgt]) hne

theorem G.smul_left_inj {g : G} (h : g ≠ 1) {a b : E} : a • g = b • g ↔ a = b :=
  (smul_left_injective h).eq_iff

end Term
end Cryptis
