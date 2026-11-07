module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.RepresentationTheory.Basic
public import Cryptis.Core.Term.Subterms
import Mathlib.Tactic.Group

/-! Extended exponents.

An extended exponent (`EExp`) is a formal sum of exponents: an element of the group ring
`MonoidAlgebra ℤ Term.E` of the exponent group. The exponent group is free abelian, so it has
unique products and `EExp` is a domain.

The Diffie-Hellman group, written additively, is a module over this ring: `s • x` raises `x` to
the sum `s`, the product of the powers of `x` by the monomials of `s`. Conversely, `log g x`
reads off the exponent of the base `g` in `x`: the sum of the exponents `e` of the group factors
`g^e` of `x`. Logarithms are linear (`Term.log` is a linear map) and determine an element of the
group (`Term.ext_log`), so the module is torsion-free.

Equations between terms thus become equations between their logarithms. `IsHomogeneous h k s`
says that every monomial of `s` has exactly `k` occurrences of `h`, and parts with different
counts can be compared separately (`IsHomogeneous.eq_of_add_eq_add`). For HMQV, the remaining
algebraic step is `eq_zero_of_add_mul_eq_add_mul`: an `h`-independent remainder cannot be a
multiple of `h * u - v`, as substituting `v / u` for `h` (`substFactor`) shows. -/

@[expose] public section
namespace Cryptis

/-! ### Signed multisets as finitely supported functions -/

namespace SMS

variable {T : Type _} [DecidableEq T]

/-- A signed multiset as the finitely supported function of its multiplicities. -/
noncomputable def toFinsupp : SMS T →+ (T →₀ ℤ) where
  toFun s := .onFinset s.elements.toFinset s.count fun _ hx =>
    Multiset.mem_toFinset.mpr (mem_iff_count_ne_zero.mpr hx)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

@[simp]
theorem toFinsupp_apply (s : SMS T) (x : T) : s.toFinsupp x = s.count x := rfl

theorem toFinsupp_injective : Function.Injective (toFinsupp (T := T)) :=
  fun _ _ h => ext fun x => by simpa using DFunLike.congr_fun h x

instance : UniqueSums (SMS T) :=
  .of_injective_addHom toFinsupp.toAddHom toFinsupp_injective inferInstance

end SMS

namespace Term

open ProdGroup

instance {o : TermOpN} : UniqueProds (ProdGroup o) :=
  .of_injective_mulHom factorsHom.toMulHom factorsHom_injective inferInstance

end Term

open Term Term.ProdGroup MonoidAlgebra

/-! ### The ring of extended exponents -/

/-- Extended exponents: formal sums of exponents, the group ring of `Term.E`. -/
@[rocq_alias cryptis.eexp]
abbrev EExp := MonoidAlgebra ℤ E

namespace EExp

instance : IsDomain EExp := NoZeroDivisors.to_isDomain _

#rocq_ignore cryptis.emul "The multiplication of MonoidAlgebra ℤ Term.E"
#rocq_ignore cryptis.emul1 "MonoidAlgebra.single_mul_single"
#rocq_ignore cryptis.emul_singleton "MonoidAlgebra.single_mul_single"
#rocq_ignore cryptis.emul_empty_l "Mathlib's zero_mul on EExp"
#rocq_ignore cryptis.emul_empty_r "Mathlib's mul_zero on EExp"
#rocq_ignore cryptis.emul_disj_union_l "Mathlib's add_mul on EExp"
#rocq_ignore cryptis.emul_disj_union_r "Mathlib's mul_add on EExp"
#rocq_ignore cryptis.emul_inv_r "Mathlib's mul_neg on EExp"
#rocq_ignore cryptis.emul_comm "Mathlib's mul_comm on EExp"
#rocq_ignore cryptis.emul1A "Mathlib's mul_assoc on EExp"
#rocq_ignore cryptis.count_emul1 "MonoidAlgebra.coeff_mul_single_apply"
#rocq_ignore cryptis.emul1_inj "Mathlib's mul_right_cancel₀ on EExp"
#rocq_ignore cryptis.emul1_eq0 "Mathlib's mul_eq_zero on EExp"
#rocq_ignore cryptis.emul_neq0 "Mathlib's mul_ne_zero on EExp, from IsDomain EExp"
#rocq_ignore cryptis.emul_injr "Mathlib's mul_left_cancel₀ on EExp, from IsDomain EExp"

/-! ### Extended exponents act on the group -/

/-- `s • x` raises `x` to the extended exponent `s`: the linear extension of exponentiation. -/
noncomputable instance : Module EExp (Additive G) :=
  Module.compHom _ (Representation.ofMulDistribMulAction E G).asAlgebraHom.toRingHom

theorem single_smul (a : E) (n : ℤ) (x : Additive G) :
    (single a n : EExp) • x = n • Additive.ofMul (a • x.toMul) := by
  change (Representation.ofMulDistribMulAction E G).asAlgebraHom (single a n) x = _
  simp

@[simp]
theorem of_smul (a : E) (x : Additive G) : of ℤ E a • x = .ofMul (a • x.toMul) := by
  simp [single_smul]

#rocq_ignore cryptis.epow "The scalar multiplication of Module EExp (Additive Term.G)"
#rocq_ignore cryptis.epow2 "Mathlib's add_smul, with EExp.of_smul"
#rocq_ignore cryptis.epow_unit "Mathlib's smul_zero on Additive Term.G"
#rocq_ignore cryptis.epowA "Mathlib's mul_smul on Additive Term.G"

end EExp

/-! ### Logarithms -/

namespace Term

variable {g t u h n : Term} {x y : Additive G}

/-- The exponents of the group factors of `t` whose base is `g`. -/
noncomputable def logAux (g t : Term) : EExp :=
  (t.factors .gmul).sum fun u => if u.base = g then single (E.ofTerm u.expo) 1 else 0

theorem logAux_exp (g t : Term) (a : E) : logAux g (t.exp ↑a) = of ℤ E a * logAux g t := by
  rw [logAux, logAux, factors_exp, SMS.sum_map]
  refine Eq.trans ?_ (SMS.map_sum (AddMonoidHom.mulLeft (of ℤ E a)) _ _).symm
  refine SMS.sum_congr fun u hu => ?_
  have hu := isProd_of_mem_factors hu
  simp only [Function.comp_apply, base_exp hu, AddMonoidHom.coe_mulLeft, ofTerm_expo_exp hu,
    ofTerm_coe]
  split_ifs <;> simp [single_mul_single, mul_comm]

/-- `logAux g` on the group, as an additive homomorphism. -/
noncomputable def logHom (g : Term) : Additive G →+ EExp where
  toFun x := logAux g ↑x.toMul
  map_zero' := by simp [logAux]
  map_add' x y := by simp [logAux]

/-- The exponent of the base `g` in `x`: the sum of the exponents of the group factors of `x`
with base `g`. Logarithms are linear over the extended exponents. -/
@[rocq_alias cryptis.log]
noncomputable def log (g : Term) : Additive G →ₗ[EExp] EExp where
  __ := logHom g
  map_smul' s x := by
    change logHom g (s • x) = s * logHom g x
    induction s using MonoidAlgebra.induction_on with
    | of a => exact (congrArg (logHom g) (EExp.of_smul a x)).trans (logAux_exp g _ a)
    | add s r hs hr => rw [add_smul, map_add, hs, hr, add_mul]
    | smul n s hs => rw [smul_assoc, map_zsmul, hs, smul_mul_assoc]

theorem log_apply (g : Term) (x : Additive G) : log g x = logAux g ↑x.toMul := rfl

theorem coeff_log (g : Term) (x : Additive G) (e : E) :
    (log g x).coeff e =
      ((x.toMul : Term).factors .gmul).sum fun u => if u.base = g ∧ E.ofTerm u.expo = e then 1
        else 0 := by
  refine (SMS.map_sum ((Finsupp.applyAddHom e).comp
    (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := E)).toAddMonoidHom) _ _).trans
    (SMS.sum_congr fun u _ => ?_)
  by_cases hb : u.base = g <;> simp [hb, Finsupp.single_apply, MonoidAlgebra.coeffAddEquiv]

/-- The coefficient of `e` in `log g x` is the multiplicity of `g^e` in `x`. -/
@[rocq_alias cryptis.count_log]
theorem coeff_log_eq_count (hx : g.isExp = false) (hg : g.isProd .gmul = false) (e : E)
    (x : Additive G) :
    (log g x).coeff e = count .gmul (g.exp ↑e) ↑x.toMul := by
  rw [coeff_log, count, SMS.count_eq_sum]
  refine SMS.sum_congr fun u hu => ?_
  have hne : G.ofTerm g ≠ 1 := fun h => ne_prod_zero hg (congrArg toTerm h)
  by_cases hb : u.base = g
  · have hu : E.ofTerm u.expo • G.ofTerm g = G.ofTerm u := by
      rw [← hb]
      exact coe_injective (exp_base_expo u)
    have : u = g.exp ↑e ↔ E.ofTerm u.expo = e := by
      rw [← G.smul_left_inj hne, hu]
      exact ⟨fun h => coe_injective h, fun h => congrArg toTerm h⟩
    simp [hb, this]
  · have : (g.exp ↑e).base ≠ u.base := by rwa [base_exp hg, base_eq_self hx, ne_comm]
    simp [hb, ne_of_apply_ne base this |>.symm]

@[rocq_alias cryptis.log_inj]
theorem ext_log (h : ∀ g, log g x = log g y) : x = y := by
  refine Additive.toMul.injective (coe_injective (ext_count (o := .gmul) fun u hu => ?_))
  have hg : u.base.isProd .gmul = false := by rwa [isProd_base]
  have := congrArg (·.coeff (E.ofTerm u.expo)) (h u.base)
  simp only [coeff_log_eq_count (isExp_base u) hg, exp_base_expo] at this
  exact this

@[rocq_alias cryptis.log_eq0]
theorem eq_zero_of_forall_log_eq_zero (h : ∀ g, log g x = 0) : x = 0 :=
  ext_log fun g => by rw [h, map_zero]

@[rocq_alias cryptis.log_neq0]
theorem exists_log_ne_zero (h : x ≠ 0) : ∃ g, log g x ≠ 0 := by
  by_contra! h'
  exact h (eq_zero_of_forall_log_eq_zero h')

#rocq_ignore cryptis.log_TGMul "map_add of the linear map Term.log, with ProdGroup.ofTerm_prod"
#rocq_ignore cryptis.log_TGMul2 "map_add of the linear map Term.log"
#rocq_ignore cryptis.log_unit "map_zero of the linear map Term.log"
#rocq_ignore cryptis.log_TExp "map_smul of the linear map Term.log, with EExp.of_smul"
#rocq_ignore cryptis.log_epow "map_smul of the linear map Term.log"

@[rocq_alias cryptis.log_atom]
theorem log_ofTerm (hx : u.isExp = false) (hg : u.isProd .gmul = false) (g : Term) :
    log g (.ofMul (G.ofTerm u)) = if u = g then 1 else 0 := by
  rw [log_apply, logAux, toMul_ofMul, coe_ofTerm, factors_eq_singleton hg, SMS.sum_singleton,
    base_eq_self hx, expo_eq_unit hx]
  rfl

@[rocq_alias cryptis.log_TExp_atom]
theorem log_smul_ofTerm (hx : u.isExp = false) (hg : u.isProd .gmul = false) (g : Term) (a : E) :
    log g (.ofMul (a • G.ofTerm u)) = if u = g then of ℤ E a else 0 := by
  rw [← toMul_ofMul (G.ofTerm u), ← EExp.of_smul, map_smul, log_ofTerm hx hg]
  split_ifs <;> simp

@[rocq_alias cryptis.log_TExp_g]
theorem log_exp (hx : g.isExp = false) (hg : g.isProd .gmul = false) (e : Term) :
    log g (.ofMul (G.ofTerm (g.exp e))) = of ℤ E (E.ofTerm e) :=
  (log_smul_ofTerm hx hg g (E.ofTerm e)).trans (ite_eq_left rfl)

/-- A positive coefficient of a logarithm is a positive group factor. -/
theorem exp_mem_factors_of_coeff_log_pos (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    {x : G} {e : E} (h : 0 < (log g (.ofMul x)).coeff e) :
    g.exp ↑e ∈ ((x : Term).factors .gmul).posPart :=
  count_pos_iff.mp (by rwa [coeff_log_eq_count hx hg, toMul_ofMul] at h)

instance : Module.IsTorsionFree EExp (Additive G) :=
  Function.Injective.moduleIsTorsionFree (fun x g => log g x)
    (fun _ _ h => ext_log (congrFun h)) fun s x => funext fun g => map_smul (log g) s x

#rocq_ignore cryptis.epow_injl
  "smul_right_injective, from Module.IsTorsionFree EExp (Additive Term.G)"

/-- Substitute `u` for the factor `h` of an exponent. Other factors, including hashes that
contain `h`, are unchanged. -/
@[rocq_alias cryptis.msubst]
noncomputable def substFactor (h u : Term) : E →* E :=
  (SMS.prodHom fun a => E.ofTerm (if a = h then u else a)).comp factorsHom

#rocq_ignore cryptis.msubst_mul "map_mul of the homomorphism Term.substFactor"

@[simp, rocq_alias cryptis.msubst_diag]
theorem substFactor_self (hh : h.isProd .mul = false) (u : Term) :
    substFactor h u (E.ofTerm h) = E.ofTerm u := by
  simp [substFactor, factors_eq_singleton hh]

@[rocq_alias cryptis.msubst_indep]
theorem substFactor_of_count_eq_zero {m : E} (hm : count .mul h ↑m = 0) (u : Term) :
    substFactor h u m = m := by
  have : ((m : Term).factors .mul).prod (fun a => E.ofTerm (if a = h then u else a)) =
      ((m : Term).factors .mul).prod ProdGroup.ofTerm := SMS.prod_congr fun a ha => by
    refine congrArg _ (ite_eq_right_iff.mpr ?_)
    rintro rfl
    exact absurd hm (count_ne_zero_iff.mpr ha)
  simp only [substFactor, MonoidHom.coe_comp, Function.comp_apply, factorsHom_apply,
    SMS.prodHom_apply, toAdd_ofAdd, this, ← ofTerm_prod, prod_factors, ofTerm_coe]

end Term

/-! ### Homogeneous parts and substitution -/

namespace EExp

variable {s r r₁ r₂ s₁ s₂ : EExp} {h n t : Term} {u v e e₀ e₁ m : E} {a b k : ℤ}

/-- Every monomial of `s` has exactly `k` occurrences of `h`. For `k = 0`, `s` is independent of
`h`. -/
@[rocq_alias cryptis.ehom]
def IsHomogeneous (h : Term) (k : ℤ) (s : EExp) : Prop :=
  ∀ m ∈ s.coeff.support, count .mul h ↑m = k

@[simp, rocq_alias cryptis.ehom_empty]
theorem isHomogeneous_zero (h : Term) (k : ℤ) : IsHomogeneous h k 0 := by
  simp [IsHomogeneous]

@[simp, rocq_alias cryptis.ehom_singleton]
theorem isHomogeneous_of : IsHomogeneous h k (of ℤ E e) ↔ count .mul h ↑e = k := by
  simp [IsHomogeneous, of_apply, coeff_single]

namespace IsHomogeneous

@[rocq_alias cryptis.ehom_add]
theorem add (hs : IsHomogeneous h k s) (hr : IsHomogeneous h k r) : IsHomogeneous h k (s + r) :=
  fun m hm => (Finset.mem_union.mp (Finsupp.support_add hm)).elim (hs m) (hr m)

@[rocq_alias cryptis.ehom_emul]
theorem mul (hs : IsHomogeneous h a s) (hr : IsHomogeneous h b r) :
    IsHomogeneous h (a + b) (s * r) := fun m hm => by
  classical
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_mul.mp (support_coeff_mul_subset s r hm)
  rw [count_coe_mul, hs m₁ hm₁, hr m₂ hm₂]

@[rocq_alias cryptis.ehom_count]
theorem coeff_eq_zero (hs : IsHomogeneous h k s) (hm : count .mul h ↑m ≠ k) :
    s.coeff m = 0 :=
  Finsupp.notMem_support_iff.mp fun h' => hm (hs m h')

/-- Parts with different counts of `h` can be compared separately. -/
@[rocq_alias cryptis.ehom_split]
theorem eq_of_add_eq_add (hs₁ : IsHomogeneous h a s₁) (hr₁ : IsHomogeneous h a r₁)
    (hs₂ : IsHomogeneous h b s₂) (hr₂ : IsHomogeneous h b r₂) (hab : a ≠ b)
    (hsr : s₁ + s₂ = r₁ + r₂) : s₂ = r₂ := by
  refine coeff_injective (Finsupp.ext fun m => ?_)
  have := congrArg (·.coeff m) hsr
  simp only [coeff_add, Finsupp.add_apply] at this
  by_cases hm : count .mul h ↑m = b
  · rw [hs₁.coeff_eq_zero (hm ▸ hab.symm), hr₁.coeff_eq_zero (hm ▸ hab.symm)] at this
    simpa using this
  · rw [hs₂.coeff_eq_zero hm, hr₂.coeff_eq_zero hm]

@[rocq_alias cryptis.ehom_binomial_const]
theorem eq_zero_of_mul_add_eq (hs : IsHomogeneous h 0 s) (hr : IsHomogeneous h 0 r)
    (he₀ : count .mul h ↑e₀ = 0) (he₁ : count .mul h ↑e₁ ≠ 0)
    (hsr : s * (of ℤ E e₀ + of ℤ E e₁) = r) : s = 0 := by
  rw [mul_add, ← add_zero r] at hsr
  have := (hs.mul (isHomogeneous_of.mpr he₀)).eq_of_add_eq_add hr
    (hs.mul (isHomogeneous_of.mpr rfl)) (isHomogeneous_zero _ _) (by simpa using he₁.symm) hsr
  simpa [of_apply, mul_eq_zero] using this

end IsHomogeneous

@[rocq_alias cryptis.ehom_log]
theorem isHomogeneous_log {x : Additive G} {k : ℤ}
    (H : ∀ u ∈ (x.toMul : Term).factors .gmul, count .mul h u.expo = k) (g : Term) :
    IsHomogeneous h k (log g x) := fun m hm => by
  rw [Finsupp.mem_support_iff, coeff_log] at hm
  by_contra hne
  refine hm (SMS.sum_eq_zero fun u hu => ite_eq_right_iff.mpr ?_)
  rintro ⟨-, rfl⟩
  exact absurd (H u hu) hne

/-- The logarithms of `t` are independent of atoms too large to occur in its exponents. -/
@[rocq_alias cryptis.ehom_log_small]
theorem isHomogeneous_log_of_tsize_le (hle : t.tsize ≤ h.tsize) (g : Term) :
    IsHomogeneous h 0 (log g (.ofMul (G.ofTerm t))) :=
  isHomogeneous_log (fun _ hu => count_expo_eq_zero_of_tsize_le hu hle) g

/-- The logarithms of `t` are independent of atoms with a subterm that does not occur in `t`. -/
@[rocq_alias cryptis.ehom_log_fresh]
theorem isHomogeneous_log_of_subterm (hn : n.Subterm h) (ht : ¬n.Subterm t) (g : Term) :
    IsHomogeneous h 0 (log g (.ofMul (G.ofTerm t))) :=
  isHomogeneous_log (fun _ hu => count_eq_zero_of_not_mem fun hh =>
    ht (Subterm.of_mem_factors hu (hn.trans (Subterm.of_mem_exps hh)))) g

@[rocq_alias cryptis.indep_log_TExp_g]
theorem isHomogeneous_log_exp {g e : Term} (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (he : count .mul h e = 0) (b : Term) :
    IsHomogeneous h 0 (log b (.ofMul (G.ofTerm (g.exp e)))) := by
  rw [show G.ofTerm (g.exp e) = E.ofTerm e • G.ofTerm g from rfl, log_smul_ofTerm hx hg]
  split_ifs
  exacts [isHomogeneous_of.mpr he, isHomogeneous_zero _ _]

#rocq_ignore cryptis.emul1_max "Only used for cancellation, which follows from IsDomain EExp"
#rocq_ignore cryptis.emul_binomial_eq0 "Mathlib's mul_eq_zero on EExp"
#rocq_ignore cryptis.emul1_apart "Mathlib's mul_left_cancel₀ on EExp, with of_injective"

/-- Substitute `u` for the factor `h` in every monomial. -/
@[rocq_alias cryptis.esubst]
noncomputable def substFactor (h u : Term) : EExp →+* EExp :=
  mapDomainRingHom ℤ (Term.substFactor h u)

#rocq_ignore cryptis.esubst_add "map_add of the ring homomorphism EExp.substFactor"
#rocq_ignore cryptis.esubst_emul1 "map_mul of the ring homomorphism EExp.substFactor"

@[simp]
theorem substFactor_of (h u : Term) (e : E) :
    substFactor h u (of ℤ E e) = of ℤ E (Term.substFactor h u e) := by
  simp [substFactor, of_apply, mapDomainRingHom, mapDomain_single]

@[rocq_alias cryptis.esubst_indep]
theorem substFactor_of_isHomogeneous (hs : IsHomogeneous h 0 s) (u : Term) :
    substFactor h u s = s := by
  refine coeff_injective ?_
  change Finsupp.mapDomain _ s.coeff = s.coeff
  rw [Finsupp.mapDomain_congr (v := s.coeff) (g := id)
    fun m hm => Term.substFactor_of_count_eq_zero (hs m hm) u, Finsupp.mapDomain_id]

/-- An `h`-independent difference cannot be a multiple of `h * u - v`: substitute `v / u` for `h`
to equate the remainders, then cancel. -/
@[rocq_alias cryptis.emul_linear]
theorem eq_zero_of_add_mul_eq_add_mul (hh : h.isProd .mul = false)
    (hu : count .mul h ↑u = 0) (hv : count .mul h ↑v = 0)
    (hr₁ : IsHomogeneous h 0 r₁) (hr₂ : IsHomogeneous h 0 r₂)
    (hsr : r₁ + s * of ℤ E (E.ofTerm h * u) = r₂ + s * of ℤ E v) : s = 0 := by
  have hsub : Term.substFactor h ↑(v * u⁻¹) (E.ofTerm h * u) = v := by
    rw [map_mul (Term.substFactor _ _), Term.substFactor_self hh,
      Term.substFactor_of_count_eq_zero hu]
    exact inv_mul_cancel_right v u
  have hr : r₁ = r₂ := by
    have := congrArg (substFactor h ↑(v * u⁻¹)) hsr
    rwa [map_add, map_add, map_mul (substFactor _ _), map_mul (substFactor _ _), substFactor_of,
      substFactor_of, hsub,
      Term.substFactor_of_count_eq_zero hv, substFactor_of_isHomogeneous hr₁,
      substFactor_of_isHomogeneous hr₂, add_left_inj] at this
  subst hr
  by_contra hs
  have := of_injective (mul_left_cancel₀ hs (add_left_cancel hsr))
  have := congrArg (fun a : E => count .mul h a) this
  simp [count_self_of_isProd_eq_false hh, hu, hv] at this

#rocq_ignore cryptis.dpart "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.count_dpart "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.elem_of_dpart "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.dpart_neq0 "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.dpart_empty "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.dpart_bind "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.bind_dpart "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.dpart_emul1 "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.dpart_emul "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.count_emul_mono "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.sms_witness "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.agree "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.agree_dpart "Cancellation follows from IsDomain EExp"
#rocq_ignore cryptis.emul_neq0_agree "Cancellation follows from IsDomain EExp"

/-! ### Examples

The usual tactics work on these structures: `group` in `Term.E` and `Term.G`, `abel` on the
group written additively, and `ring` on extended exponents. Inside Cryptis, Iris-Lean's camera
operation is also written `•`, with a lower precedence, so products of powers need parentheses. -/

section Examples

example (a b : E) (g : G) : a • b • g = (a * b) • g := (mul_smul a b g).symm

example (x y : G) (a b : E) :
    (a * b)⁻¹ • (x * y⁻¹) = (b⁻¹ • a⁻¹ • x) * (b⁻¹ • a⁻¹ • y)⁻¹ := by
  simp only [smul_mul', smul_inv', mul_smul, mul_inv_rev]

example (a b c : E) : (a * b * c)⁻¹ * a = (b * c)⁻¹ := by group

/-- An HMQV-style key: `g ^ (x * (a * e))` combined with `Y ^ e`. -/
example (g Y : G) (x a e : E) :
    ((x * (a * e)) • g) * (e • Y) = (x • a • e • g) * (e • Y) := by
  simp only [mul_smul]

example (x y : Additive G) (s r : EExp) :
    (s • (x + y)) - (r • x) = ((s - r) • x) + (s • y) := by
  rw [sub_smul, smul_add]
  abel

example (s r : EExp) : (s + r) * (s - r) = s * s - r * r := by ring

end Examples

end EExp
end Cryptis
