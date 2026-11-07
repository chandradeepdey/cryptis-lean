module

public import Mathlib.Data.Multiset.Sort
public import Cryptis.Lib.SMS
public import Cryptis.Core.PreTerm.WithStdpp

/-! Normalization of pre-terms.

Cryptis models Diffie–Hellman key exchange with two commutative groups: the exponents, under
the scalar product, and the Diffie–Hellman values, under the group product. Exponentiation raises
a value to an exponent. It multiplies iterated exponents, `(g ^ a) ^ b = g ^ (a * b)`, leaves a
value unchanged under the unit exponent, and distributes over group products,
`(u ⋅ v) ^ x = u ^ x ⋅ v ^ x`. Many pre-terms denote the same message under these equations;
`normalize` picks one of them, and `wf` says when a pre-term is in normal form.

- Recognisers test for exponentials, products and nonces.
- Products as signed multisets: a product is read as a signed multiset of factors, and built back
  as a pre-term with sorted factor lists, so that each product has a single representation. One
  definition covers both kinds of product, chosen by the operator `o`.
- Normal forms: the base of an exponential is neither an exponential nor a group product, and its
  exponent is not the unit; a product has sorted factor lists with no common factor, is not a
  single factor, and has no factor that is a product of the same kind.
- Factors, products and exponentials: the smart constructors build normal forms from normal
  forms.
- Normalization produces normal forms, and leaves them unchanged.
- The exponentiation laws, on normal pre-terms.

The group laws themselves are proved for terms, in `Cryptis.Core.Term.Algebra`. -/

@[expose] public section
namespace Cryptis
namespace PreTerm

/-- The height of a pre-term. -/
@[rocq_alias cryptis.PreTerm.height]
def height : PreTerm → Nat
  | op0 _ => 1
  | op1 _ t => t.height + 1
  | op2 _ t₁ t₂ => max t₁.height t₂.height + 1
  | opN _ ps ns => max ((ps.map height).foldr max 0) ((ns.map height).foldr max 0) + 1

/-! ### Recognisers -/

@[rocq_alias cryptis.PreTerm.is_exp]
def isExp : PreTerm → Bool
  | ptExp _ _ => true
  | _ => false

/-- Whether a pre-term is a product of kind `o`: a scalar product for `.mul`, a group product for
`.gmul`. -/
@[rocq_alias cryptis.PreTerm.is_mul, rocq_alias cryptis.PreTerm.is_gmul]
def isProd (o : TermOpN) : PreTerm → Bool
  | opN o' _ _ => decide (o' = o)
  | _ => false

@[rocq_alias cryptis.PreTerm.is_nonce]
def isNonce : PreTerm → Bool
  | op0 (.nonce _) => true
  | _ => false

/-- Exponentials and products: the heads that terms hold as normal pre-terms. -/
@[rocq_alias cryptis.PreTerm.is_non_free]
def isNonFree (pt : PreTerm) : Bool := pt.isExp || pt.isProd .mul || pt.isProd .gmul

/-- The heads that the base of a normal exponential may not have. A scalar product in a base is
an atom, since exponentiation does not distribute over it. -/
@[rocq_alias cryptis.PreTerm.is_gnon_free]
def isGNonFree (pt : PreTerm) : Bool := pt.isExp || pt.isProd .gmul

variable {o : TermOpN} {pt t b e : PreTerm} {ps ns : List PreTerm} {s : SMS PreTerm}

theorem isExp_iff : pt.isExp ↔ ∃ b e, pt = ptExp b e := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> simp [isExp]

theorem isProd_iff : pt.isProd o ↔ ∃ ps ns, pt = opN o ps ns := by
  rcases pt with _ | _ | _ | ⟨o', _, _⟩ <;> simp [isProd, eq_comm]

@[simp] theorem isProd_opN : (opN o ps ns).isProd o := by simp [isProd]

@[simp] theorem isProd_ptExp : (ptExp b e).isProd o = false := rfl

theorem isNonFree_iff : pt.isNonFree ↔ (∃ b e, pt = ptExp b e) ∨ ∃ o ps ns, pt = opN o ps ns := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | ⟨_ | _⟩ <;> simp [isNonFree, isExp, isProd]

@[simp, rocq_alias cryptis.PreTerm.Nnf_Nexp, rocq_alias cryptis.PreTerm.Nnf_Nmul,
  rocq_alias cryptis.PreTerm.Nnf_Ngmul]
theorem isNonFree_eq_false :
    pt.isNonFree = false ↔
      pt.isExp = false ∧ pt.isProd .mul = false ∧ pt.isProd .gmul = false := by
  simp [isNonFree, and_assoc]

@[simp, rocq_alias cryptis.PreTerm.Ngnf_Nexp, rocq_alias cryptis.PreTerm.Ngnf_Ngmul]
theorem isGNonFree_eq_false :
    pt.isGNonFree = false ↔ pt.isExp = false ∧ pt.isProd .gmul = false := by
  simp [isGNonFree]

@[rocq_alias cryptis.PreTerm.Nnf_Ngnf]
theorem isNonFree_of_isGNonFree (h : pt.isGNonFree) : pt.isNonFree := by
  simp only [isGNonFree, isNonFree, Bool.or_eq_true] at h ⊢
  tauto

/-! ### Products as signed multisets -/

/-- The base of an exponential, and any other pre-term itself. -/
@[rocq_alias cryptis.PreTerm.base]
def base : PreTerm → PreTerm
  | ptExp b _ => b
  | pt => pt

/-- The exponent of an exponential, and the unit `ptMul [] []` otherwise. -/
@[rocq_alias cryptis.PreTerm.expo]
def expo : PreTerm → PreTerm
  | ptExp _ e => e
  | _ => ptMul [] []

/-- The factors of a product of kind `o`, and any other pre-term as a single factor. -/
@[rocq_alias cryptis.PreTerm.factors, rocq_alias cryptis.PreTerm.gfactors]
def factors (o : TermOpN) (pt : PreTerm) : SMS PreTerm :=
  match pt with
  | opN o' ps ns => if o' = o then .make ps ns else {pt}
  | _ => {pt}

/-- The factor lists of a product of kind `o` as it stores them, and any other pre-term as a
single factor. These are the sorted factors of `factors o pt` when `pt` is normal. -/
@[rocq_alias cryptis.raw_factors, rocq_alias cryptis.raw_gfactors]
def rawFactors (o : TermOpN) (pt : PreTerm) : List PreTerm × List PreTerm :=
  match pt with
  | opN o' ps ns => if o' = o then (ps, ns) else ([pt], [])
  | _ => ([pt], [])

/-- The sorted positive and negative factors of a signed multiset. -/
def toLists (s : SMS PreTerm) : List PreTerm × List PreTerm :=
  (s.posPart.sort, s.negPart.sort)

/-- Whether a pair of factor lists is a single positive factor. -/
@[rocq_alias cryptis.PreTerm.single]
def single {α : Type _} : List α × List α → Bool
  | ([_], []) => true
  | _ => false

/-- The product of kind `o` of `s`, as a pre-term; a single positive factor stands for itself. -/
@[rocq_alias cryptis.PreTerm.mul_aux, rocq_alias cryptis.PreTerm.gmul_aux]
def prodAux (o : TermOpN) (s : SMS PreTerm) : PreTerm :=
  match toLists s with
  | ([t], []) => t
  | (ps, ns) => opN o ps ns

/-- The product of kind `o` of the elements of `s`, flattening the products of that kind among
them. -/
@[rocq_alias cryptis.PreTerm.mul, rocq_alias cryptis.PreTerm.gmul]
def prod (o : TermOpN) (s : SMS PreTerm) : PreTerm := prodAux o (s.bind (factors o))

/-- `b ^ e`, or `b` when `e` is the unit. -/
@[rocq_alias cryptis.PreTerm.mk_exp]
def mkExp (b e : PreTerm) : PreTerm := if e = ptMul [] [] then b else ptExp b e

/-- Exponentiation of a group atom, which merges iterated exponents. -/
@[rocq_alias cryptis.PreTerm.exp_aux]
def expAux (b e : PreTerm) : PreTerm := mkExp (base b) (prod .mul ({expo b} + {e}))

/-- Exponentiation, which distributes over the group factors of the base. -/
@[rocq_alias cryptis.PreTerm.exp]
def exp (b e : PreTerm) : PreTerm := prod .gmul ((factors .gmul b).map (expAux · e))

/-- The normal form of a pre-term. -/
@[rocq_alias cryptis.PreTerm.normalize]
def normalize : PreTerm → PreTerm
  | op0 o => op0 o
  | op1 o t => op1 o (normalize t)
  | op2 .exp b e => exp (normalize b) (normalize e)
  | op2 o t₁ t₂ => op2 o (normalize t₁) (normalize t₂)
  | opN o ps ns => prod o (.make (ps.map normalize) (ns.map normalize))

/-! ### Normal forms -/

/-- Factor lists in canonical form: both sorted, and with no common factor. -/
def IsCanonical (A : List PreTerm × List PreTerm) : Prop :=
  A.1.Pairwise (· ≤ ·) ∧ A.2.Pairwise (· ≤ ·) ∧ ∀ t ∈ A.1, t ∉ A.2

instance : DecidablePred IsCanonical := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

mutual

/-- Normal forms. The base of an exponential is a group atom and its exponent is not the unit;
products list their factors in canonical form, are not a single positive factor, and have no
products of the same kind as factors. -/
@[rocq_alias cryptis.PreTerm.wf]
def wf : PreTerm → Bool
  | op0 _ => true
  | op1 _ t => wf t
  | op2 .exp b e => wf b && !b.isGNonFree && wf e && e != ptMul [] []
  | op2 _ t₁ t₂ => wf t₁ && wf t₂
  | opN o ps ns => wfAll (isProd o) ps && wfAll (isProd o) ns && decide (IsCanonical (ps, ns)) &&
      !single (ps, ns)

/-- `ts.all fun t => wf t && !p t`, spelled out so that `wf` is structurally recursive. -/
def wfAll (p : PreTerm → Bool) : List PreTerm → Bool
  | [] => true
  | t :: ts => wf t && !p t && wfAll p ts

end

theorem wfAll_iff {p : PreTerm → Bool} {ts : List PreTerm} :
    wfAll p ts ↔ ∀ t ∈ ts, wf t ∧ p t = false := by
  induction ts <;> simp_all [wfAll]

/-- The factors of `s` are normal, and not products of kind `o`. -/
@[rocq_alias cryptis.PreTerm.wf_factors, rocq_alias cryptis.PreTerm.wf_gfactors]
def WfFactors (o : TermOpN) (s : SMS PreTerm) : Prop := ∀ t ∈ s, wf t ∧ t.isProd o = false

#rocq_ignore cryptis.PreTerm.wf_factorsP "PreTerm.WfFactors is this proposition"
#rocq_ignore cryptis.PreTerm.wf_gfactorsP "PreTerm.WfFactors is this proposition"

@[rocq_alias cryptis.PreTerm.wf_mulE, rocq_alias cryptis.PreTerm.wf_gmulE]
theorem wf_opN : wf (opN o ps ns) ↔
    (∀ t ∈ ps ++ ns, wf t ∧ t.isProd o = false) ∧ IsCanonical (ps, ns) ∧
      single (ps, ns) = false := by
  rw [List.forall_mem_append]
  simp [wf, wfAll_iff, and_assoc]

@[simp]
theorem wf_ptExp : wf (ptExp b e) ↔
    wf b ∧ b.isGNonFree = false ∧ wf e ∧ e ≠ ptMul [] [] := by
  simp [wf, and_assoc]

@[rocq_alias cryptis.PreTerm.wf_factors_wf, rocq_alias cryptis.PreTerm.wf_gfactors_wf]
theorem WfFactors.wf (h : WfFactors o s) (ht : t ∈ s) : wf t := (h t ht).1

@[rocq_alias cryptis.PreTerm.wf_factors_Nmul, rocq_alias cryptis.PreTerm.wf_gfactors_Ngmul]
theorem WfFactors.isProd_eq_false (h : WfFactors o s) (ht : t ∈ s) : t.isProd o = false :=
  (h t ht).2

@[simp]
theorem wfFactors_singleton : WfFactors o {t} ↔ wf t ∧ t.isProd o = false := by
  simp [WfFactors]

@[rocq_alias cryptis.PreTerm.wf_one, rocq_alias cryptis.PreTerm.wf_gone]
theorem wf_opN_nil : wf (opN o [] []) := by
  simp [wf_opN, IsCanonical, single]

/-! ### Factors -/

@[simp] theorem factors_opN : (opN o ps ns).factors o = .make ps ns := by simp [factors]

@[simp] theorem rawFactors_opN : (opN o ps ns).rawFactors o = (ps, ns) := by simp [rawFactors]

@[rocq_alias cryptis.PreTerm.factors_Nmul, rocq_alias cryptis.PreTerm.gfactors_Ngmul]
theorem factors_eq_singleton (h : pt.isProd o = false) : pt.factors o = {pt} := by
  rcases pt with _ | _ | _ | ⟨o', _, _⟩ <;> simp_all [factors, isProd]

theorem rawFactors_eq_singleton (h : pt.isProd o = false) : pt.rawFactors o = ([pt], []) := by
  rcases pt with _ | _ | _ | ⟨o', _, _⟩ <;> simp_all [rawFactors, isProd]

@[simp]
theorem toLists_singleton (t : PreTerm) : toLists {t} = ([t], []) := by
  simp [toLists]

theorem isCanonical_toLists (s : SMS PreTerm) : IsCanonical (toLists s) :=
  ⟨Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _, fun _ h₁ h₂ =>
    Multiset.disjoint_left.mp s.disjoint ((Multiset.mem_sort _).mp h₁)
      ((Multiset.mem_sort _).mp h₂)⟩

theorem mem_of_mem_toLists (h : t ∈ (toLists s).1 ++ (toLists s).2) : t ∈ s := by
  rcases List.mem_append.mp h with h | h
  · exact SMS.mem_of_mem_posPart ((Multiset.mem_sort _).mp h)
  · exact SMS.mem_of_mem_negPart ((Multiset.mem_sort _).mp h)

theorem make_toLists (s : SMS PreTerm) : SMS.make (toLists s).1 (toLists s).2 = s := by
  simp [toLists, SMS.make_posPart_negPart]

theorem IsCanonical.disjoint {A : List PreTerm × List PreTerm} (h : IsCanonical A) :
    Disjoint (A.1 : Multiset PreTerm) A.2 :=
  (Multiset.coe_disjoint _ _).mpr fun _ ha hb => h.2.2 _ ha hb

theorem toLists_make {A : List PreTerm × List PreTerm} (h : IsCanonical A) :
    toLists (.make A.1 A.2) = A := by
  rw [SMS.make_of_disjoint h.disjoint]
  simp [toLists, List.mergeSort_eq_self _ h.1, List.mergeSort_eq_self _ h.2.1]

@[rocq_alias cryptis.PreTerm.car_factors, rocq_alias cryptis.PreTerm.car_gfactors]
theorem toLists_factors_opN (h : wf (opN o ps ns)) : toLists ((opN o ps ns).factors o) = (ps, ns) :=
  by rw [factors_opN]; exact toLists_make (wf_opN.mp h).2.1

@[rocq_alias cryptis.PreTerm.car_factorsE, rocq_alias cryptis.PreTerm.car_gfactorsE]
theorem toLists_factors (h : wf pt) : toLists (pt.factors o) = pt.rawFactors o := by
  by_cases hm : pt.isProd o
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp hm
    rw [toLists_factors_opN h, rawFactors_opN]
  · rw [factors_eq_singleton (by simpa using hm), rawFactors_eq_singleton (by simpa using hm),
      toLists_singleton]

@[rocq_alias cryptis.PreTerm.elements_factors, rocq_alias cryptis.PreTerm.elements_gfactors]
theorem elements_factors (h : wf pt) :
    (pt.factors o).elements = ((pt.rawFactors o).1 : Multiset PreTerm) + (pt.rawFactors o).2 := by
  rw [← toLists_factors h, toLists, Multiset.sort_eq, Multiset.sort_eq, SMS.elements]

@[rocq_alias cryptis.PreTerm.wf_wf_factors, rocq_alias cryptis.PreTerm.wf_wf_gfactors]
theorem wfFactors_factors (h : wf pt) : WfFactors o (pt.factors o) := by
  by_cases hm : pt.isProd o
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp hm
    intro t ht
    rw [factors_opN] at ht
    exact (wf_opN.mp h).1 t (by simpa using SMS.mem_of_mem_make ht)
  · rw [factors_eq_singleton (by simpa using hm)]
    simp_all

/-! ### Products -/

@[rocq_alias cryptis.PreTerm.mul_aux_Nsingle, rocq_alias cryptis.PreTerm.gmul_aux_Nsingle]
theorem prodAux_of_single_eq_false (h : single (toLists s) = false) :
    prodAux o s = opN o (toLists s).1 (toLists s).2 := by
  rw [prodAux]
  split <;> simp_all [single]

@[rocq_alias cryptis.PreTerm.mul_aux_single, rocq_alias cryptis.PreTerm.gmul_aux_single]
theorem prodAux_of_toLists_eq (h : toLists s = ([t], [])) : prodAux o s = t := by
  rw [prodAux, h]

@[simp] theorem prodAux_singleton (t : PreTerm) : prodAux o {t} = t :=
  prodAux_of_toLists_eq (toLists_singleton t)

@[rocq_alias cryptis.PreTerm.single_car]
theorem single_toLists : single (toLists s) ↔ ∃ t, s = {t} := by
  refine ⟨fun h => ?_, fun ⟨t, h⟩ => by simp [h, single]⟩
  match hs : toLists s, h with
  | ([t], []), _ => exact ⟨t, by rw [← make_toLists s, hs]; simp⟩

@[rocq_alias cryptis.PreTerm.wf_mul_aux, rocq_alias cryptis.PreTerm.wf_gmul_aux]
theorem wf_prodAux (h : WfFactors o s) : wf (prodAux o s) := by
  cases hs : single (toLists s)
  · rw [prodAux_of_single_eq_false hs, wf_opN]
    exact ⟨fun t ht => h t (mem_of_mem_toLists ht), isCanonical_toLists s, hs⟩
  · obtain ⟨t, rfl⟩ := single_toLists.mp hs
    simpa using h.wf (SMS.mem_singleton.mpr rfl)

@[rocq_alias cryptis.PreTerm.mul_auxK, rocq_alias cryptis.PreTerm.gmul_auxK]
theorem factors_prodAux (h : WfFactors o s) : (prodAux o s).factors o = s := by
  cases hs : single (toLists s)
  · rw [prodAux_of_single_eq_false hs, factors_opN, make_toLists]
  · obtain ⟨t, rfl⟩ := single_toLists.mp hs
    simpa using factors_eq_singleton (wfFactors_singleton.mp h).2

@[rocq_alias cryptis.PreTerm.factorsK, rocq_alias cryptis.PreTerm.gfactorsK]
theorem prodAux_factors (h : wf t) : prodAux o (t.factors o) = t := by
  by_cases hm : t.isProd o
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp hm
    have hs : single (toLists ((opN o ps ns).factors o)) = false := by
      rw [toLists_factors_opN h]
      exact (wf_opN.mp h).2.2
    rw [prodAux_of_single_eq_false hs, toLists_factors_opN h]
  · simp [factors_eq_singleton (by simpa using hm)]

@[rocq_alias cryptis.PreTerm.wf_bind_factors, rocq_alias cryptis.PreTerm.wf_bind_gfactors]
theorem wfFactors_bind_factors (h : ∀ t ∈ s, wf t) : WfFactors o (s.bind (factors o)) :=
  fun _ ht =>
    have ⟨u, hu, ht⟩ := SMS.exists_mem_of_mem_bind ht
    wfFactors_factors (h u hu) _ ht

@[rocq_alias cryptis.PreTerm.wf_mul, rocq_alias cryptis.PreTerm.wf_gmul]
theorem wf_prod (h : ∀ t ∈ s, wf t) : wf (prod o s) := wf_prodAux (wfFactors_bind_factors h)

@[rocq_alias cryptis.PreTerm.bind_factors_wf, rocq_alias cryptis.PreTerm.bind_gfactors_wf]
theorem WfFactors.bind_factors (h : WfFactors o s) : s.bind (factors o) = s :=
  (SMS.bind_congr fun _ ht => factors_eq_singleton (h.isProd_eq_false ht)).trans
    (SMS.bind_singleton_right s)

theorem factors_prod (h : ∀ t ∈ s, wf t) : (prod o s).factors o = s.bind (factors o) :=
  factors_prodAux (wfFactors_bind_factors h)

theorem prod_factors (h : wf pt) : prod o (pt.factors o) = pt := by
  rw [prod, (wfFactors_factors h).bind_factors, prodAux_factors h]

@[rocq_alias cryptis.PreTerm.mul1, rocq_alias cryptis.PreTerm.gmul1]
theorem prod_singleton (h : wf t) : prod o {t} = t := by
  rw [prod, SMS.bind_singleton, prodAux_factors h]

theorem prod_zero : prod o 0 = opN o [] [] := by
  simp [prod, prodAux, toLists]

@[rocq_alias cryptis.PreTerm.mul_unit_l]
theorem prod_unit_left (t : PreTerm) : prod o ({opN o [] []} + {t}) = prod o {t} := by
  simp [prod]

@[rocq_alias cryptis.PreTerm.mul_unit_r]
theorem prod_unit_right (h : wf t) : prod o ({t} + {opN o [] []}) = t := by
  rw [add_comm, prod_unit_left, prod_singleton h]

/-! ### Exponentials -/

@[rocq_alias cryptis.PreTerm.wf_mk_exp]
theorem wf_mkExp (hb : b.isGNonFree = false) (wb : wf b) (we : wf e) : wf (mkExp b e) := by
  unfold mkExp
  split_ifs with he
  · exact wb
  · simp [wb, hb, we, he]

@[rocq_alias cryptis.PreTerm.wf_base]
theorem wf_base (h : wf pt) : wf (base pt) := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _
  case op2.exp => exact (wf_ptExp.mp h).1
  all_goals exact h

@[rocq_alias cryptis.PreTerm.base_expN]
theorem base_eq_self (h : pt.isExp = false) : base pt = pt := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> first | rfl | simp [isExp] at h

@[rocq_alias cryptis.PreTerm.base_Nexp]
theorem isExp_base (h : wf pt) : (base pt).isExp = false := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _
  case op2.exp => exact (isGNonFree_eq_false.mp (wf_ptExp.mp h).2.1).1
  all_goals rfl

/-- There is no scalar counterpart: a scalar product in a base is an atom. -/
@[rocq_alias cryptis.PreTerm.is_gmul_base]
theorem isProd_gmul_base (h : wf pt) : (base pt).isProd .gmul = pt.isProd .gmul := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _
  case op2.exp => exact (isGNonFree_eq_false.mp (wf_ptExp.mp h).2.1).2
  all_goals rfl

@[rocq_alias cryptis.PreTerm.expo_expN]
theorem expo_eq_unit (h : pt.isExp = false) : expo pt = ptMul [] [] := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> first | rfl | simp [isExp] at h

@[rocq_alias cryptis.PreTerm.wf_expo]
theorem wf_expo (h : wf pt) : wf (expo pt) := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _
  case op2.exp => exact (wf_ptExp.mp h).2.2.1
  all_goals exact wf_opN_nil

@[rocq_alias cryptis.PreTerm.base_Ngnf]
theorem isGNonFree_base (h : wf t) (hm : t.isProd .gmul = false) :
    (base t).isGNonFree = false :=
  isGNonFree_eq_false.mpr ⟨isExp_base h, (isProd_gmul_base h).trans hm⟩

@[rocq_alias cryptis.PreTerm.wf_exp_aux]
theorem wf_expAux (ht : wf t) (hm : t.isProd .gmul = false) (he : wf e) : wf (expAux t e) := by
  refine wf_mkExp (isGNonFree_base ht hm) (wf_base ht) (wf_prod fun u hu => ?_)
  rcases SMS.mem_or_mem_of_mem_add hu with hu | hu <;> rw [SMS.mem_singleton.mp hu]
  exacts [wf_expo ht, he]

@[rocq_alias cryptis.PreTerm.exp_aux_Ngmul]
theorem isProd_gmul_expAux (ht : wf t) (hm : t.isProd .gmul = false) :
    (expAux t e).isProd .gmul = false := by
  unfold expAux mkExp
  split_ifs
  · exact (isGNonFree_eq_false.mp (isGNonFree_base ht hm)).2
  · rfl

@[rocq_alias cryptis.PreTerm.wf_exp]
theorem wf_exp (hb : wf b) (he : wf e) : wf (exp b e) := by
  refine wf_prod fun t ht => ?_
  obtain ⟨u, hu, rfl⟩ := SMS.exists_of_mem_map ht
  have := wfFactors_factors (o := .gmul) hb
  exact wf_expAux (this.wf hu) (this.isProd_eq_false hu) he

/-- On a base that is not a group product, the group product of `exp` collapses. -/
@[rocq_alias cryptis.PreTerm.exp_Ngmul]
theorem exp_eq_expAux (hb : wf b) (he : wf e) (hm : b.isProd .gmul = false) :
    exp b e = expAux b e := by
  rw [exp, factors_eq_singleton hm, SMS.map_singleton, prod_singleton (wf_expAux hb hm he)]

@[rocq_alias cryptis.PreTerm.mk_exp_base_expo]
theorem mkExp_base_expo (h : wf t) : mkExp (base t) (expo t) = t := by
  rcases t with _ | _ | ⟨_ | _ | _⟩ | _
  case op2.exp => exact ite_eq_right (wf_ptExp.mp h).2.2.2
  all_goals exact ite_eq_left rfl

@[rocq_alias cryptis.PreTerm.exp_aux_unit]
theorem expAux_unit (h : wf t) : expAux t (ptMul [] []) = t := by
  rw [expAux, prod_unit_right (wf_expo h), mkExp_base_expo h]

/-- A normal exponential is its own normal form. -/
theorem exp_eq_ptExp (h : wf (ptExp b e)) : exp b e = ptExp b e := by
  obtain ⟨hb, hgnf, he, he1⟩ := wf_ptExp.mp h
  obtain ⟨hx, hm⟩ := isGNonFree_eq_false.mp hgnf
  rw [exp_eq_expAux hb he hm, expAux, base_eq_self hx, expo_eq_unit hx, prod_unit_left,
    prod_singleton he, mkExp, ite_eq_right he1]

#rocq_ignore cryptis.PreTerm.foldr_Forall "PreTerm.ind takes ∀ t ∈ ps hypotheses"

/-! ### Normalization -/

@[rocq_alias cryptis.PreTerm.wf_normalize]
theorem wf_normalize (pt : PreTerm) : wf (normalize pt) := by
  induction pt with
  | op0 o => rw [normalize]; rfl
  | op1 o t ih => rw [normalize]; exact ih
  | op2 o t₁ t₂ ih₁ ih₂ =>
    cases o
    case exp => rw [normalize]; exact wf_exp ih₁ ih₂
    all_goals
      rw [normalize]
      · simp [wf, ih₁, ih₂]
      · nofun
  | opN o ps ns ihp ihn =>
    rw [normalize]
    refine wf_prod fun t ht => ?_
    have := SMS.mem_of_mem_make ht
    simp only [Multiset.coe_add, Multiset.mem_coe, List.mem_append, List.mem_map] at this
    rcases this with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    exacts [ihp u hu, ihn u hu]

@[rocq_alias cryptis.PreTerm.normalize_wf]
theorem normalize_of_wf (h : wf pt) : normalize pt = pt := by
  induction pt with
  | op0 o => rw [normalize]
  | op1 o t ih => rw [normalize, ih h]
  | op2 o t₁ t₂ ih₁ ih₂ =>
    cases o
    case exp =>
      have ⟨hb, _, he, _⟩ := wf_ptExp.mp h
      rw [normalize, ih₁ hb, ih₂ he, exp_eq_ptExp h]
    all_goals
      have ⟨h₁, h₂⟩ : wf t₁ ∧ wf t₂ := by simpa [wf] using h
      rw [normalize, ih₁ h₁, ih₂ h₂]
      nofun
  | opN o ps ns ihp ihn =>
    have hw := (wf_opN.mp h).1
    rw [normalize, List.map_congr_left fun t ht => ihp t ht (hw t (by simp [ht])).1,
      List.map_congr_left fun t ht => ihn t ht (hw t (by simp [ht])).1, List.map_id',
      List.map_id', ← factors_opN, prod_factors h]

@[simp, rocq_alias cryptis.PreTerm.normalize_idem]
theorem normalize_idem (pt : PreTerm) : normalize (normalize pt) = normalize pt :=
  normalize_of_wf (wf_normalize pt)

@[rocq_alias cryptis.PreTerm.fmap_normalize_wf]
theorem map_normalize_of_wf {ts : List PreTerm} (h : ∀ t ∈ ts, wf t) : ts.map normalize = ts :=
  (List.map_congr_left fun t ht => normalize_of_wf (h t ht)).trans (List.map_id _)

/-! ### The exponentiation laws -/

@[rocq_alias cryptis.PreTerm.exp_unit]
theorem exp_unit (h : wf b) : exp b (ptMul [] []) = b := by
  have hg := wfFactors_factors (o := .gmul) h
  rw [exp, SMS.map_eq_self fun u hu => expAux_unit (hg.wf hu), prod_factors h]

@[rocq_alias cryptis.PreTerm.exp_base_expo]
theorem exp_base_expo (h : wf b) : exp (base b) (expo b) = b := by
  by_cases hx : b.isExp
  · obtain ⟨c, d, rfl⟩ := isExp_iff.mp hx
    exact exp_eq_ptExp h
  · rw [base_eq_self (by simpa using hx), expo_eq_unit (by simpa using hx), exp_unit h]

/-- `exp` sees through to the base only when it is not a group product: otherwise `exp`
distributes and the result is not an exponential. -/
@[rocq_alias cryptis.PreTerm.base_exp]
theorem base_exp (hb : wf b) (he : wf e) (hm : b.isProd .gmul = false) :
    base (exp b e) = base b := by
  rw [exp_eq_expAux hb he hm, expAux, mkExp]
  split_ifs
  · exact base_eq_self (isExp_base hb)
  · rfl

@[rocq_alias cryptis.PreTerm.expo_exp]
theorem expo_exp (hb : wf b) (he : wf e) (hm : b.isProd .gmul = false) :
    expo (exp b e) = prod .mul ({expo b} + {e}) := by
  rw [exp_eq_expAux hb he hm, expAux, mkExp]
  split_ifs with h
  · rw [h, expo_eq_unit (isExp_base hb)]
  · rfl

/-- Exponentiation distributes over group atoms: `(t₁ ⋯ tₙ) ^ e = t₁ ^ e ⋯ tₙ ^ e`. -/
@[rocq_alias cryptis.PreTerm.exp_gmul]
theorem exp_prod_gmul (hw : ∀ t ∈ s, wf t) (hm : ∀ t ∈ s, t.isProd .gmul = false) :
    exp (prod .gmul s) e = prod .gmul (s.map (expAux · e)) := by
  have hs : WfFactors .gmul s := fun t ht => ⟨hw t ht, hm t ht⟩
  have hg : prod .gmul s = prodAux .gmul s := by rw [prod, hs.bind_factors]
  rw [exp, hg, factors_prodAux hs]

@[rocq_alias cryptis.PreTerm.Ngmul_exp]
theorem isProd_gmul_exp (hb : wf b) (he : wf e) (hm : b.isProd .gmul = false) :
    (exp b e).isProd .gmul = false := by
  rw [exp_eq_expAux hb he hm]
  exact isProd_gmul_expAux hb hm

end PreTerm
end Cryptis
