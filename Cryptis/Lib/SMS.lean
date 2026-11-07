module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Filter
public import Iris.Init

/-! Signed multisets: the free abelian group on a type `T`.

A signed multiset has positive and negative occurrences of elements, kept as two disjoint
multisets. Disjointness makes the representation canonical, so two signed multisets are equal when
each element has the same signed multiplicity `count x s` in both.

- The basic operations: `make X Y` is `X` minus `Y`, which cancels their common occurrences, and
  signed multisets form an additive commutative group.
- Elements and membership: an element belongs to a signed multiset when its multiplicity is not
  zero, and signed multisets are built from `0` one element at a time.
- Bind and map: `bind` substitutes a signed multiset for each element, extended to a group
  homomorphism, and `map` substitutes elements for elements.
- Filter: the occurrences of the elements that satisfy a predicate.
- Products: a map into a commutative group extends to signed multisets (`prod` and `sum`). -/

@[expose] public section
namespace Cryptis

/-- Signed multisets, as disjoint positive and negative parts. -/
@[rocq_alias cryptis.SMS.sms]
structure SMS (T : Type _) where
  posPart : Multiset T
  negPart : Multiset T
  disjoint : Disjoint posPart negPart

namespace SMS

variable {T U V : Type _}

instance : Zero (SMS T) := ⟨⟨0, 0, disjoint_bot_left⟩⟩
instance : Singleton T (SMS T) := ⟨fun x => ⟨{x}, 0, disjoint_bot_right⟩⟩
instance : Neg (SMS T) := ⟨fun s => ⟨s.negPart, s.posPart, s.disjoint.symm⟩⟩

@[simp] theorem posPart_zero : (0 : SMS T).posPart = 0 := rfl
@[simp] theorem negPart_zero : (0 : SMS T).negPart = 0 := rfl
@[simp, rocq_alias cryptis.SMS.pos_singleton] theorem posPart_singleton (x : T) :
    ({x} : SMS T).posPart = {x} := rfl
@[simp, rocq_alias cryptis.SMS.neg_singleton] theorem negPart_singleton (x : T) :
    ({x} : SMS T).negPart = 0 := rfl
@[simp, rocq_alias cryptis.SMS.pos_inv] theorem posPart_neg (s : SMS T) : (-s).posPart = s.negPart := rfl
@[simp, rocq_alias cryptis.SMS.neg_inv] theorem negPart_neg (s : SMS T) : (-s).negPart = s.posPart := rfl

/-- The occurrences of `s`, positive and negative. -/
@[rocq_alias cryptis.SMS.elements_instance]
def elements (s : SMS T) : Multiset T := s.posPart + s.negPart

@[rocq_alias cryptis.SMS.elem_of_instance]
instance : Membership T (SMS T) := ⟨fun s x => x ∈ s.elements⟩

@[rocq_alias cryptis.SMS.elem_of_elements]
theorem mem_elements {x : T} {s : SMS T} : x ∈ s.elements ↔ x ∈ s := .rfl

@[rocq_alias cryptis.SMS.elem_of_pos]
theorem mem_of_mem_posPart {x : T} {s : SMS T} (h : x ∈ s.posPart) : x ∈ s :=
  Multiset.mem_add.mpr (.inl h)

@[rocq_alias cryptis.SMS.elem_of_neg]
theorem mem_of_mem_negPart {x : T} {s : SMS T} (h : x ∈ s.negPart) : x ∈ s :=
  Multiset.mem_add.mpr (.inr h)

@[simp, rocq_alias cryptis.SMS.elements_empty]
theorem elements_zero : (0 : SMS T).elements = 0 := rfl

@[simp, rocq_alias cryptis.SMS.elements_singleton]
theorem elements_singleton (x : T) : ({x} : SMS T).elements = {x} := rfl

@[simp, rocq_alias cryptis.SMS.elements_inv]
theorem elements_neg (s : SMS T) : (-s).elements = s.elements := add_comm _ _

theorem eq_singleton_of_card_elements_eq_one {s : SMS T} {a : T}
    (h : Multiset.card s.elements = 1) (ha : a ∈ s.posPart) : s = {a} := by
  obtain ⟨X, Y, _⟩ := s
  have hX : 0 < Multiset.card X := Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩
  simp only [elements, Multiset.card_add] at h
  obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp (show Multiset.card X = 1 by omega)
  obtain rfl : Y = 0 := Multiset.card_eq_zero.mp (by omega)
  obtain rfl := Multiset.mem_singleton.mp ha
  rfl

variable [DecidableEq T] [DecidableEq U] [DecidableEq V]

instance : DecidableEq (SMS T) := fun s t =>
  decidable_of_iff (s.posPart = t.posPart ∧ s.negPart = t.negPart) <| by
    cases s; cases t; simp

/-- The signed multiplicity of `x` in `s`. -/
@[rocq_alias cryptis.SMS.count]
def count (x : T) (s : SMS T) : ℤ := s.posPart.count x - s.negPart.count x

theorem count_eq_zero_or_of_disjoint {X Y : Multiset T} (h : Disjoint X Y) (x : T) :
    X.count x = 0 ∨ Y.count x = 0 := by
  by_contra h'
  push Not at h'
  exact Multiset.disjoint_left.mp h (Multiset.count_ne_zero.mp h'.1)
    (Multiset.count_ne_zero.mp h'.2)

theorem count_posPart_eq_zero_or (s : SMS T) (x : T) :
    s.posPart.count x = 0 ∨ s.negPart.count x = 0 :=
  count_eq_zero_or_of_disjoint s.disjoint x

@[rocq_alias cryptis.SMS.count_mem_pos]
theorem count_posPart (s : SMS T) (x : T) : s.posPart.count x = (s.count x).toNat := by
  have := s.count_posPart_eq_zero_or x
  simp only [count]
  omega

theorem count_negPart (s : SMS T) (x : T) : s.negPart.count x = (-s.count x).toNat := by
  have := s.count_posPart_eq_zero_or x
  simp only [count]
  omega

@[ext, rocq_alias cryptis.SMS.count_inj, rocq_alias cryptis.SMS.car_inj]
theorem ext {s t : SMS T} (h : ∀ x, s.count x = t.count x) : s = t := by
  have hp : s.posPart = t.posPart :=
    Multiset.ext.mpr fun x => by rw [count_posPart, count_posPart, h]
  have hn : s.negPart = t.negPart :=
    Multiset.ext.mpr fun x => by rw [count_negPart, count_negPart, h]
  cases s
  cases t
  simp_all

/-- The signed multiset with positive occurrences `X` and negative occurrences `Y`. -/
@[rocq_alias cryptis.SMS.make]
def make (X Y : Multiset T) : SMS T where
  posPart := X - Y
  negPart := Y - X
  disjoint := Multiset.disjoint_left.mpr fun h₁ h₂ => by
    rw [← Multiset.count_pos, Multiset.count_sub] at h₁ h₂
    omega

@[simp] theorem posPart_make (X Y : Multiset T) : (make X Y).posPart = X - Y := rfl
@[simp] theorem negPart_make (X Y : Multiset T) : (make X Y).negPart = Y - X := rfl

@[simp, rocq_alias cryptis.SMS.count_make]
theorem count_make (x : T) (X Y : Multiset T) : (make X Y).count x = X.count x - Y.count x := by
  simp only [count, posPart_make, negPart_make, Multiset.count_sub]
  omega

@[rocq_alias cryptis.SMS.make_pos_neg]
theorem make_posPart_negPart (s : SMS T) : make s.posPart s.negPart = s :=
  ext fun x => by rw [count_make]; rfl

theorem make_of_disjoint {X Y : Multiset T} (h : Disjoint X Y) : make X Y = ⟨X, Y, h⟩ :=
  ext fun x => by rw [count_make]; rfl

instance : Add (SMS T) := ⟨fun s t => make (s.posPart + t.posPart) (s.negPart + t.negPart)⟩
instance : Sub (SMS T) := ⟨fun s t => s + -t⟩

attribute [rocq_alias cryptis.SMS.empty_instance] instZero
attribute [rocq_alias cryptis.SMS.singleton_instance] instSingleton
attribute [rocq_alias cryptis.SMS.disj_union_instance] instAdd
attribute [rocq_alias cryptis.SMS.inv] instNeg

@[simp, rocq_alias cryptis.SMS.count_empty]
theorem count_zero (x : T) : (0 : SMS T).count x = 0 := rfl

@[simp, rocq_alias cryptis.SMS.count_singleton]
theorem count_singleton (x y : T) : ({y} : SMS T).count x = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [count, h]

@[simp, rocq_alias cryptis.SMS.count_disj_union]
theorem count_add (x : T) (s t : SMS T) : (s + t).count x = s.count x + t.count x := by
  change (make _ _).count x = _
  simp [count]
  omega

@[simp, rocq_alias cryptis.SMS.count_inv]
theorem count_neg (x : T) (s : SMS T) : (-s).count x = -s.count x := by
  simp [count]

@[simp]
theorem count_sub (x : T) (s t : SMS T) : (s - t).count x = s.count x - t.count x := by
  change (s + -t).count x = _
  simp [sub_eq_add_neg]

@[rocq_alias cryptis.SMS.disj_union_comm, rocq_alias cryptis.SMS.disj_union_assoc,
  rocq_alias cryptis.SMS.disj_union_left_id, rocq_alias cryptis.SMS.disj_union_right_id,
  rocq_alias cryptis.SMS.disj_union_inv_r, rocq_alias cryptis.SMS.invK]
instance : AddCommGroup (SMS T) where
  add_assoc _ _ _ := ext fun _ => by simp [add_assoc]
  zero_add _ := ext fun _ => by simp
  add_zero _ := ext fun _ => by simp
  add_comm _ _ := ext fun _ => by simp [add_comm]
  neg_add_cancel _ := ext fun _ => by simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg _ _ := rfl

@[rocq_alias cryptis.SMS.disj_union_make]
theorem make_add_make (X₁ Y₁ X₂ Y₂ : Multiset T) :
    make X₁ Y₁ + make X₂ Y₂ = make (X₁ + X₂) (Y₁ + Y₂) :=
  ext fun x => by simp; omega

@[simp, rocq_alias cryptis.SMS.singleton_make]
theorem make_singleton_zero (x : T) : make {x} 0 = ({x} : SMS T) :=
  make_of_disjoint _

@[simp]
theorem make_zero_zero : make 0 0 = (0 : SMS T) := make_of_disjoint _

@[rocq_alias cryptis.SMS.make_cons_l]
theorem make_cons_left (x : T) (X Y : Multiset T) : make (x ::ₘ X) Y = {x} + make X Y := by
  rw [← make_singleton_zero, make_add_make, Multiset.singleton_add, zero_add]

@[rocq_alias cryptis.SMS.make_cons_r]
theorem make_cons_right (y : T) (X Y : Multiset T) : make X (y ::ₘ Y) = -{y} + make X Y :=
  ext fun x => by by_cases h : x = y <;> simp [h]; omega

@[simp, rocq_alias cryptis.SMS.inv_make]
theorem neg_make (X Y : Multiset T) : -make X Y = make Y X :=
  ext fun x => by simp

/-! ### Elements and membership -/


@[rocq_alias cryptis.SMS.elem_of_dec]
instance (x : T) (s : SMS T) : Decidable (x ∈ s) :=
  inferInstanceAs (Decidable (x ∈ s.elements))


theorem count_elements (x : T) (s : SMS T) :
    s.elements.count x = (s.count x).toNat + (-s.count x).toNat := by
  rw [elements, Multiset.count_add, count_posPart, count_negPart]

@[rocq_alias cryptis.SMS.elem_of_count]
theorem mem_iff_count_ne_zero {x : T} {s : SMS T} : x ∈ s ↔ s.count x ≠ 0 := by
  rw [← mem_elements, ← Multiset.count_ne_zero, count_elements]
  omega

@[rocq_alias cryptis.SMS.not_elem_of_count]
theorem count_eq_zero_of_not_mem {x : T} {s : SMS T} (h : x ∉ s) : s.count x = 0 := by
  rw [mem_iff_count_ne_zero] at h
  omega

@[rocq_alias cryptis.SMS.count_pos]
theorem count_pos_iff {x : T} {s : SMS T} : 0 < s.count x ↔ x ∈ s.posPart := by
  rw [← Multiset.count_pos, count_posPart]
  omega

@[rocq_alias cryptis.SMS.count_neg]
theorem count_neg_iff {x : T} {s : SMS T} : s.count x < 0 ↔ x ∈ s.negPart := by
  rw [← Multiset.count_pos, count_negPart]
  omega


@[rocq_alias cryptis.SMS.elements_empty_inv]
theorem eq_zero_of_elements_eq_zero {s : SMS T} (h : s.elements = 0) : s = 0 :=
  ext fun x => by
    have := congrArg (Multiset.count x) h
    simp only [elements, Multiset.count_add, Multiset.count_zero] at this
    simp only [count, posPart_zero, negPart_zero, Multiset.count_zero]
    omega

@[rocq_alias cryptis.SMS.elements_disj_union]
theorem elements_add {s t : SMS T} (h₁ : Disjoint s.posPart t.negPart)
    (h₂ : Disjoint s.negPart t.posPart) : (s + t).elements = s.elements + t.elements := by
  refine Multiset.ext.mpr fun x => ?_
  have d₁ := count_eq_zero_or_of_disjoint h₁ x
  have d₂ := count_eq_zero_or_of_disjoint h₂ x
  rw [count_posPart, count_negPart] at d₁ d₂
  simp only [count_elements, count_add, Multiset.count_add]
  omega

@[rocq_alias cryptis.SMS.elem_of_disj_union]
theorem mem_or_mem_of_mem_add {x : T} {s t : SMS T} (h : x ∈ s + t) : x ∈ s ∨ x ∈ t := by
  simp only [mem_iff_count_ne_zero, count_add] at h ⊢
  omega

omit [DecidableEq T] in
@[simp, rocq_alias cryptis.SMS.elem_of_singleton]
theorem mem_singleton {x y : T} : x ∈ ({y} : SMS T) ↔ x = y := Multiset.mem_singleton

@[rocq_alias cryptis.SMS.elem_of_make]
theorem mem_of_mem_make {x : T} {X Y : Multiset T} (h : x ∈ make X Y) : x ∈ X + Y := by
  rw [mem_iff_count_ne_zero, count_make] at h
  rw [← Multiset.count_ne_zero, Multiset.count_add]
  omega

@[simp, rocq_alias cryptis.SMS.pos_make_nil_r]
theorem posPart_make_zero (X : Multiset T) : (make X 0).posPart = X := Multiset.sub_zero X

@[simp, rocq_alias cryptis.SMS.neg_make_nil_r]
theorem negPart_make_zero (X : Multiset T) : (make X 0).negPart = 0 :=
  Multiset.ext.mpr fun _ => by simp [Multiset.count_sub]

@[simp, rocq_alias cryptis.SMS.elements_make_nil_r]
theorem elements_make_zero (X : Multiset T) : (make X 0).elements = X := by
  rw [elements, posPart_make_zero, negPart_make_zero, add_zero]

@[rocq_alias cryptis.SMS.elem_of_make_nil_r]
theorem mem_make_zero {x : T} {X : Multiset T} : x ∈ make X 0 ↔ x ∈ X := by
  rw [← mem_elements, elements_make_zero]

@[rocq_alias cryptis.SMS.max_or_empty]
theorem exists_max_or_eq_zero {β : Type _} [LinearOrder β] (f : T → β) (s : SMS T) :
    (∃ x ∈ s, ∀ y ∈ s, f y ≤ f x) ∨ s = 0 := by
  by_cases h : s.elements = 0
  · exact .inr (eq_zero_of_elements_eq_zero h)
  · obtain ⟨x, hx, hmax⟩ := s.elements.toFinset.exists_max_image f
      (Multiset.toFinset_nonempty.mpr h)
    exact .inl ⟨x, Multiset.mem_toFinset.mp hx,
      fun y hy => hmax y (Multiset.mem_toFinset.mpr hy)⟩

/-- Induction on signed multisets: they are built from `0` by adding or subtracting one
element at a time. -/
@[elab_as_elim, rocq_alias cryptis.SMS.sms_ind]
theorem induction {motive : SMS T → Prop} (zero : motive 0)
    (add : ∀ x s, motive s → motive ({x} + s)) (sub : ∀ x s, motive s → motive (-{x} + s))
    (s : SMS T) : motive s := by
  rw [← make_posPart_negPart s]
  generalize s.posPart = X
  generalize s.negPart = Y
  induction Y using Multiset.induction_on with
  | empty =>
    induction X using Multiset.induction_on with
    | empty => simpa using zero
    | cons x X ih => rw [make_cons_left]; exact add _ _ ih
  | cons y Y ih => rw [make_cons_right]; exact sub _ _ ih

#rocq_ignore cryptis.SMS.car "The representation is the pair posPart, negPart"
#rocq_ignore cryptis.SMS.wf_car "SMS.disjoint"
#rocq_ignore cryptis.SMS.pos "SMS.posPart"
#rocq_ignore cryptis.SMS.neg "SMS.negPart"
#rocq_ignore cryptis.SMS.car_make "posPart and negPart of make X Y are X - Y and Y - X by definition"
#rocq_ignore cryptis.SMS.make_proper "make takes multisets, which are invariant under permutation"
#rocq_ignore cryptis.SMS.car_singleton "SMS.posPart_singleton, SMS.negPart_singleton"
#rocq_ignore cryptis.SMS.car_inv "SMS.posPart_neg, SMS.negPart_neg"
#rocq_ignore cryptis.SMS.elements_car "SMS.elements is defined from posPart and negPart"
#rocq_ignore cryptis.SMS.elements_pos_neg "SMS.elements is defined from posPart and negPart"
#rocq_ignore cryptis.SMS.count_mem_elements "SMS.count_elements"

#rocq_ignore cryptis.SMS.Internal.app "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel_cons "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel_disjoint "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel_id "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel_nil "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.cancel_step "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_app "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_cancel "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_cancel_step "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_cons1 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_cons2 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_count_mem "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_elements "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_eq0_elem_of "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_app "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_cancel "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_cons1 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_cons2 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_ext_count "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_nil "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_perm "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_flat_to "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_mem_disjoint "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_perm "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_smap_cancel "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_smap_cancel_step "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_smap_inj "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_smap_to "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_to "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.count_to_eq "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elements "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elements_smap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elements_swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elem_of_cancel "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elem_of_elements_to "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elem_of_flat "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elem_of_to1 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.elem_of_to2 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.flat "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.flat_atoms "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.flat_ext "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.flat_singletons "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.flat_smap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.le "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.le_antisymm "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.le_dec "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.le_total "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.le_trans "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.not_elem_of_count "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.not_elem_of_count1 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.not_elem_of_count2 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.smap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.smap_ext "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.smap_flat "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.smap_id "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.smap_smap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to_disjoint "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to_eq "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to_id "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to_pos "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.to_swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_count_gt0 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_count_inj "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_count_lt0 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_count_mem_elements "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_disjoint "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_elem_of_elements "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_intro "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_nil "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_singleton1 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_singleton2 "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_smap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_sorted "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_swap "Multisets need no list representation"
#rocq_ignore cryptis.SMS.Internal.wf_to "Multisets need no list representation"

/-! ### Bind and map -/

section Bind

-- `bind` needs no decidable equality on its domain, but most lemmas about it do.
set_option linter.unusedSectionVars false

/-- Substitute `f x` for each occurrence of `x`, negating it for negative occurrences. -/
@[rocq_alias cryptis.SMS.bind]
def bind (f : T → SMS U) (s : SMS T) : SMS U :=
  make (s.posPart.bind (fun x => (f x).posPart) + s.negPart.bind (fun x => (f x).negPart))
    (s.posPart.bind (fun x => (f x).negPart) + s.negPart.bind (fun x => (f x).posPart))

theorem count_bind_parts (z : U) (f : T → SMS U) (X Y : Multiset T) :
    (make (X.bind (fun x => (f x).posPart) + Y.bind (fun x => (f x).negPart))
      (X.bind (fun x => (f x).negPart) + Y.bind (fun x => (f x).posPart))).count z =
    (X.map fun x => (f x).count z).sum - (Y.map fun x => (f x).count z).sum := by
  rw [count_make]
  induction X using Multiset.induction_on with
  | empty =>
    induction Y using Multiset.induction_on with
    | empty => simp
    | cons y Y ih => simp only [Multiset.count_add, count] at ih ⊢; simp at ih ⊢; omega
  | cons x X ih => simp only [Multiset.count_add, count] at ih ⊢; simp at ih ⊢; omega

@[rocq_alias cryptis.SMS.count_bind, rocq_alias cryptis.SMS.car_bind]
theorem count_bind (z : U) (f : T → SMS U) (s : SMS T) :
    (s.bind f).count z =
      (s.posPart.map fun x => (f x).count z).sum - (s.negPart.map fun x => (f x).count z).sum :=
  count_bind_parts z f _ _

@[rocq_alias cryptis.SMS.bind_make]
theorem bind_make (f : T → SMS U) (X Y : Multiset T) :
    (make X Y).bind f =
      make (X.bind (fun x => (f x).posPart) + Y.bind (fun x => (f x).negPart))
        (X.bind (fun x => (f x).negPart) + Y.bind (fun x => (f x).posPart)) := by
  ext z
  rw [count_bind, count_bind_parts, posPart_make, negPart_make]
  have hX : (X.map fun x => (f x).count z).sum =
      ((X - Y).map fun x => (f x).count z).sum + ((X ∩ Y).map fun x => (f x).count z).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter X Y]
    rw [Multiset.map_add, Multiset.sum_add]
  have hY : (Y.map fun x => (f x).count z).sum =
      ((Y - X).map fun x => (f x).count z).sum + ((X ∩ Y).map fun x => (f x).count z).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Y X]
    rw [Multiset.map_add, Multiset.sum_add, Multiset.inter_comm]
  omega

@[simp, rocq_alias cryptis.SMS.bind_empty]
theorem bind_zero (f : T → SMS U) : (0 : SMS T).bind f = 0 :=
  ext fun z => by simp [count_bind]

@[simp, rocq_alias cryptis.SMS.bind_singleton]
theorem bind_singleton (f : T → SMS U) (x : T) : ({x} : SMS T).bind f = f x :=
  ext fun z => by simp [count_bind]

@[simp, rocq_alias cryptis.SMS.bind_disj_union]
theorem bind_add (f : T → SMS U) (s t : SMS T) : (s + t).bind f = s.bind f + t.bind f := by
  change (make _ _).bind f = _
  ext z
  rw [bind_make, count_bind_parts, count_add, count_bind, count_bind]
  simp only [Multiset.map_add, Multiset.sum_add]
  omega

@[simp, rocq_alias cryptis.SMS.bind_inv]
theorem bind_neg (f : T → SMS U) (s : SMS T) : (-s).bind f = -s.bind f :=
  ext fun z => by simp [count_bind]

@[rocq_alias cryptis.SMS.bind_make_cons_l]
theorem bind_make_cons_left (f : T → SMS U) (x : T) (X Y : Multiset T) :
    (make (x ::ₘ X) Y).bind f = f x + (make X Y).bind f := by
  rw [make_cons_left, bind_add, bind_singleton]

@[rocq_alias cryptis.SMS.bind_make_cons_r]
theorem bind_make_cons_right (f : T → SMS U) (y : T) (X Y : Multiset T) :
    (make X (y ::ₘ Y)).bind f = -f y + (make X Y).bind f := by
  rw [make_cons_right, bind_add, bind_neg, bind_singleton]

@[rocq_alias cryptis.SMS.elem_of_bind]
theorem exists_mem_of_mem_bind {f : T → SMS U} {s : SMS T} {y : U} (h : y ∈ s.bind f) :
    ∃ x ∈ s, y ∈ f x := by
  rcases Multiset.mem_add.mp (mem_of_mem_make h) with h | h <;>
    rcases Multiset.mem_add.mp h with h | h <;>
    obtain ⟨x, hx, hy⟩ := Multiset.mem_bind.mp h
  · exact ⟨x, mem_of_mem_posPart hx, mem_of_mem_posPart hy⟩
  · exact ⟨x, mem_of_mem_negPart hx, mem_of_mem_negPart hy⟩
  · exact ⟨x, mem_of_mem_posPart hx, mem_of_mem_negPart hy⟩
  · exact ⟨x, mem_of_mem_negPart hx, mem_of_mem_posPart hy⟩

@[rocq_alias cryptis.SMS.bind_ext]
theorem bind_congr {f g : T → SMS U} {s : SMS T} (h : ∀ x ∈ s, f x = g x) :
    s.bind f = s.bind g := by
  ext z
  rw [count_bind, count_bind,
    Multiset.map_congr rfl fun x hx => by rw [h x (mem_of_mem_posPart hx)],
    Multiset.map_congr (s := s.negPart) rfl fun x hx => by rw [h x (mem_of_mem_negPart hx)]]

@[rocq_alias cryptis.SMS.bind_disj_union_l]
theorem bind_add_left (f g : T → SMS U) (s : SMS T) :
    s.bind (fun x => f x + g x) = s.bind f + s.bind g :=
  ext fun z => by simp [count_bind, Multiset.sum_map_add]; omega

@[rocq_alias cryptis.SMS.bind_inv_l]
theorem bind_neg_left (f : T → SMS U) (s : SMS T) : s.bind (fun x => -f x) = -s.bind f :=
  ext fun z => by simp [count_bind, Multiset.sum_map_neg]; omega

@[rocq_alias cryptis.SMS.bind_empty_l]
theorem bind_zero_left (s : SMS T) : s.bind (fun _ => (0 : SMS U)) = 0 :=
  ext fun z => by simp [count_bind]

/-- The image of a signed multiset. -/
@[rocq_alias cryptis.SMS.map]
def map (f : T → U) (s : SMS T) : SMS U := s.bind fun x => {f x}

@[rocq_alias cryptis.SMS.map_make]
theorem map_make (f : T → U) (X Y : Multiset T) :
    (make X Y).map f = make (X.map f) (Y.map f) := by
  simp [map, bind_make, Multiset.bind_singleton]

@[rocq_alias cryptis.SMS.map_pos_neg, rocq_alias cryptis.SMS.car_map]
theorem map_eq_make (f : T → U) (s : SMS T) : s.map f = make (s.posPart.map f) (s.negPart.map f) := by
  rw [← map_make, make_posPart_negPart]

@[rocq_alias cryptis.SMS.count_map_inj]
theorem count_map_of_injective {f : T → U} (hf : Function.Injective f) (x : T) (s : SMS T) :
    (s.map f).count (f x) = s.count x := by
  simp [map_eq_make, Multiset.count_map_eq_count' f _ hf, count]
  omega

@[rocq_alias cryptis.SMS.elem_of_map]
theorem exists_of_mem_map {f : T → U} {s : SMS T} {y : U} (h : y ∈ s.map f) :
    ∃ x ∈ s, y = f x := by
  obtain ⟨x, hx, hy⟩ := exists_mem_of_mem_bind h
  exact ⟨x, hx, mem_singleton.mp hy⟩

@[rocq_alias cryptis.SMS.elements_map_inj]
theorem elements_map_of_injective {f : T → U} (hf : Function.Injective f) (s : SMS T) :
    (s.map f).elements = s.elements.map f := by
  have hd : Disjoint (s.posPart.map f) (s.negPart.map f) :=
    Multiset.disjoint_left.mpr fun h₁ h₂ => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp h₁
      rw [Multiset.mem_map_of_injective hf] at h₂
      exact Multiset.disjoint_left.mp s.disjoint hx h₂
  rw [map_eq_make, make_of_disjoint hd]
  simp [elements]

theorem mem_map_of_injective {f : T → U} (hf : Function.Injective f) {x : T} {s : SMS T} :
    f x ∈ s.map f ↔ x ∈ s := by
  rw [← mem_elements, elements_map_of_injective hf, Multiset.mem_map_of_injective hf]
  rfl

@[simp, rocq_alias cryptis.SMS.map_singleton]
theorem map_singleton (f : T → U) (x : T) : ({x} : SMS T).map f = {f x} := bind_singleton _ _

@[simp, rocq_alias cryptis.SMS.map_empty]
theorem map_zero (f : T → U) : (0 : SMS T).map f = 0 := bind_zero _

@[simp, rocq_alias cryptis.SMS.map_disj_union]
theorem map_add (f : T → U) (s t : SMS T) : (s + t).map f = s.map f + t.map f := bind_add _ _ _

@[simp, rocq_alias cryptis.SMS.map_inv]
theorem map_neg (f : T → U) (s : SMS T) : (-s).map f = -s.map f := bind_neg _ _

@[rocq_alias cryptis.SMS.map_ext]
theorem map_congr {f g : T → U} {s : SMS T} (h : ∀ x ∈ s, f x = g x) : s.map f = s.map g :=
  bind_congr fun x hx => by rw [h x hx]

@[rocq_alias cryptis.SMS.map_map]
theorem map_map (f : T → U) (g : U → V) (s : SMS T) : (s.map f).map g = s.map (g ∘ f) := by
  rw [map_eq_make f, map_make, map_eq_make, Multiset.map_map, Multiset.map_map]

@[rocq_alias cryptis.SMS.bind_map]
theorem bind_map (f : U → SMS V) (g : T → U) (s : SMS T) :
    (s.map g).bind f = s.bind (f ∘ g) := by
  simp only [map_eq_make, bind_make, Multiset.bind_map]
  rfl

@[rocq_alias cryptis.SMS.bind_unit]
theorem bind_singleton_right (s : SMS T) : s.bind (fun x => {x}) = s := by
  change s.map id = s
  rw [map_eq_make, Multiset.map_id, Multiset.map_id, make_posPart_negPart]

@[rocq_alias cryptis.SMS.map_id_ext]
theorem map_eq_self {f : T → T} {s : SMS T} (h : ∀ x ∈ s, f x = x) : s.map f = s :=
  (map_congr (g := id) h).trans (bind_singleton_right s)

@[rocq_alias cryptis.SMS.map_bind]
theorem map_bind (f : U → V) (g : T → SMS U) (s : SMS T) :
    (s.bind g).map f = s.bind fun x => (g x).map f := by
  induction s using SMS.induction with
  | zero => simp
  | add x s ih => simp [ih]
  | sub x s ih => simp [ih]

@[rocq_alias cryptis.SMS.bind_bind]
theorem bind_bind (f : U → SMS V) (g : T → SMS U) (s : SMS T) :
    (s.bind g).bind f = s.bind fun x => (g x).bind f := by
  induction s using SMS.induction with
  | zero => simp
  | add x s ih => simp [ih]
  | sub x s ih => simp [ih]

@[rocq_alias cryptis.SMS.bind_comm]
theorem bind_comm (f : T → U → SMS V) (s : SMS T) (r : SMS U) :
    s.bind (fun x => r.bind (f x)) = r.bind fun y => s.bind fun x => f x y := by
  induction s using SMS.induction with
  | zero => simp [bind_zero_left]
  | add x s ih => simp [ih, bind_add_left]
  | sub x s ih => simp [ih, bind_add_left, bind_neg_left]

end Bind

/-! ### Filter -/

/-- The occurrences of the elements that satisfy `p`. -/
@[rocq_alias cryptis.SMS.filter]
def filter (p : T → Bool) (s : SMS T) : SMS T where
  posPart := s.posPart.filter (p ·)
  negPart := s.negPart.filter (p ·)
  disjoint := s.disjoint.mono (Multiset.filter_le _ _) (Multiset.filter_le _ _)

@[simp, rocq_alias cryptis.SMS.count_filter]
theorem count_filter (p : T → Bool) (z : T) (s : SMS T) :
    (s.filter p).count z = if p z then s.count z else 0 := by
  by_cases h : p z <;> simp [filter, count, h]


omit [DecidableEq T] in
@[simp]
theorem singleton_inj {x y : T} : ({x} : SMS T) = {y} ↔ x = y :=
  ⟨fun h => Multiset.singleton_inj.mp (congrArg posPart h), fun h => h ▸ rfl⟩

@[simp]
theorem singleton_ne_zero (x : T) : ({x} : SMS T) ≠ 0 :=
  fun h => by simpa using congrArg (count x) h

@[simp]
theorem singleton_add_singleton_ne_zero (x y : T) : ({x} + {y} : SMS T) ≠ 0 := fun h => by
  have := congrArg (count x) h
  simp only [count_add, count_singleton, count_zero] at this
  split_ifs at this <;> omega

theorem count_bind_congr {f g : T → SMS U} {s : SMS T} {y z : U}
    (h : ∀ x ∈ s, (f x).count y = (g x).count z) : (s.bind f).count y = (s.bind g).count z := by
  rw [count_bind, count_bind, Multiset.map_congr rfl fun x hx => h x (mem_of_mem_posPart hx),
    Multiset.map_congr (s := s.negPart) rfl fun x hx => h x (mem_of_mem_negPart hx)]

/-! ### Products in commutative groups

`SMS T` is the free abelian group on `T`: a map `f` into a commutative group extends to the
homomorphism `prod f`, which multiplies the images of the positive occurrences and divides by
those of the negative ones. -/

section Prod

-- `prod` needs no decidable equality, but most lemmas about it do.
set_option linter.unusedSectionVars false

variable {M : Type _} [CommGroup M]

/-- The product of the images of the elements of `s`, negative occurrences inverted. -/
@[to_additive /-- The sum of the images of the elements of `s`, negative occurrences negated. -/]
def prod (s : SMS T) (f : T → M) : M := (s.posPart.map f).prod / (s.negPart.map f).prod

@[to_additive (attr := simp)]
theorem prod_zero (f : T → M) : (0 : SMS T).prod f = 1 := by simp [prod]

@[to_additive (attr := simp)]
theorem prod_singleton (f : T → M) (x : T) : ({x} : SMS T).prod f = f x := by simp [prod]

@[to_additive (attr := simp)]
theorem prod_neg (f : T → M) (s : SMS T) : (-s).prod f = (s.prod f)⁻¹ := by simp [prod]

@[to_additive]
theorem prod_make (f : T → M) (X Y : Multiset T) :
    (make X Y).prod f = (X.map f).prod / (Y.map f).prod := by
  have hX := congrArg (fun Z => (Z.map f).prod) (Multiset.sub_add_inter X Y)
  have hY := congrArg (fun Z => (Z.map f).prod) (Multiset.sub_add_inter Y X)
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.inter_comm Y X] at hX hY
  rw [← hX, ← hY, prod, posPart_make, negPart_make, mul_div_mul_right_eq_div]

@[to_additive (attr := simp)]
theorem prod_add (f : T → M) (s t : SMS T) : (s + t).prod f = s.prod f * t.prod f := by
  change (make _ _).prod f = _
  rw [prod_make]
  simp [prod, div_mul_div_comm]

@[to_additive (attr := simp)]
theorem prod_sub (f : T → M) (s t : SMS T) : (s - t).prod f = s.prod f / t.prod f := by
  rw [sub_eq_add_neg, prod_add, prod_neg, div_eq_mul_inv]

/-- `prod f` as a homomorphism. -/
@[simps]
def prodHom (f : T → M) : Multiplicative (SMS T) →* M where
  toFun s := s.toAdd.prod f
  map_one' := prod_zero f
  map_mul' := prod_add f

@[to_additive]
theorem prod_congr {f g : T → M} {s : SMS T} (h : ∀ x ∈ s, f x = g x) : s.prod f = s.prod g := by
  rw [prod, prod, Multiset.map_congr rfl fun x hx => h x (mem_of_mem_posPart hx),
    Multiset.map_congr (s := s.negPart) rfl fun x hx => h x (mem_of_mem_negPart hx)]

@[to_additive]
theorem prod_bind (f : U → M) (g : T → SMS U) (s : SMS T) :
    (s.bind g).prod f = s.prod fun x => (g x).prod f := by
  induction s using SMS.induction with
  | zero => simp
  | add x s ih => simp [ih]
  | sub x s ih => simp [ih]

@[to_additive]
theorem prod_map (f : U → M) (g : T → U) (s : SMS T) : (s.map g).prod f = s.prod (f ∘ g) := by
  simp [map, prod_bind, Function.comp_def]

@[to_additive (attr := simp)]
theorem prod_const_one (s : SMS T) : s.prod (fun _ => (1 : M)) = 1 := by simp [prod]

@[to_additive]
theorem prod_eq_one {f : T → M} {s : SMS T} (h : ∀ x ∈ s, f x = 1) : s.prod f = 1 :=
  (prod_congr h).trans (prod_const_one s)

@[to_additive]
theorem map_prod {N F : Type _} [CommGroup N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (f : T → M) (s : SMS T) : φ (s.prod f) = s.prod fun x => φ (f x) := by
  simp [prod, map_div, map_multiset_prod, Multiset.map_map]

theorem count_eq_sum (x : T) (s : SMS T) : s.count x = s.sum fun y => if y = x then 1 else 0 := by
  induction s using SMS.induction with
  | zero => simp
  | add y s ih => simp [ih, count_singleton, eq_comm]
  | sub y s ih => simp [ih, count_singleton, eq_comm]

/-- `bind` is the sum of the substituted signed multisets. -/
theorem bind_eq_sum (f : T → SMS U) (s : SMS T) : s.bind f = s.sum f := by
  induction s using SMS.induction with
  | zero => simp
  | add x s ih => simp [ih]
  | sub x s ih => simp [ih]

end Prod

end SMS
end Cryptis
