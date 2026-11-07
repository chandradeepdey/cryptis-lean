module

public import Iris.Init

/-! Lemmas about comparisons: `isLE` of `compare` as a decision of `≤`, and lexicographic
comparisons, including for orders that are being proved lawful by induction and are therefore not
yet `Std.TransCmp` instances. -/

@[expose] public section

theorem isLE_compare_eq_decide {α : Type _} [Ord α] [LE α] [Std.LawfulOrderOrd α] [DecidableLE α]
    (a b : α) : (compare a b).isLE = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact Std.isLE_compare

/-- A lexicographic comparison is decided by its tail when the heads are equal. -/
theorem isLE_compare_then {α : Type _} [Ord α] [Std.LawfulEqOrd α] [DecidableEq α] (a b : α)
    (x : Ordering) :
    ((compare a b).then x).isLE = if a = b then x.isLE else (compare a b).isLE := by
  split
  · subst_vars; simp
  · cases h : compare a b <;> simp_all [Std.LawfulEqCmp.compare_eq_iff_eq]

namespace Ordering

/-- `(cmp a b).then x` is transitive when `cmp` is transitive at `a, b, c` and the
tail comparisons `x, y, z` are transitive. -/
theorem then_isLE_trans {cmp : α → α → Ordering}
    (swap : ∀ {a b}, cmp a b = (cmp b a).swap) (eq : ∀ {a b}, cmp a b = .eq → a = b)
    {a b c : α} (trans : (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE)
    {x y z : Ordering} (h : x.isLE → y.isLE → z.isLE) :
    ((cmp a b).then x).isLE → ((cmp b c).then y).isLE → ((cmp a c).then z).isLE := by
  simp only [isLE_then_iff_or]
  rintro (hab | ⟨hab, hx⟩) (hbc | ⟨hbc, hy⟩)
  · left
    have hac := trans (by simp [hab]) (by simp [hbc])
    cases h : cmp a c
    · rfl
    · obtain rfl := eq h
      simp [swap (a := a), hbc, Ordering.swap] at hab
    · simp [h] at hac
  · obtain rfl := eq hbc
    exact .inl hab
  · obtain rfl := eq hab
    exact .inl hbc
  · obtain rfl := eq hab
    obtain rfl := eq hbc
    exact .inr ⟨hab, h hx hy⟩

/-- The instance version of `then_isLE_trans`. -/
theorem compare_then_isLE_trans [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] {a b c : α}
    {x y z : Ordering} (h : x.isLE → y.isLE → z.isLE) :
    ((compare a b).then x).isLE → ((compare b c).then y).isLE →
      ((compare a c).then z).isLE :=
  then_isLE_trans (cmp := compare) (a := a) (b := b) (c := c) Std.OrientedCmp.eq_swap Std.LawfulEqCmp.eq_of_compare
    Std.TransCmp.isLE_trans h

end Ordering
