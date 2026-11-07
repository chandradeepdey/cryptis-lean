module

public import Iris.Init
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Basic

/-! Sorting lists into canonical form.

Sorting with `List.mergeSort` by a lawful `Ord` puts lists in canonical form: two lists have the
same sorted form exactly when they are permutations of each other. The other list operations that
canonical forms need, such as `List.erase` and `List.count`, come from core Lean and Mathlib. -/

@[expose] public section

attribute [rocq_alias cryptis.rem] List.erase
attribute [rocq_alias cryptis.elem_of_rem] List.mem_of_mem_erase
attribute [rocq_alias cryptis.length_rem] List.length_erase_of_mem
attribute [rocq_alias cryptis.count_mem] List.count
attribute [rocq_alias cryptis.count_mem_app] List.count_append
attribute [rocq_alias cryptis.count_mem_Permutation] List.Perm.count_eq
attribute [rocq_alias cryptis.count_mem_rem] List.count_erase
attribute [rocq_alias cryptis.rem_Permutation] List.perm_cons_erase
attribute [rocq_alias cryptis.Permutation_count_mem] List.perm_iff_count
attribute [rocq_alias cryptis.submseteq_count_mem] List.subperm_ext_iff
attribute [rocq_alias cryptis.list_bind_fmap] List.map_flatMap
attribute [rocq_alias cryptis.elem_of_merge_sort] List.mem_mergeSort
attribute [rocq_alias cryptis.length_merge_sort] List.length_mergeSort
attribute [rocq_alias cryptis.merge_sort_id] List.mergeSort_of_pairwise
attribute [rocq_alias cryptis.merge_sort_fmap] List.map_mergeSort
attribute [rocq_alias cryptis.count_mem_fmap] List.count_map_of_injective
attribute [rocq_alias cryptis.fmap_rem] List.map_erase

#rocq_ignore cryptis.rem_submseteq "List.erase_sublist"
#rocq_ignore cryptis.elem_of_count_mem "List.count_pos_iff"
#rocq_ignore cryptis.not_elem_of_count_mem "List.count_eq_zero"
#rocq_ignore cryptis.Forall_merge_sort "Use List.mem_mergeSort"
#rocq_ignore cryptis.sum_list_with_Permutation "Unused; List.Perm.sum_eq if needed"
#rocq_ignore cryptis.list_disjoint_dec "List.Disjoint is not used as a decidable proposition"

namespace List

variable {α β : Type _}

section Ord

variable [Ord α]

/-- The order that `List.mergeSort` sorts by. -/
abbrev leOrd (a b : α) : Bool := (compare a b).isLE

theorem leOrd_trans [Std.TransOrd α] (a b c : α) : leOrd a b → leOrd b c → leOrd a c :=
  Std.TransCmp.isLE_trans

theorem leOrd_total [Std.TransOrd α] (a b : α) : leOrd a b || leOrd b a := by
  simp only [leOrd]
  rw [Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering)) (a := a) (b := b)]
  cases compare b a <;> rfl

theorem leOrd_antisymm [Std.TransOrd α] [Std.LawfulEqOrd α] (a b : α) : leOrd a b → leOrd b a → a = b := fun h₁ h₂ =>
  Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h₁ h₂)

@[rocq_alias cryptis.merge_sort_sorted]
theorem pairwise_mergeSort_leOrd [Std.TransOrd α] (l : List α) : (l.mergeSort leOrd).Pairwise (leOrd · ·) :=
  pairwise_mergeSort leOrd_trans leOrd_total l

/-- Lists sorted by a lawful `Ord` are equal as soon as they are permutations. -/
theorem Perm.eq_of_pairwise_leOrd [Std.TransOrd α] [Std.LawfulEqOrd α] {l₁ l₂ : List α} (h : l₁ ~ l₂)
    (h₁ : l₁.Pairwise (leOrd · ·)) (h₂ : l₂.Pairwise (leOrd · ·)) : l₁ = l₂ :=
  h.eq_of_pairwise (fun a b _ _ => leOrd_antisymm a b) h₁ h₂

@[rocq_alias cryptis.merge_sort_Permutation_eq]
theorem mergeSort_eq_of_perm [Std.TransOrd α] [Std.LawfulEqOrd α] {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    l₁.mergeSort leOrd = l₂.mergeSort leOrd :=
  ((mergeSort_perm l₁ _).trans (h.trans (mergeSort_perm l₂ _).symm)).eq_of_pairwise_leOrd
    (pairwise_mergeSort_leOrd l₁) (pairwise_mergeSort_leOrd l₂)

@[rocq_alias cryptis.merge_sort_eq_Permutation]
theorem perm_of_mergeSort_eq {l₁ l₂ : List α} (h : l₁.mergeSort leOrd = l₂.mergeSort leOrd) :
    l₁ ~ l₂ :=
  (mergeSort_perm l₁ _).symm.trans (h ▸ mergeSort_perm l₂ _)

end Ord

end List
