module

public import Iris.Std.Namespaces

/-! Upstream candidate (Iris-Lean): facts about namespaces, for `Iris/Std/Namespaces.lean` and
`Iris/Std/Positives.lean`. The operation `.@` is injective, the mask of a namespace contains the
position of the namespace and survives the removal of a disjoint namespace, and `Unit` is
countable. The tactic `solve_ndisj` proves common goals about the masks of namespaces. -/

@[expose] public section

open Iris.Std

theorem ndot_inj [Pos.Countable A] {N₁ N₂ : Namespace} {x₁ x₂ : A} :
    N₁.@x₁ = N₂.@x₂ ↔ N₁ = N₂ ∧ x₁ = x₂ := by
  simp [ndot, Pos.encode_inj.eq_iff, and_comm]

theorem flatten_mem_nclose (N : Namespace) : Pos.flatten N ∈ (↑N : CoPset) :=
  CoPset.elem_suffixes.mpr ⟨.xH, (Pos.app_1_left_id _).symm⟩

theorem nclose_subset_diff {E : CoPset} {N N' : Namespace} (h : (↑N : CoPset) ⊆ E)
    (hd : N ## N') : (↑N : CoPset) ⊆ E \ ↑N' :=
  fun p hp => LawfulSet.mem_diff.mpr ⟨h p hp, fun hq => hd p ⟨hp, hq⟩⟩

instance : Pos.Countable Unit where
  encode _ := 1
  decode _ := some ()
  decode_encode _ := rfl

public meta section

/-- `solve_ndisj` proves that the mask of a namespace is included in a mask built from `⊤`, the
masks of namespaces and differences with them, and that two namespaces `N.@x` and `N.@y` are
disjoint. -/
syntax "solve_ndisj" : tactic

macro_rules
  | `(tactic| solve_ndisj) => `(tactic| first
    | exact Iris.Std.LawfulSet.subset_refl
    | exact CoPset.subseteq_top
    | exact ndot_ne_disjoint _ (by decide)
    | apply nclose_subset_diff <;> solve_ndisj
    | apply nclose_subseteq' <;> solve_ndisj)

end
