module

public import Iris.BI.BigOp
public import Iris.ProofMode.Instances
public import Iris.ProofMode.InstancesFrame
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.UnionInter
public import Mathlib.Data.Finset.Basic

/-! Upstream candidate (Iris-Lean): big separating conjunctions over Mathlib's `Multiset` and
`Finset`, for `IrisMath`.

Iris-Lean's `[∗mset]` ranges over any instance of its class `LawfulFiniteMultiSet`, which brings
its own `∈` and `⊆`. To keep these apart from Mathlib's, the instance is on the type synonym
`Multiset.AsIris`, and `Multiset.toIris` views a multiset through it. The instance needs decidable
equality for union and difference, and reads the list of a multiset off its runtime
representation, so that definitions using these big operators stay computable.

- `[∗multiset] x ∈ s, Φ x` stands for `[∗mset] x ∈ s.toIris, Φ x`, so Iris-Lean's lemmas and
  proof-mode instances apply to it once the simp lemmas `Multiset.toIris_*` have rewritten
  Mathlib's operations into Iris-Lean's. `[∗finset] x ∈ s, Φ x` is the same over `s.val`.
- An elaborator and a delaborator read and print both notations.
- The namespaces `BigSepMultiset` and `BigSepFinset` restate the common Iris-Lean lemmas in terms
  of Mathlib's operations. -/

@[expose] public section

namespace Multiset

open Iris.Std

variable {α : Type _}

/-- Multisets as an instance of Iris-Lean's `LawfulFiniteMultiSet`. -/
def AsIris (α : Type _) : Type _ := Multiset α

/-- A multiset as an Iris-Lean multiset. -/
def toIris (s : Multiset α) : AsIris α := s

/-- An Iris-Lean multiset as a multiset. -/
def ofIris (s : AsIris α) : Multiset α := s

@[simp] theorem ofIris_toIris (s : Multiset α) : ofIris s.toIris = s := rfl

@[simp] theorem toIris_ofIris (s : AsIris α) : toIris (ofIris s) = s := rfl

theorem toIris_injective : Function.Injective (toIris : Multiset α → AsIris α) := fun _ _ h => h

/-- Reads off the list that represents a multiset at runtime. -/
unsafe def AsIris.toListUnsafe (s : AsIris α) : List α := Quot.unquot s

/-- `Multiset.toList`, computed from the runtime representation, so that big operators over
multisets are computable. -/
@[implemented_by AsIris.toListUnsafe]
def AsIris.toList (s : AsIris α) : List α := (ofIris s).toList

instance [DecidableEq α] : LawfulFiniteMultiSet (AsIris α) α where
  singleton a := toIris {a}
  emptyCollection := toIris 0
  union s t := toIris (ofIris s ∪ ofIris t)
  inter s t := toIris (ofIris s ∩ ofIris t)
  sdiff s t := toIris (ofIris s - ofIris t)
  multiplicity a s := (ofIris s).count a
  disjUnion s t := toIris (ofIris s + ofIris t)
  ext h := Multiset.ext.mpr h
  multiplicity_empty := count_zero _
  multiplicity_singleton_eq := count_singleton_self _
  multiplicity_singleton_ne h := by simp [h]
  multiplicity_disjUnion := count_add ..
  multiplicity_union := count_union ..
  multiplicity_intersection := count_inter ..
  multiplicity_difference := count_sub ..
  toList := AsIris.toList
  mem_toList := mem_toList.trans count_pos.symm
  toList_empty := toList_zero
  toList_singleton := toList_singleton _
  toList_disjUnion := coe_eq_coe.mp (by
    rw [AsIris.toList, coe_toList, AsIris.toList, AsIris.toList, ← coe_add, coe_toList, coe_toList]
    rfl)

variable [DecidableEq α] {s t : Multiset α} {a : α}

@[simp]
theorem mem_toIris : a ∈ s.toIris ↔ a ∈ s := count_pos

@[simp]
theorem multiplicity_toIris : MultiSet.multiplicity a s.toIris = s.count a := rfl

@[simp]
theorem toList_toIris : FiniteMultiSet.toList s.toIris = s.toList := rfl

@[simp]
theorem toIris_zero : (0 : Multiset α).toIris = ∅ := rfl

@[simp]
theorem toIris_singleton (a : α) : ({a} : Multiset α).toIris = {a} := rfl

@[simp]
theorem toIris_add (s t : Multiset α) : (s + t).toIris = s.toIris ⊎ t.toIris := rfl

@[simp]
theorem toIris_cons (a : α) (s : Multiset α) : (a ::ₘ s).toIris = {a} ⊎ s.toIris :=
  congrArg toIris (singleton_add a s).symm

@[simp]
theorem toIris_sub (s t : Multiset α) : (s - t).toIris = s.toIris \ t.toIris := rfl

@[simp]
theorem toIris_union (s t : Multiset α) : (s ∪ t).toIris = s.toIris ∪ t.toIris := rfl

@[simp]
theorem toIris_inter (s t : Multiset α) : (s ∩ t).toIris = s.toIris ∩ t.toIris := rfl

@[simp]
theorem toIris_erase (s : Multiset α) (a : α) : (s.erase a).toIris = s.toIris \ {a} := by
  rw [← sub_singleton, toIris_sub, toIris_singleton]

@[simp]
theorem toIris_subset_toIris : s.toIris ⊆ t.toIris ↔ s ≤ t := by
  simp [Iris.Std.subset_iff, le_iff_count]

end Multiset

namespace Iris.BI

open Iris.Std Iris.ProofMode BIBase Iris.BI.BigSepMS

/-- Big separating conjunction over a multiset: `[∗multiset] x ∈ s, Φ x` is
`[∗mset] x ∈ s.toIris, Φ x`. -/
syntax (name := bigSepMultisetStx) "[∗multiset] " ident " ∈ " term ", " term : term

/-- Big separating conjunction over a finset: `[∗finset] x ∈ s, Φ x` is
`[∗mset] x ∈ s.val.toIris, Φ x`. -/
syntax (name := bigSepFinsetStx) "[∗finset] " ident " ∈ " term ", " term : term

macro_rules
  | `(iprop([∗multiset] $x:ident ∈ $s, $P)) => `([∗multiset] $x ∈ $s, iprop($P))
  | `(iprop([∗finset] $x:ident ∈ $s, $P)) => `([∗finset] $x ∈ $s, iprop($P))

section Elab
open Lean Elab Term Meta

/-- Elaborates `[∗mset] x ∈ X, P`, where `X` is `s.toIris` for a multiset `s`, or `s.val.toIris`
for a finset `s`. The collection `s` is elaborated first, so that `x` gets its element type even
when `P` only uses `x` through a coercion. -/
meta def elabBigSepCollection (tk x : Syntax) (s P : Syntax) (finset : Bool)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (.succ u))
  let s ← elabTermEnsuringType s (mkApp (.const (if finset then ``Finset else ``Multiset) [u]) α)
  synthesizeSyntheticMVars (postpone := .yes)
  let sStx ← exprToSyntax s
  let αStx ← exprToSyntax (← instantiateMVars α)
  let X ← if finset then `(Multiset.toIris (Finset.val $sStx)) else `(Multiset.toIris $sStx)
  elabTerm (← `($(wrapIprop tk ``bigSepMS) (fun ($(⟨x⟩) : $αStx) => $(⟨P⟩)) $X)) expectedType?

@[term_elab bigSepMultisetStx, inherit_doc bigSepMultisetStx]
meta def elabBigSepMultiset : TermElab := fun stx expectedType? => do
  let `([∗multiset]%$tk $x:ident ∈ $s, $P) := stx | throwUnsupportedSyntax
  elabBigSepCollection tk x s P false expectedType?

@[term_elab bigSepFinsetStx, inherit_doc bigSepFinsetStx]
meta def elabBigSepFinset : TermElab := fun stx expectedType? => do
  let `([∗finset]%$tk $x:ident ∈ $s, $P) := stx | throwUnsupportedSyntax
  elabBigSepCollection tk x s P true expectedType?

end Elab

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- Shows `[∗mset] x ∈ s.toIris, P` as `[∗multiset] x ∈ s, P`, and as `[∗finset] x ∈ t, P` when
`s` is `t.val`. -/
@[delab app.Iris.BI.bigSepMS]
meta def delabBigSepMultiset : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let .lam xn _ _ _ := e.getArg! 5 | failure
  let X := e.getArg! 6
  guard (X.isAppOfArity ``Multiset.toIris 2)
  let P ← withNaryArg 5 <| withBindingBody xn delab
  let x := mkIdent xn
  if (X.getArg! 1).isAppOfArity ``Finset.val 2 then
    let s ← withNaryArg 6 <| withNaryArg 1 <| withNaryArg 1 delab
    `([∗finset] $x ∈ $s, $P)
  else
    let s ← withNaryArg 6 <| withNaryArg 1 delab
    `([∗multiset] $x ∈ $s, $P)

end Delab

instance isDisjUnion_toIris_add {α : Type _} [DecidableEq α] (s t : Multiset α) :
    IsDisjUnion (A := α) (s + t).toIris s.toIris t.toIris where
  is_disj_union := rfl

instance intoSep_bigSepMultiset_add {PROP : Type _} [BI PROP] {α : Type _} [DecidableEq α]
    (Φ : α → PROP)
    (s t : Multiset α) :
    IntoSep ([∗multiset] x ∈ s + t, Φ x) ([∗multiset] x ∈ s, Φ x) ([∗multiset] x ∈ t, Φ x) where
  into_sep := bigSepMS_disjUnion.mp

instance fromSep_bigSepMultiset_add {PROP : Type _} [BI PROP] {α : Type _} [DecidableEq α]
    (Φ : α → PROP)
    (s t : Multiset α) :
    FromSep ([∗multiset] x ∈ s + t, Φ x) ([∗multiset] x ∈ s, Φ x) ([∗multiset] x ∈ t, Φ x) where
  from_sep := bigSepMS_disjUnion.mpr

namespace BigSepMultiset

variable {PROP : Type _} [BI PROP] {α β : Type _} [DecidableEq α] [DecidableEq β] {Φ Ψ : α → PROP}
  {s t : Multiset α} {a : α}
local bi PROP

theorem bigSepMultiset_toList : ([∗multiset] x ∈ s, Φ x) ⊣⊢ [∗list] x ∈ s.toList, Φ x :=
  bigSepMS_elements

theorem bigSepMultiset_coe (l : List α) :
    ([∗multiset] x ∈ (l : Multiset α), Φ x) ⊣⊢ [∗list] x ∈ l, Φ x :=
  bigSepMultiset_toList.trans <| .of_eq <|
    Iris.Algebra.BigOpL.bigOpL_eq_of_perm _ (Multiset.coe_eq_coe.mp (Multiset.coe_toList _))

@[simp]
theorem bigSepMultiset_zero : ([∗multiset] x ∈ (0 : Multiset α), Φ x) ⊣⊢ emp :=
  bigSepMS_empty

theorem bigSepMultiset_singleton (a : α) :
    ([∗multiset] x ∈ ({a} : Multiset α), Φ x) ⊣⊢ Φ a :=
  bigSepMS_singleton

theorem bigSepMultiset_cons (a : α) (s : Multiset α) :
    ([∗multiset] x ∈ a ::ₘ s, Φ x) ⊣⊢ Φ a ∗ [∗multiset] x ∈ s, Φ x := by
  rw [Multiset.toIris_cons]
  exact bigSepMS_insert

theorem bigSepMultiset_add (s t : Multiset α) :
    ([∗multiset] x ∈ s + t, Φ x) ⊣⊢ ([∗multiset] x ∈ s, Φ x) ∗ [∗multiset] x ∈ t, Φ x :=
  bigSepMS_disjUnion

theorem bigSepMultiset_erase (h : a ∈ s) :
    ([∗multiset] x ∈ s, Φ x) ⊣⊢ Φ a ∗ [∗multiset] x ∈ s.erase a, Φ x := by
  rw [Multiset.toIris_erase]
  exact bigSepMS_delete (Multiset.mem_toIris.mpr h)

theorem bigSepMultiset_map (f : β → α) (s : Multiset β) :
    ([∗multiset] x ∈ s.map f, Φ x) ⊣⊢ [∗multiset] x ∈ s, Φ (f x) := by
  induction s using Multiset.induction_on with
  | empty => exact bigSepMultiset_zero.trans bigSepMultiset_zero.symm
  | cons b s ih =>
    rw [Multiset.map_cons]
    exact (bigSepMultiset_cons _ _).trans <| (sep_congr .rfl ih).trans
      (bigSepMultiset_cons (Φ := fun x => Φ (f x)) b s).symm

theorem bigSepMultiset_attach (s : Multiset α) :
    ([∗multiset] x ∈ s.attach, Φ x.1) ⊣⊢ [∗multiset] x ∈ s, Φ x := by
  rw [← (bigSepMultiset_map Subtype.val s.attach).to_eq, Multiset.attach_map_val]
  exact .rfl

theorem bigSepMultiset_mono (h : ∀ x ∈ s, Φ x ⊢ Ψ x) :
    ([∗multiset] x ∈ s, Φ x) ⊢ [∗multiset] x ∈ s, Ψ x :=
  bigSepMS_mono fun hx => h _ (Multiset.mem_toIris.mp hx)

theorem bigSepMultiset_congr (h : ∀ x ∈ s, Φ x ⊣⊢ Ψ x) :
    ([∗multiset] x ∈ s, Φ x) ⊣⊢ [∗multiset] x ∈ s, Ψ x :=
  bigSepMS_eqv fun hx => h _ (Multiset.mem_toIris.mp hx)

theorem bigSepMultiset_mem [∀ x, Affine (Φ x)] (h : a ∈ s) : ([∗multiset] x ∈ s, Φ x) ⊢ Φ a :=
  bigSepMS_elem_of (Multiset.mem_toIris.mpr h)

theorem bigSepMultiset_forall [BIAffine PROP] [∀ x, Persistent (Φ x)] :
    ([∗multiset] x ∈ s, Φ x) ⊣⊢ ∀ x, ⌜x ∈ s⌝ → Φ x :=
  bigSepMS_forall.trans <| forall_congr fun _ => imp_congr_left (pure_congr Multiset.mem_toIris)

end BigSepMultiset

namespace BigSepFinset

open BigSepMultiset

variable {PROP : Type _} [BI PROP] {α : Type _} [DecidableEq α] {Φ Ψ : α → PROP} {s t : Finset α}
  {a : α}
local bi PROP

@[simp]
theorem bigSepFinset_empty : ([∗finset] x ∈ (∅ : Finset α), Φ x) ⊣⊢ emp := bigSepMS_empty

theorem bigSepFinset_singleton (a : α) : ([∗finset] x ∈ ({a} : Finset α), Φ x) ⊣⊢ Φ a :=
  bigSepMS_singleton

theorem bigSepFinset_insert (h : a ∉ s) :
    ([∗finset] x ∈ insert a s, Φ x) ⊣⊢ Φ a ∗ [∗finset] x ∈ s, Φ x := by
  rw [Finset.insert_val_of_notMem h]
  exact bigSepMultiset_cons a s.val

theorem bigSepFinset_union (h : Disjoint s t) :
    ([∗finset] x ∈ s ∪ t, Φ x) ⊣⊢ ([∗finset] x ∈ s, Φ x) ∗ [∗finset] x ∈ t, Φ x := by
  rw [← Finset.disjUnion_eq_union s t h]
  exact bigSepMultiset_add s.val t.val

theorem bigSepFinset_erase (h : a ∈ s) :
    ([∗finset] x ∈ s, Φ x) ⊣⊢ Φ a ∗ [∗finset] x ∈ s.erase a, Φ x :=
  bigSepMultiset_erase h

theorem bigSepFinset_mono (h : ∀ x ∈ s, Φ x ⊢ Ψ x) :
    ([∗finset] x ∈ s, Φ x) ⊢ [∗finset] x ∈ s, Ψ x :=
  bigSepMultiset_mono h

theorem bigSepFinset_congr (h : ∀ x ∈ s, Φ x ⊣⊢ Ψ x) :
    ([∗finset] x ∈ s, Φ x) ⊣⊢ [∗finset] x ∈ s, Ψ x :=
  bigSepMultiset_congr h

theorem bigSepFinset_mem [∀ x, Affine (Φ x)] (h : a ∈ s) : ([∗finset] x ∈ s, Φ x) ⊢ Φ a :=
  bigSepMultiset_mem h

theorem bigSepFinset_forall [BIAffine PROP] [∀ x, Persistent (Φ x)] :
    ([∗finset] x ∈ s, Φ x) ⊣⊢ ∀ x, ⌜x ∈ s⌝ → Φ x :=
  bigSepMultiset_forall

end BigSepFinset

end Iris.BI
