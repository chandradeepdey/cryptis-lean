module

public import Mathlib.Data.List.Perm.Basic
public import Iris.HeapLang.Lib.NondetBool
public import Iris.HeapLang.Metatheory
public import Iris.Std.GenSets

/-! Miscellaneous definitions and lemmas.

- Lists: permutations of mapped lists.
- Finite maps and sets: singletons, and relations given by sets of pairs that are one-to-one.
- Lists of a given length: quantifiers over the lists of length `n`, and tuples built from them.
- Binders: insertion into and deletion from maps at a HeapLang binder.
- Pure expressions: HeapLang expressions whose evaluation only takes pure steps.
- Nondeterministic numbers: HeapLang programs that return an arbitrary natural number or
  integer. -/

@[expose] public section

/-! ## Lists -/

namespace List

variable {α β : Type _}

/-- A permutation of a mapped list is itself a mapped list. -/
@[rocq_alias cryptis.Permutation_fmap_inv_l]
theorem exists_perm_of_map_perm (f : α → β) {xs : List α} {ys : List β}
    (h : xs.map f ~ ys) : ∃ xs', ys = xs'.map f ∧ xs ~ xs' := by
  obtain ⟨xs', h₁, h₂⟩ :=
    (congrFun (congrFun (eq_map_comp_perm f) ys) xs).mpr h.symm
  exact ⟨xs', h₁, h₂.symm⟩

end List

attribute [rocq_alias cryptis.list_fmap_perm_inj] List.map_perm_map_iff

#rocq_ignore cryptis.eq_op_bool_decide "mathcomp `eqType` bridge; Lean has a single `DecidableEq`."
#rocq_ignore cryptis.sum_list_with_fmap
  "`sum_list_with f l` is `(l.map f).sum`, and the lemma is `List.map_map`."
#rocq_ignore cryptis.union_list_fmap_mono
  "Monotonicity of a union indexed by a list; it belongs to the set type chosen for nonces."

namespace Cryptis

/-! ## Finite maps and sets -/

universe u

section Maps

open Iris.Std PartialMap

variable {M : Type _ → Type _} {K V : Type _} [LawfulPartialMap M K]

@[rocq_alias cryptis.dom_singleton_eq]
theorem exists_eq_singleton_of_mem_iff [DecidableEq K] {m : M V} {x : K}
    (h : ∀ k, k ∈ m ↔ k = x) : ∃ y, m = {[x := y]} := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((h x).mpr rfl)
  refine ⟨y, equiv_iff_eq.mp fun k => ?_⟩
  by_cases hk : x = k
  · subst hk; rw [hy, LawfulPartialMap.get?_singleton_eq rfl]
  · rw [LawfulPartialMap.get?_singleton_ne hk]
    exact Option.not_isSome_iff_eq_none.mp fun hm => hk ((h k).mp hm).symm

@[rocq_alias cryptis.singleton_inj]
theorem singleton_injective {S A : Type _} [LawfulSet S A] :
    Function.Injective (fun x : A => ({x} : S)) := fun x _ (h : ({x} : S) = _) =>
  mem_singleton.mp (h ▸ mem_singleton.mpr rfl)

end Maps

#rocq_ignore cryptis.option_Forall2E "`Option.Forall₂` is defined by this case analysis."
#rocq_ignore cryptis.option_equivE
  "The option OFE relates options by `Option.Forall₂`, which is defined by this case analysis."

/-- The pairs in `X` relate elements one-to-one. -/
@[rocq_alias cryptis.perm]
def IsPerm {α S : Type _} [Membership (α × α) S] (X : S) : Prop :=
  ∀ p₁ ∈ X, ∀ p₂ ∈ X, (p₁.1 = p₂.1 ↔ p₁.2 = p₂.2)

/-- Apply `f` to `x` and `y`, swapped unless `b`. -/
@[rocq_alias cryptis.flipb]
def flipb {α β : Type _} (b : Bool) (f : α → α → β) (x y : α) : β :=
  f (if b then x else y) (if b then y else x)

/-! ## Lists of a given length -/

/-- `nforall n P` is `∀ x₁ … xₙ, P [x₁, …, xₙ]`. -/
@[rocq_alias cryptis.nforall]
def nforall {α : Type _} : Nat → (List α → Prop) → Prop
  | 0, P => P []
  | n + 1, P => ∀ x, nforall n (fun xs => P (x :: xs))

@[rocq_alias cryptis.nforallP]
theorem nforall_iff {α : Type _} {n : Nat} {P : List α → Prop} :
    nforall n P ↔ ∀ xs, n = xs.length → P xs := by
  induction n generalizing P with
  | zero =>
    exact ⟨fun h xs hl => List.eq_nil_of_length_eq_zero hl.symm ▸ h, fun h => h [] rfl⟩
  | succ n ih =>
    simp only [nforall, ih]
    refine ⟨fun h xs hl => ?_, fun h x xs hl => h (x :: xs) (by simp [hl])⟩
    cases xs with
    | nil => simp at hl
    | cons x xs => exact h x xs (by simpa using hl)

/-- `nforallEq n xs P` is `∀ x₁ … xₙ, xs = [x₁, …, xₙ] → P [x₁, …, xₙ]`. -/
@[rocq_alias cryptis.nforall_eq]
def nforallEq {α : Type _} (n : Nat) (xs : List α) (P : List α → Prop) : Prop :=
  nforall n fun xs' => xs = xs' → P xs'

@[rocq_alias cryptis.nforall_eqP]
theorem nforallEq_iff {α : Type _} {n : Nat} {xs : List α} {P : List α → Prop} :
    nforallEq n xs P ↔ (n = xs.length → P xs) := by
  simp only [nforallEq, nforall_iff]
  exact ⟨fun h hl => h xs hl rfl, fun h _ hl e => e ▸ h (e ▸ hl)⟩

/-- Prove a property of all lists by treating the lists of length `n` separately. -/
@[rocq_alias cryptis.list_len_rect]
theorem list_len_rect {α : Type _} (n : Nat) (P : List α → Prop) (h₁ : nforall n P)
    (h₂ : ∀ xs, xs.length ≠ n → P xs) (xs : List α) : P xs :=
  if h : n = xs.length then nforall_iff.mp h₁ xs h else h₂ xs (Ne.symm h)

/-! ## Tuples from lists -/

/-- The type `α × ⋯ × α` of `n` elements, or `Unit` when `n = 0`. -/
@[rocq_alias cryptis.prod_of_list_type]
def ProdOfListType (α : Type u) : Nat → Type u
  | 0 => PUnit
  | 1 => α
  | n + 2 => α × ProdOfListType α (n + 1)

/-- The tuple of the elements of a list of length `n`. -/
@[rocq_alias cryptis.prod_of_list]
def prodOfList {α : Type u} : (n : Nat) → List α → Option (ProdOfListType α n)
  | 0, [] => some ⟨⟩
  | 1, [x] => some x
  | n + 2, x :: xs => (prodOfList (n + 1) xs).map ((x, ·))
  | _, _ => none

#rocq_ignore cryptis.prod_of_list_aux_type
  "Tuples are nested to the right, so `ProdOfListType` needs no accumulator."
#rocq_ignore cryptis.prod_of_list_aux
  "Tuples are nested to the right, so `prodOfList` needs no accumulator."

@[rocq_alias cryptis.prod_of_list_neq]
theorem prodOfList_eq_none {α : Type _} {n : Nat} {xs : List α} (h : xs.length ≠ n) :
    prodOfList n xs = none := by
  induction xs generalizing n with
  | nil => cases n <;> simp_all [prodOfList]
  | cons x xs ih =>
    match n, xs with
    | 0, _ => rfl
    | 1, [] => simp at h
    | 1, _ :: _ => rfl
    | n + 2, xs => rw [prodOfList, ih (by simpa using h)]; rfl

/-! ## Binders -/

section Binders

open Iris.Std Iris.HeapLang LawfulPartialMap

variable {M : Type u → Type _} {V V' : Type u} [LawfulPartialMap M String]

@[rocq_alias cryptis.fmap_binder_delete]
theorem map_deleteMap (f : V → V') (m : M V) (b : Binder) :
    Iris.Std.PartialMap.map f (b.deleteMap m) = b.deleteMap (Iris.Std.PartialMap.map f m) := by
  cases b
  · rfl
  · exact map_delete

@[rocq_alias cryptis.fmap_binder_insert]
theorem map_insertMap (f : V → V') (m : M V) (b : Binder) (x : V) :
    Iris.Std.PartialMap.map f (b.insertMap x m) =
      b.insertMap (f x) (Iris.Std.PartialMap.map f m) := by
  cases b
  · rfl
  · exact map_insert

@[rocq_alias cryptis.insert_same]
theorem insert_congr {m₁ m₂ : M V} {i : String} (x : V)
    (h : ∀ j, j ≠ i → PartialMap.get? m₁ j = PartialMap.get? m₂ j) :
    PartialMap.insert m₁ i x = PartialMap.insert m₂ i x := by
  refine equiv_iff_eq.mp fun j => ?_
  by_cases hj : i = j
  · rw [get?_insert_eq hj, get?_insert_eq hj]
  · rw [get?_insert_ne hj, get?_insert_ne hj, h j (Ne.symm hj)]

@[rocq_alias cryptis.binder_insert_same]
theorem insertMap_congr {m₁ m₂ : M V} {b : Binder} (x : V)
    (h : ∀ j : String, .named j ≠ b → PartialMap.get? m₁ j = PartialMap.get? m₂ j) :
    b.insertMap x m₁ = b.insertMap x m₂ := by
  cases b with
  | anon => exact equiv_iff_eq.mp fun j => h j nofun
  | named i => exact insert_congr x fun j hj => h j (by simpa using hj)

@[rocq_alias cryptis.binder_insert_delete]
theorem insertMap_deleteMap (m : M V) (b : Binder) (x : V) :
    b.insertMap x (b.deleteMap m) = b.insertMap x m := by
  cases b
  · rfl
  · exact insert_delete

@[rocq_alias cryptis.binder_delete_commute]
theorem deleteMap_comm (m : M V) (i j : Binder) :
    i.deleteMap (j.deleteMap m) = j.deleteMap (i.deleteMap m) := by
  cases i <;> cases j
  any_goals rfl
  exact delete_delete_comm

@[rocq_alias cryptis.binder_insert_delete2]
theorem insertMap_insertMap_deleteMap_deleteMap (m : M V) (i j : Binder) (x y : V) :
    i.insertMap x (j.insertMap y (i.deleteMap (j.deleteMap m))) =
      i.insertMap x (j.insertMap y m) := by
  refine insertMap_congr x fun k hk => ?_
  cases j with
  | anon =>
    cases i with
    | anon => rfl
    | named i => exact get?_delete_ne (by simpa [eq_comm] using hk)
  | named j =>
    by_cases hjk : j = k
    · rw [Binder.insertMap, Binder.insertMap, get?_insert_eq hjk, get?_insert_eq hjk]
    · rw [Binder.insertMap, Binder.insertMap, get?_insert_ne hjk, get?_insert_ne hjk]
      cases i with
      | anon => exact get?_delete_ne hjk
      | named i =>
        rw [Binder.deleteMap, Binder.deleteMap, get?_delete_ne (by simpa [eq_comm] using hk),
          get?_delete_ne hjk]

end Binders

/-! ## Pure expressions -/

section Pure

open Iris.HeapLang Iris.ProgramLogic Language Language.Notation EctxLanguage EctxItemLanguage

mutual
/-- Expressions whose evaluation only takes pure steps. -/
@[rocq_alias cryptis.pure_expr]
def pureExp : Exp → Bool
  | .val v => pureVal v
  | .var _ => true
  | .rec_ _ _ e => pureExp e
  | .app e₁ e₂ | .binop _ e₁ e₂ | .pair e₁ e₂ => pureExp e₁ && pureExp e₂
  | .unop _ e | .fst e | .snd e | .injL e | .injR e => pureExp e
  | .if e₀ e₁ e₂ | .case e₀ e₁ e₂ => pureExp e₀ && pureExp e₁ && pureExp e₂
  | _ => false

/-- Values whose closures only take pure steps. -/
@[rocq_alias cryptis.pure_val]
def pureVal : Val → Bool
  | .lit _ => true
  | .rec_ _ _ e => pureExp e
  | .pair v₁ v₂ => pureVal v₁ && pureVal v₂
  | .injL v | .injR v => pureVal v
end

/-- Evaluation-context items of pure expressions. -/
@[rocq_alias cryptis.pure_item]
def pureItem : ECtxItem → Bool
  | .appL v | .binOpL _ v | .pairL v => pureVal v
  | .appR e | .binOpR _ e | .pairR e => pureExp e
  | .unOp _ | .fst | .snd | .injL | .injR => true
  | .if e₁ e₂ | .case e₁ e₂ => pureExp e₁ && pureExp e₂
  | _ => false

/-- Evaluation contexts of pure expressions. -/
@[rocq_alias cryptis.pure_ctx]
def pureCtx (K : List ECtxItem) : Bool := K.all pureItem

@[rocq_alias cryptis.pure_expr_fill_item]
theorem pureExp_fillItem (a : ECtxItem) (e : Exp) :
    pureExp (a.fill e) = (pureItem a && pureExp e) := by
  cases a <;> simp [ECtxItem.fill, pureExp, pureItem, -val_to_ofVal, ToVal.ofVal, Bool.and_comm,
    Bool.and_assoc]

@[rocq_alias cryptis.pure_expr_fill]
theorem pureExp_fill (K : List ECtxItem) (e : Exp) :
    pureExp (fill K e) = (pureCtx K && pureExp e) := by
  induction K generalizing e with
  | nil => rfl
  | cons a K ih =>
    rw [fill_cons, ih]
    simp [pureCtx, fillItem, pureExp_fillItem, Bool.and_left_comm, Bool.and_assoc]

@[rocq_alias cryptis.subst_pure]
theorem pureExp_substStr {x : String} {v : Val} {e : Exp} (hv : pureVal v) (he : pureExp e) :
    pureExp (e.substStr x v) := by
  induction e using Exp.substStr.induct (x := x) <;>
    simp_all [Exp.substStr, pureExp, -val_to_ofVal]
  split <;> assumption

@[rocq_alias cryptis.subst'_pure]
theorem pureExp_subst {b : Binder} {v : Val} {e : Exp} (hv : pureVal v) (he : pureExp e) :
    pureExp (e.subst b v) := by
  cases b
  · exact he
  · exact pureExp_substStr hv he

theorem pureVal_of_unOp_eval {op : UnOp} {v v' : Val} (h : op.eval v = some v') :
    pureVal v' := by
  unfold UnOp.eval at h; split at h <;> cases h <;> rfl

theorem pureVal_of_binOp_eval {op : BinOp} {v₁ v₂ v : Val} (h : op.eval v₁ v₂ = some v) :
    pureVal v := by
  unfold BinOp.eval at h
  split at h
  · split at h <;> cases h; rfl
  · split at h <;> simp_all [Option.map_eq_some_iff] <;> grind [pureVal]

theorem pureExp_of_baseStep {e₁ e₂ : Exp} {σ₁ σ₂ : State} {κ : List Observation}
    {es : List Exp} (h : BaseStep e₁ σ₁ κ e₂ σ₂ es) (he : pureExp e₁) : pureExp e₂ := by
  induction h <;> simp_all [pureExp, pureVal, -val_to_ofVal, ToVal.ofVal]
  case betaS => exact pureExp_subst he.2 (pureExp_subst (by simpa [pureVal] using he.1) he.1)
  case unOpS => exact pureVal_of_unOp_eval (by assumption)
  case binOpS => exact pureVal_of_binOp_eval (by assumption)

@[rocq_alias cryptis.pure_exprP]
theorem pureExp_of_primStep {e₁ e₂ : Exp} {σ₁ σ₂ : State} {κ : List Observation}
    {es : List Exp} (h : (e₁, σ₁) -<κ>-> (e₂, σ₂, es)) (he : pureExp e₁) : pureExp e₂ := by
  obtain ⟨hb⟩ := h
  simp only [pureExp_fill, Bool.and_eq_true] at he ⊢
  exact ⟨he.1, pureExp_of_baseStep hb he.2⟩

@[rocq_alias cryptis.pure_expr_pure_step]
theorem purePrimStep_of_pureExp {e₁ e₂ : Exp} {σ₁ σ₂ : State} {κ : List Observation}
    {es : List Exp} (h : (e₁, σ₁) -<κ>-> (e₂, σ₂, es)) (he : pureExp e₁) : e₁ -ᵖ-> e₂ := by
  have once {φ : Prop} {e₁ e₂ : Exp} (hexec : PureExec φ 1 e₁ e₂) (hφ : φ) : e₁ -ᵖ-> e₂ :=
    match hexec.pureExec hφ with | .tail _ (.rfl _) h => h
  obtain ⟨hb⟩ := h
  simp only [pureExp_fill, Bool.and_eq_true] at he
  refine purePrimStep_fill (fill _) ?_
  cases hb
  all_goals try exact once inferInstance trivial
  case betaS heq => subst heq; exact once inferInstance trivial
  case unOpS h => exact once instPureExecUnOp h
  case binOpS h => exact once instPureExecBinOp h
  all_goals simp [pureExp] at he

end Pure

/-! ## Nondeterministic numbers -/

open Iris Iris.HeapLang BI ProgramLogic

/-- Count up from the argument, stopping at a nondeterministic point. -/
@[rocq_alias cryptis.nondet_nat_loop]
def nondetNatLoop : Val := hl_val%
  rec loop n := if &nondetBool #() then n else loop (n + #1)

/-- A nondeterministic natural number. -/
@[rocq_alias cryptis.nondet_nat]
def nondetNat : Val := hl_val% λ _, &nondetNatLoop #0

/-- A nondeterministic integer. -/
@[rocq_alias cryptis.nondet_int]
def nondetInt : Val := hl_val%
  λ _, let n := &nondetNat #(); if &nondetBool #() then n else -n

section NondetProofs

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

@[rocq_alias cryptis.wp_nondet_nat_loop]
theorem wp_nondetNatLoop (Ψ : Val → IProp GF) (m : Nat) :
    (∀ n : Nat, Ψ hl_val(#n)) ⊢ WP hl(&nondetNatLoop #m) {{ Ψ }} := by
  iintro H
  iloeb as IH generalizing %m
  wp_rec
  wp_apply nondetBool.spec $$ [//] with %b -
  cases b
  · wp_pures
    rw [show (m : Int) + 1 = ((m + 1 : Nat) : Int) by omega]
    iapply IH $$ H
  · wp_pures; iapply H

@[rocq_alias cryptis.wp_nondet_nat]
theorem wp_nondetNat (Ψ : Val → IProp GF) :
    (∀ n : Nat, Ψ hl_val(#n)) ⊢ WP hl(&nondetNat #()) {{ Ψ }} := by
  iintro H; wp_rec; iapply wp_nondetNatLoop Ψ 0 $$ H

@[rocq_alias cryptis.wp_nondet_int]
theorem wp_nondetInt (Ψ : Val → IProp GF) :
    (∀ n : Int, Ψ hl_val(#n)) ⊢ WP hl(&nondetInt #()) {{ Ψ }} := by
  iintro H
  wp_rec
  wp_apply wp_nondetNat with %n
  wp_pures
  wp_apply nondetBool.spec $$ [//] with %b -
  cases b
  · wp_pures; iapply H
  · wp_pures; iapply H

end NondetProofs

end Cryptis
