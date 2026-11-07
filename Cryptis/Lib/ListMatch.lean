module

public import Cryptis.Lib.Encode
public import Cryptis.Lib.HeapLangLinter
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Metatheory

/-! Matching a HeapLang list against a fixed number of variables.

`hl(list_match [x, y] := e in k)` evaluates `e` to a list. If it has exactly two elements, it
binds them to `x` and `y` in `k`; otherwise it returns `none()`. It is implemented by
`listMatchLoop`, which applies the closure `λ x y _, k` to the elements of the list one at a
time, so the matched variables are bound by ordinary substitution. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic

/-- Apply a curried function `f` of `n` arguments and a unit to the elements of a list of
length `n`, or return `none()` if the list has another length. -/
def listMatchLoop : Val := hl_val%
  rec loop n f l :=
    match l with
    | none() => if n = #0 then f #() else none()
    | some(p) => if n = #0 then none() else loop (n - #1) (f (fst(p))) (snd(p))

/-- The function `λ x₁ … xₙ _, k`. -/
@[rocq_alias cryptis.close_vars]
def closeVars : List String → Exp → Exp
  | [], k => .rec_ .anon .anon k
  | x :: xs, k => .rec_ .anon (.named x) (closeVars xs k)

/-- The value of `closeVars vars k`. -/
def closeVarsV : List String → Exp → Val
  | [], k => .rec_ .anon .anon k
  | x :: xs, k => .rec_ .anon (.named x) (closeVars xs k)

instance instPureExecCloseVars {vars : List String} {k : Exp} :
    ProgramLogic.Language.PureExec True 1 (closeVars vars k) (closeVarsV vars k) := by
  cases vars <;> exact instPureExecRec

/-- Match the list `e` against the variables `vars` in `k`. -/
@[rocq_alias cryptis.list_match]
def listMatch (vars : List String) (e k : Exp) : Exp :=
  hl(v(&listMatchLoop) #(vars.length) &(closeVars vars k) &e)

/-- `list_match [x₁, …, xₙ] := e in k` matches the list `e` against `x₁, …, xₙ` in `k`. -/
syntax:10 (name := listMatchSyntax) "list_match " "[" ident,* "]" " := " hl_exp:10 " in " hl_exp:1 : hl_exp

macro_rules
  | `(hl(list_match [$xs,*] := $e in $k)) => do
    let names := xs.getElems.map fun x => Lean.Syntax.mkStrLit x.getId.toString
    `(listMatch [$names,*] hl($e) hl($k))

/-- Substitute the values `vs` for the variables `vars` in `k`, or `none()` if their lengths
differ. -/
@[rocq_alias cryptis.nsubst]
def nsubst : List String → List Val → Exp → Exp
  | [], [], k => k
  | x :: xs, v :: vs, k => (nsubst xs vs k).subst (.named x) v
  | _, _, _ => hl(v(none()))

attribute [rocq_alias cryptis.substC] Exp.substStr_substStr_ne

#rocq_ignore cryptis.list_match_aux "Done by the HeapLang loop `listMatchLoop`."
#rocq_ignore cryptis.subst_list_match_aux "`listMatchLoop` is a closed value."
#rocq_ignore cryptis.napp
  "`listMatchLoop` applies the closure itself, so no evaluation context is built."
#rocq_ignore cryptis.wp_close_vars "Part of `wp_listMatchLoop`."
#rocq_ignore cryptis.binder_vars "Free variables are not needed: the closure binds the variables."
#rocq_ignore cryptis.elem_of_binder_vars "Free variables are not needed."
#rocq_ignore cryptis.free_vars "Free variables are not needed: the closure binds the variables."
#rocq_ignore cryptis.subst_free_vars "Free variables are not needed."
#rocq_ignore cryptis.subst_free_vars_rem "Free variables are not needed."
#rocq_ignore cryptis.free_vars_subst "Free variables are not needed."
#rocq_ignore cryptis.free_vars_nsubst "Free variables are not needed."

@[rocq_alias cryptis.subst_close_vars]
theorem subst_closeVars (x : String) (v : Val) (vars : List String) (k : Exp) :
    (closeVars vars k).subst (.named x) v =
      closeVars vars (if x ∈ vars then k else k.subst (.named x) v) := by
  induction vars with
  | nil => simp [closeVars, Exp.subst]
  | cons y ys ih => by_cases h : x = y <;> simp_all [closeVars, Exp.subst]

@[rocq_alias cryptis.subst_list_match]
theorem subst_listMatch (x : String) (v : Val) (vars : List String) (e k : Exp) :
    (listMatch vars e k).subst (.named x) v =
      listMatch vars (e.subst (.named x) v) (if x ∈ vars then k else k.subst (.named x) v) := by
  unfold listMatch
  rw [← subst_closeVars]
  simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_listMatch_of_mem {x : String} {v : Val} {vars : List String} {e k : Exp}
    (h : x ∈ vars) :
    (listMatch vars e k).subst (.named x) v = listMatch vars (e.subst (.named x) v) k := by
  simp [subst_listMatch, h]

@[wp_expr_simp]
theorem subst_listMatch_of_not_mem {x : String} {v : Val} {vars : List String} {e k : Exp}
    (h : x ∉ vars) :
    (listMatch vars e k).subst (.named x) v =
      listMatch vars (e.subst (.named x) v) (k.subst (.named x) v) := by
  simp [subst_listMatch, h]

attribute [wp_expr_simp] List.mem_cons List.not_mem_nil _root_.or_false not_or

@[rocq_alias cryptis.subst_nsubst]
theorem subst_nsubst_of_mem {x : String} (v : Val) {vars : List String} (vs : List Val)
    (k : Exp) (h : x ∈ vars) : (nsubst vars vs k).subst (.named x) v = nsubst vars vs k := by
  induction vars generalizing vs with
  | nil => simp at h
  | cons y ys ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      by_cases hxy : x = y
      · subst hxy; exact Exp.subst_subst
      · rw [nsubst, Exp.subst_subst_ne (by simpa using hxy), ih ws (by simpa [hxy] using h)]

@[rocq_alias cryptis.subst_nsubst_nin]
theorem subst_nsubst_of_not_mem {x : String} (v : Val) {vars : List String}
    (vs : List Val) (k : Exp) (h : x ∉ vars) :
    (nsubst vars vs k).subst (.named x) v = nsubst vars vs (k.subst (.named x) v) := by
  induction vars generalizing vs with
  | nil => cases vs <;> rfl
  | cons y ys ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      simp only [List.mem_cons, not_or] at h
      rw [nsubst, nsubst, Exp.subst_subst_ne (by simpa using h.1), ih ws h.2]

theorem nsubst_cons (x : String) (xs : List String) (w : Val) (ws : List Val) (k : Exp) :
    nsubst (x :: xs) (w :: ws) k =
      nsubst xs ws (if x ∈ xs then k else k.subst (.named x) w) := by
  split <;> simp [nsubst, subst_nsubst_of_mem, subst_nsubst_of_not_mem, *]

section Specs

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {α : Type _} [Encode α]
local bi (IProp GF)

@[rocq_alias cryptis.wp_list_match_aux]
theorem wp_listMatchLoop (vars : List String) (vs : List Val) (k : Exp) (Ψ : Val → IProp GF) :
    (if vars.length = vs.length then WP (nsubst vars vs k) @ s; E {{ Ψ }} else Ψ hl_val(none())) ⊢
      WP hl(&listMatchLoop #(vars.length) &(closeVarsV vars k) &(encode vs)) @ s; E {{ Ψ }} := by
  induction vs generalizing vars k with
  | nil =>
    iintro H; wp_rec; simp only [encode_nil]; wp_pures
    cases vars with
    | nil => simp [closeVarsV, nsubst]; wp_pures; iexact H
    | cons x xs =>
      simp [Bool.beq_eq_decide_eq, show (xs.length : Int) + 1 ≠ 0 by omega]
      wp_pures; iexact H
  | cons w ws ih =>
    iintro H; wp_rec; simp only [encode_cons]; wp_pures
    cases vars with
    | nil => simp; wp_pures; iexact H
    | cons x xs =>
      simp [Bool.beq_eq_decide_eq, show (xs.length : Int) + 1 ≠ 0 by omega]
      wp_pures
      simp only [closeVarsV]
      wp_pures
      simp only [subst_closeVars]
      wp_pures
      rw [show (xs.length : Int) + 1 - 1 = xs.length by omega]
      iapply ih
      rw [nsubst_cons]
      iexact H

@[rocq_alias cryptis.wp_list_match]
theorem wp_listMatch (vars : List String) (vs : List α) (k : Exp) (Ψ : Val → IProp GF) :
    (if vars.length = vs.length then WP (nsubst vars (vs.map encode) k) @ s; E {{ Ψ }}
      else Ψ hl_val(none())) ⊢
      WP (listMatch vars (encode vs) k) @ s; E {{ Ψ }} := by
  iintro H
  unfold listMatch
  wp_pures
  rw [← encode_map_encode]
  iapply wp_listMatchLoop
  simp only [List.length_map]
  iexact H

end Specs

end Cryptis
