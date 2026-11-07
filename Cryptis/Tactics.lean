module

public import Cryptis.Lib.ListMatch
public import Cryptis.Primitives

/-! Tactics for the symbolic execution of the Cryptis primitives.

Each tactic takes the pure steps of a goal `WP e {{ Φ }}`, applies the spec of a primitive to the
first matching subexpression of `e`, and simplifies the resulting goals with `wp_finish`. The
tactics for primitives that can fail split the goal into a success and a failure case, with specs
whose premise is the conjunction of both cases, such as `HL.wp_untag_cases`; `wp_apply` finds the
evaluation context itself.

In the success case, `wp_untag t` names the payload `t`, and uses the equation that decomposes the
tested term to substitute it if it is a variable. `wp_untag t with h` keeps this equation as `h`,
and also names `h` the failure, which the first form forgets. The other tactics follow the same
pattern. `wp_dec` also names the sealing key and the fact that the given key opens it.

The table lists the tactics by their Rocq names.

| Rocq | Lean |
|---|---|
| `wp_cons`, `wp_list`, `wp_term_of_list`, `wp_hash`, `wp_tag` | the same |
| `wp_eq_term h` | `wp_eq_term h` |
| `wp_list_match => [x y ->\|h]` | `wp_list_match x y`, `wp_list_match x y with h` |
| `wp_list_match` | `wp_list_match` |
| `wp_untag t`, `wp_untag_eq t h` | `wp_untag t`, `wp_untag t with h` |
| `wp_list_of_term t`, `wp_list_of_term_eq t h` | `wp_list_of_term t`, `… with h` |
| `wp_is_key_eq kt k h` | `wp_is_key kt k`, `wp_is_key kt k with h` |
| `wp_lookup t h` | `wp_lookup t with h` |
| `wp_dec t`, `wp_dec_eq t h` | `wp_dec kt t`, `wp_dec kt t with hk h` |
| `wp_adec t`, `wp_adec_eq t h` | `wp_adec t`, `wp_adec t with h` |
| `wp_sdec t`, `wp_sdec_eq t h` | `wp_sdec t`, `wp_sdec t with h` |
| `wp_verify t`, `wp_verify_eq t h` | `wp_verify t`, `wp_verify t with h` | -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode ProgramLogic

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {α : Type _} [Encode α]
local bi (IProp GF)

/-! ## Specs by cases -/

#rocq_ignore cryptis.tac_wp_cons "`wp_cons` is already in continuation form."
#rocq_ignore cryptis.tac_wp_hash "`HL.wp_hash` is already in continuation form."
#rocq_ignore cryptis.tac_wp_tag "`HL.wp_tag` is already in continuation form."
#rocq_ignore cryptis.tac_wp_enc "`HL.wp_enc` is already in continuation form."
#rocq_ignore cryptis.tac_wp_senc "`HL.wp_senc'` is already in continuation form."
#rocq_ignore cryptis.tac_wp_list "`HL.wp_listToExp` is already in continuation form."
#rocq_ignore cryptis.tac_wp_adec "The postcondition `HL.decPost` of `HL.wp_adec'` splits the cases."
#rocq_ignore cryptis.tac_wp_sdec "The postcondition `HL.decPost` of `HL.wp_sdec'` splits the cases."
#rocq_ignore cryptis.tac_wp_verify
  "The postcondition `HL.decPost` of `HL.wp_verify'` splits the cases."

/-- `wp_cons` for the last cell of a list, whose tail is the empty list `[]` rather than the
encoding of a list. -/
@[rocq_alias cryptis.tac_wp_cons1]
theorem wp_cons_nil (x : α) (Ψ : Val → IProp GF) :
    Ψ (encode [x]) ⊢ WP hl(v(&(encode x)) :: v([])) @ s; E {{ Ψ }} :=
  wp_cons x [] Ψ

/-- `wp_listMatch`, with the list of the right length as a variable `vs'`, so that the tactic
`wp_list_match` can split it into its elements. -/
@[rocq_alias cryptis.tac_wp_list_match]
theorem wp_listMatch_cases (vars : List String) (vs : List α) (k : Exp) (Ψ : Val → IProp GF) :
    (∀ vs' : List α, ⌜vars.length = vs'.length⌝ -∗ ⌜vs = vs'⌝ -∗
        WP (nsubst vars (vs'.map encode) k) @ s; E {{ Ψ }}) ∧
      (⌜vars.length ≠ vs.length⌝ -∗ Ψ hl_val(none())) ⊢
      WP (listMatch vars (encode vs) k) @ s; E {{ Ψ }} := by
  iintro H
  iapply wp_listMatch
  by_cases h : vars.length = vs.length
  · rw [ite_eq_left h]; icases H with ⟨H, -⟩; iapply H $$ %vs %h %rfl
  · rw [ite_eq_right h]; icases H with ⟨-, H⟩; iapply H $$ %h

@[rocq_alias cryptis.tac_twp_lookup]
theorem twp_getList_cases (l : List α) (n : Nat) (Ψ : Val → IProp GF) :
    (∀ x, ⌜l[n]? = some x⌝ -∗ Ψ hl_val(some(&(encode x)))) ∧ (⌜l[n]? = none⌝ -∗ Ψ hl_val(none()))
      ⊢ WP hl(&getList &(encode l) #n) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_getList
  cases h : l[n]? with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some x => icases H with ⟨H, -⟩; iapply H $$ %x %rfl

@[rocq_alias cryptis.tac_wp_lookup]
theorem wp_getList_cases (l : List α) (n : Nat) (Ψ : Val → IProp GF) :
    (∀ x, ⌜l[n]? = some x⌝ -∗ Ψ hl_val(some(&(encode x)))) ∧ (⌜l[n]? = none⌝ -∗ Ψ hl_val(none()))
      ⊢ WP hl(&getList &(encode l) #n) @ s; E {{ Ψ }} :=
  (twp_getList_cases l n Ψ).trans (wand_entails twp.to_wp)

namespace HL

theorem twp_eqTerm_cases (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    (⌜t₁ = t₂⌝ -∗ Ψ hl_val(#true)) ∧ (⌜t₁ ≠ t₂⌝ -∗ Ψ hl_val(#false)) ⊢
      WP hl(&eqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_eqTerm
  by_cases h : t₁ = t₂
  · rw [decide_eq_true h]; icases H with ⟨H, -⟩; iapply H $$ %h
  · rw [decide_eq_false h]; icases H with ⟨-, H⟩; iapply H $$ %h

@[rocq_alias cryptis.tac_wp_eq_term]
theorem wp_eqTerm_cases (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    (⌜t₁ = t₂⌝ -∗ Ψ hl_val(#true)) ∧ (⌜t₁ ≠ t₂⌝ -∗ Ψ hl_val(#false)) ⊢
      WP hl(&eqTerm &(encode t₁) &(encode t₂)) @ s; E {{ Ψ }} :=
  (twp_eqTerm_cases t₁ t₂ Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.tac_twp_untag]
theorem twp_untag_cases (c t : Term) (Ψ : Val → IProp GF) :
    (∀ t', ⌜t = Spec.tag c t'⌝ -∗ Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.untag c t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&untag &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_untag
  cases h : Spec.untag c t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some t' => icases H with ⟨H, -⟩; iapply H $$ %t' %(Spec.untag_eq_some_iff.mp h)

@[rocq_alias cryptis.tac_wp_untag]
theorem wp_untag_cases (c t : Term) (Ψ : Val → IProp GF) :
    (∀ t', ⌜t = Spec.tag c t'⌝ -∗ Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.untag c t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&untag &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_untag_cases c t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.tac_twp_open]
theorem twp_opened_cases (k t : Term) (Ψ : Val → IProp GF) :
    (∀ kt t', ⌜Spec.openKey kt = some k⌝ -∗ ⌜t = .sealed kt t'⌝ -∗
        Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.opened k t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&opened &(encode k) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_opened
  cases h : Spec.opened k t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some t' =>
    obtain ⟨kt, hk, ht⟩ := Spec.opened_eq_some_iff.mp h
    icases H with ⟨H, -⟩
    iapply H $$ %kt %t' %hk %ht

@[rocq_alias cryptis.tac_wp_open]
theorem wp_opened_cases (k t : Term) (Ψ : Val → IProp GF) :
    (∀ kt t', ⌜Spec.openKey kt = some k⌝ -∗ ⌜t = .sealed kt t'⌝ -∗
        Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.opened k t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&opened &(encode k) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_opened_cases k t Ψ).trans (wand_entails twp.to_wp)

theorem twp_dec_cases (k c t : Term) (Ψ : Val → IProp GF) :
    (∀ kt t', ⌜Spec.openKey kt = some k⌝ -∗ ⌜t = .sealed kt (Spec.tag c t')⌝ -∗
        Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.dec k c t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&dec &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_dec
  cases h : Spec.dec k c t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some t' =>
    obtain ⟨kt, hk, ht⟩ := Spec.dec_eq_some_iff.mp h
    icases H with ⟨H, -⟩
    iapply H $$ %kt %t' %hk %ht

@[rocq_alias cryptis.tac_wp_dec]
theorem wp_dec_cases (k c t : Term) (Ψ : Val → IProp GF) :
    (∀ kt t', ⌜Spec.openKey kt = some k⌝ -∗ ⌜t = .sealed kt (Spec.tag c t')⌝ -∗
        Ψ hl_val(some(&(encode t')))) ∧
      (⌜Spec.dec k c t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&dec &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_dec_cases k c t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.tac_twp_list_of_term]
theorem twp_listOfTerm_cases (t : Term) (Ψ : Val → IProp GF) :
    (∀ ts, ⌜t = Spec.ofList ts⌝ -∗ Ψ hl_val(some(&(encode ts)))) ∧
      (⌜Spec.toList t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&listOfTerm &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_listOfTerm
  cases h : Spec.toList t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some ts => icases H with ⟨H, -⟩; iapply H $$ %ts %(Spec.toList_eq_some_iff.mp h)

@[rocq_alias cryptis.tac_wp_list_of_term]
theorem wp_listOfTerm_cases (t : Term) (Ψ : Val → IProp GF) :
    (∀ ts, ⌜t = Spec.ofList ts⌝ -∗ Ψ hl_val(some(&(encode ts)))) ∧
      (⌜Spec.toList t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&listOfTerm &(encode t)) @ s; E {{ Ψ }} :=
  (twp_listOfTerm_cases t Ψ).trans (wand_entails twp.to_wp)

theorem twp_isKey_cases (t : Term) (Ψ : Val → IProp GF) :
    (∀ kt k, ⌜t = .key kt k⌝ -∗ Ψ hl_val(some(&(encode kt)))) ∧
      (⌜Spec.isKey t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&isKey &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_isKey
  cases h : Spec.isKey t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %rfl
  | some kt =>
    obtain ⟨k, hk⟩ := Spec.isKey_eq_some_iff.mp h
    icases H with ⟨H, -⟩
    iapply H $$ %kt %k %hk

@[rocq_alias cryptis.tac_wp_is_key]
theorem wp_isKey_cases (t : Term) (Ψ : Val → IProp GF) :
    (∀ kt k, ⌜t = .key kt k⌝ -∗ Ψ hl_val(some(&(encode kt)))) ∧
      (⌜Spec.isKey t = none⌝ -∗ Ψ hl_val(none())) ⊢
      WP hl(&isKey &(encode t)) @ s; E {{ Ψ }} :=
  (twp_isKey_cases t Ψ).trans (wand_entails twp.to_wp)

end HL

end Cryptis

end

/-! ## Tactics -/

namespace Cryptis.Tactics

open Lean

public meta section

/-- Take the pure steps of the goal, apply the spec `lem`, whose premise is the conjunction of a
success and a failure case, introduce each case with `succ` and `fail`, and simplify the
resulting goals. -/
def wpCases (lem : Lean.Term) (succ fail : TSyntax `tactic) : MacroM (TSyntax `tactic) :=
  `(tactic| focus
      (wp_pures
       wp_apply $lem:term
       isplit <;> [$succ; $fail]
       all_goals try wp_finish))

/-- `wpCases` for a spec whose success case binds `xs`, then an equation, then the premises
`extra`. With `h`, the equation and the failure are named `h`. Without it, the equation is
substituted if one of its sides is a variable and dropped otherwise, and the failure is dropped. -/
def wpCasesEq (lem : Lean.Term) (xs : Array Ident) (h? : Option Ident)
    (extra : Array (TSyntax `introPat) := #[]) : MacroM (TSyntax `tactic) := do
  let pats ← xs.mapM fun x => `(introPat| %$x:ident)
  match h? with
  | some h => wpCases lem (← `(tactic| iintro $pats* %$h $extra*)) (← `(tactic| iintro %$h))
  | none =>
    wpCases lem (← `(tactic| (iintro $pats* %h $extra*; first | subst h | clear h)))
      (← `(tactic| iintro -))

end

end Cryptis.Tactics

public meta section

open Lean Cryptis.Tactics

/-- `wp_cons` evaluates a list cell `v :: vs` of encoded values to the encoding of the list. -/
macro "wp_cons" : tactic =>
  `(tactic| focus
      (wp_pures
       first
         | wp_apply Cryptis.wp_cons
         | wp_apply Cryptis.wp_cons_nil
       try wp_finish))

/-- `wp_list` evaluates the list literals of encoded values in the goal. -/
macro "wp_list" : tactic => `(tactic| repeat wp_cons)

/-- `wp_term_of_list` evaluates `HL.termOfList` on the encoding of a list of terms. -/
macro "wp_term_of_list" : tactic =>
  `(tactic| focus (wp_pures; wp_apply Cryptis.HL.wp_termOfList; try wp_finish))

/-- `wp_hash` evaluates `HL.hash` on the encoding of a term. -/
macro "wp_hash" : tactic =>
  `(tactic| focus (wp_pures; wp_apply Cryptis.HL.wp_hash; try wp_finish))

/-- `wp_tag` evaluates `HL.tag` on the encodings of terms. -/
macro "wp_tag" : tactic =>
  `(tactic| focus (wp_pures; wp_apply Cryptis.HL.wp_tag; try wp_finish))

/-- `wp_eq_term h` evaluates `HL.eqTerm` on the encodings of terms `t₁` and `t₂`, and splits the
goal on `h : t₁ = t₂` and `h : t₁ ≠ t₂`. -/
macro "wp_eq_term " h:ident : tactic => do
  wpCases (← `(Cryptis.HL.wp_eqTerm_cases)) (← `(tactic| iintro %$h)) (← `(tactic| iintro %$h))

/-- `wp_lookup x with h` evaluates `getList` on the encoding of a list `l` and a natural number
`n`, and splits the goal on `h : l[n]? = some x` and `h : l[n]? = none`. -/
macro "wp_lookup " x:ident " with " h:ident : tactic => do
  wpCasesEq (← `(Cryptis.wp_getList_cases)) #[x] h

/-- `wp_untag t` evaluates `HL.untag` on the encodings of terms `c` and `u`. In the success case,
the payload is `t`, and `u` is replaced by `Spec.tag c t` if it is a variable.
`wp_untag t with h` names the equation `h : u = Spec.tag c t` instead, and the failure
`h : Spec.untag c u = none`. -/
syntax (name := wpUntag) "wp_untag " ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_untag $t $[with $h?]?) => do wpCasesEq (← `(Cryptis.HL.wp_untag_cases)) #[t] h?

/-- `wp_list_of_term ts` evaluates `HL.listOfTerm` on the encoding of a term `t`. In the success
case, the list is `ts`, and `t` is replaced by `Spec.ofList ts` if it is a variable.
`wp_list_of_term ts with h` names the equation `h : t = Spec.ofList ts` instead, and the failure
`h : Spec.toList t = none`. -/
syntax (name := wpListOfTerm) "wp_list_of_term " ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_list_of_term $ts $[with $h?]?) => do
    wpCasesEq (← `(Cryptis.HL.wp_listOfTerm_cases)) #[ts] h?

/-- `wp_is_key kt k` evaluates `HL.isKey` on the encoding of a term `t`. In the success case, `t`
is the key `Term.key kt k`, and is replaced by it if it is a variable. `wp_is_key kt k with h`
names the equation `h : t = Term.key kt k` instead, and the failure `h : Spec.isKey t = none`. -/
syntax (name := wpIsKey) "wp_is_key " ident ppSpace ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_is_key $kt $k $[with $h?]?) => do
    wpCasesEq (← `(Cryptis.HL.wp_isKey_cases)) #[kt, k] h?

/-- `wp_dec kt t` evaluates `HL.dec` on the encodings of terms `k`, `c` and `u`. In the success
case, `u` is the term `t` tagged with `c` and sealed with a key `kt` that `k` opens, and is
replaced by it if it is a variable. `wp_dec kt t with hk h` names the facts
`hk : Spec.openKey kt = some k` and `h : u = .sealed kt (Spec.tag c t)`, and the failure
`h : Spec.dec k c u = none`. -/
syntax (name := wpDec) "wp_dec " ident ppSpace ident (" with " ident ppSpace ident)? : tactic

macro_rules
  | `(tactic| wp_dec $kt $t with $hk $h) => do
    wpCasesEq (← `(Cryptis.HL.wp_dec_cases)) #[kt, t, hk] h
  | `(tactic| wp_dec $kt $t) => do
    wpCasesEq (← `(Cryptis.HL.wp_dec_cases)) #[kt, t, mkIdent (← MonadQuotation.addMacroScope `hk)]
      none

/-- `wp_adec t` evaluates `HL.adec` with a secret key `sk` on a ciphertext `u`. In the success
case, `u` is the term `t` tagged and sealed with `Spec.pkey sk`, and is replaced by it if it is a
variable. `wp_adec t with h` names this equation `h` instead, and the failure
`h : Spec.dec sk c u = none`. -/
syntax (name := wpADec) "wp_adec " ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_adec $t $[with $h?]?) => do
    wpCasesEq (← `(Cryptis.HL.wp_adec')) #[t] h? #[← `(introPat| -)]

/-- `wp_sdec t` is `wp_adec t` for `HL.sdec` and a symmetric key. -/
syntax (name := wpSDec) "wp_sdec " ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_sdec $t $[with $h?]?) => do
    wpCasesEq (← `(Cryptis.HL.wp_sdec')) #[t] h? #[← `(introPat| -)]

/-- `wp_verify t` is `wp_adec t` for `HL.verify`, with the public key of a signing key. -/
syntax (name := wpVerify) "wp_verify " ident (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_verify $t $[with $h?]?) => do
    wpCasesEq (← `(Cryptis.HL.wp_verify')) #[t] h? #[← `(introPat| -)]

/-- `wp_list_match x₁ … xₙ` evaluates `list_match [y₁, …, yₙ] := v in k`, where `v` encodes a
list `vs`. In the success case, the elements of `vs` are `x₁, …, xₙ`, `vs` is replaced by
`[x₁, …, xₙ]` if it is a variable, and the goal is `k` with `yᵢ` replaced by `xᵢ`.
`wp_list_match x₁ … xₙ with h` names the equation `h : vs = [x₁, …, xₙ]` instead, and the failure
`h : n ≠ vs.length`. With no names, `wp_list_match` leaves the success case as
`∀ x₁ … xₙ, vs = [x₁, …, xₙ] → …`. -/
syntax (name := wpListMatch) "wp_list_match" (ppSpace colGt ident)* (" with " ident)? : tactic

macro_rules
  | `(tactic| wp_list_match $xs* $[with $h?]?) => do
    let split ← `(tactic|
      (iintro %vs %hlen %hvs
       revert vs hlen hvs
       refine Cryptis.nforall_iff.mp ?_
       simp only [Cryptis.nforall, Cryptis.nsubst, List.length_cons, List.length_nil,
         List.map_cons, List.map_nil]))
    let lem ← `(Cryptis.wp_listMatch_cases)
    match xs.isEmpty, h? with
    | true, none => wpCases lem split (← `(tactic| iintro -))
    | _, some h =>
      wpCases lem (← `(tactic| ($split; intro $xs* $h:ident)))
        (← `(tactic| (iintro %$h; simp only [List.length_cons, List.length_nil] at $h:ident)))
    | false, none =>
      wpCases lem (← `(tactic| ($split; intro $xs* h; first | subst h | clear h)))
        (← `(tactic| iintro -))

end

/-! ## Examples -/

section Examples

open Cryptis Iris Iris.BI Iris.HeapLang

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

example (a b : Term) :
    ⊢ WP hl(&HL.termOfList [&(encode a), &(encode b)])
      {{ v, ⌜v = encode (Spec.ofList [a, b])⌝ }} := by
  wp_list
  wp_term_of_list
  ipureintro; rfl

example (c t : Term) :
    ⊢ WP hl(&HL.hash (&HL.tag &(encode c) &(encode t)))
      {{ v, ⌜v = encode (Term.hash (Spec.tag c t))⌝ }} := by
  wp_tag
  wp_hash
  ipureintro; rfl

example (t₁ t₂ : Term) :
    ⊢ WP hl(if &HL.eqTerm &(encode t₁) &(encode t₂) then #true else #false)
      {{ v, ⌜v = hl_val(#(decide (t₁ = t₂)))⌝ }} := by
  wp_eq_term h
  · wp_pures; ipureintro; simp [h]
  · wp_pures; ipureintro; simp [h]

example (vs : List Term) :
    ⊢ WP hl(list_match [x, y] := &(encode vs) in (y, x))
      {{ v, ⌜v ≠ hl_val(#0)⌝ }} := by
  wp_list_match a b
  · wp_pures; ipureintro; simp
  · ipureintro; simp

example (vs : List Term) :
    ⊢ WP hl(list_match [x, y] := &(encode vs) in (y, x))
      {{ v, ⌜v = hl_val(none()) → vs.length ≠ 2⌝ }} := by
  wp_list_match a b with h
  · wp_pures; ipureintro; simp
  · ipureintro; simpa [eq_comm] using h

example (vs : List Term) : ⊢ WP hl(list_match [x] := &(encode vs) in x) {{ _v, True }} := by
  wp_list_match
  · intro a h; wp_pures; ipureintro; trivial
  · ipureintro; trivial

example (c u : Term) :
    ⊢ WP hl(&HL.untag &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.untag c u) ∨ v = hl_val(none())⌝ }} := by
  wp_untag t
  · ipureintro; simp
  · ipureintro; simp

example (c u : Term) :
    ⊢ WP hl(&HL.untag &(encode c) &(encode u)) {{ v, ⌜v = encode (Spec.untag c u)⌝ }} := by
  wp_untag t with h
  · ipureintro; simp [h]
  · ipureintro; simp [h]

example (u : Term) :
    ⊢ WP hl(&HL.listOfTerm &(encode u))
      {{ v, ⌜v = encode (Spec.toList u) ∨ v = hl_val(none())⌝ }} := by
  wp_list_of_term ts
  · ipureintro; simp
  · ipureintro; simp

example (u : Term) :
    ⊢ WP hl(&HL.listOfTerm &(encode u)) {{ v, ⌜v = encode (Spec.toList u)⌝ }} := by
  wp_list_of_term ts with h
  · ipureintro; simp [h]
  · ipureintro; simp [h]

example (u : Term) :
    ⊢ WP hl(&HL.isKey &(encode u)) {{ v, ⌜v = encode (Spec.isKey u) ∨ v = hl_val(none())⌝ }} := by
  wp_is_key kt k
  · ipureintro; simp [Spec.isKey]
  · ipureintro; simp

example (u : Term) :
    ⊢ WP hl(&HL.isKey &(encode u)) {{ v, ⌜v = encode (Spec.isKey u)⌝ }} := by
  wp_is_key kt k with h
  · ipureintro; simp [h, Spec.isKey]
  · ipureintro; simp [h]

example (l : List Term) (n : Nat) :
    ⊢ WP hl(&getList &(encode l) #n) {{ v, ⌜v = encode l[n]?⌝ }} := by
  wp_lookup x with h
  · ipureintro; simp [h]
  · ipureintro; simp [h]

example (k c u : Term) :
    ⊢ WP hl(&HL.dec &(encode k) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec k c u) ∨ v = hl_val(none())⌝ }} := by
  wp_dec kt t
  · ipureintro; simp_all [Spec.dec, Spec.opened]
  · ipureintro; simp

example (k c u : Term) :
    ⊢ WP hl(&HL.dec &(encode k) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec k c u)⌝ }} := by
  wp_dec kt t with hk h
  · ipureintro; simp [h, hk, Spec.dec, Spec.opened]
  · ipureintro; simp [h]

example (sk : Key .aenc) (c u : Term) :
    ⊢ WP hl(&HL.adec &(encode sk) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec sk c u) ∨ v = hl_val(none())⌝ }} := by
  wp_adec t
  · ipureintro; simp [Spec.dec, Spec.opened]
  · ipureintro; simp

example (sk : Key .aenc) (c u : Term) :
    ⊢ WP hl(&HL.adec &(encode sk) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec sk c u)⌝ }} := by
  wp_adec t with h
  · ipureintro; simp [h, Spec.dec, Spec.opened]
  · ipureintro; simp [h]

example (k : Key .senc) (c u : Term) :
    ⊢ WP hl(&HL.sdec &(encode k) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec k c u) ∨ v = hl_val(none())⌝ }} := by
  wp_sdec t
  · ipureintro; simp [Spec.dec, Spec.opened]
  · ipureintro; simp

example (k : Key .senc) (c u : Term) :
    ⊢ WP hl(&HL.sdec &(encode k) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec k c u)⌝ }} := by
  wp_sdec t with h
  · ipureintro; simp [h, Spec.dec, Spec.opened]
  · ipureintro; simp [h]

example (sk : Key .sign) (c u : Term) :
    ⊢ WP hl(&HL.verify &(encode (Spec.pkey sk)) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec (Spec.pkey sk) c u) ∨ v = hl_val(none())⌝ }} := by
  wp_verify t
  · ipureintro; simp [Spec.dec, Spec.opened]
  · ipureintro; simp

example (sk : Key .sign) (c u : Term) :
    ⊢ WP hl(&HL.verify &(encode (Spec.pkey sk)) &(encode c) &(encode u))
      {{ v, ⌜v = encode (Spec.dec (Spec.pkey sk) c u)⌝ }} := by
  wp_verify t with h
  · ipureintro; simp [h, Spec.dec, Spec.opened]
  · ipureintro; simp [h]

end Examples
