module

public import Iris.HeapLang.Linter

/-! The HeapLang free-variable linter, extended with the binding forms of Cryptis.

Iris-Lean's `linter.heapLang.freeVars` knows the binders of core HeapLang, so it would report
the variables bound by `list_match [x, y] := e in k` and `bind: x := e₁ in e₂` as unbound. This
package turns that linter off in `lakefile.toml` and runs `linter.cryptis.heapLangFreeVars`: the
same analysis with these two binding forms, recognised by their syntax kinds
`Cryptis.listMatchSyntax` and `Cryptis.bindExp`.

The upstream candidate (Iris-Lean) is an extensible `linter.heapLang.freeVars`, to which
packages register binding forms by syntax kind; this file would then only register the two forms
above. -/

public meta section
namespace Cryptis.HeapLangLinter

open Lean Lean.Elab Lean.Elab.Command Lean.Linter
open Iris.HeapLang.Linter (extendScope matchArmBinder collectEntries)

register_option linter.cryptis.heapLangFreeVars : Bool := {
  defValue := true
  descr := "warn about unbound variables in HeapLang `hl(...)` expressions, \
    knowing Cryptis's binding forms"
}

/-- Iris-Lean's `Iris.HeapLang.Linter.analyze`, extended with `list_match` and `bind:`. -/
partial def analyze (scope : List String) (stx : Syntax) : CommandElabM Unit := do
  let underBinders (bs : Array Syntax) (body : Syntax) : CommandElabM Unit := do
    if let some scope := extendScope scope bs then analyze scope body
  if stx.isOfKind `Cryptis.listMatchSyntax then
    -- `list_match [x₁, …, xₙ] := e in k`
    analyze scope stx[5]
    let names := stx[2].getSepArgs.toList.map (·.getId.toString)
    analyze (names ++ scope) stx[7]
    return
  if stx.isOfKind `Cryptis.bindExp then
    -- `bind: x := e₁ in e₂`
    analyze scope stx[3]
    underBinders #[stx[1]] stx[5]
    return
  match stx with
  | `(hl_exp| $i:ident) =>
    let name := i.getId.toString
    unless scope.contains name do
      logLint linter.cryptis.heapLangFreeVars i m!"\
        unbound HeapLang variable `{name}`.\n\n\
        • If you meant a meta-level (Lean) definition, escape it: `&{name}`.\n\
        • Otherwise `{name}` is a free variable, and likely a typo."
  | `(hl_exp| & $_) => pure ()
  | `(hl_exp| # $_) => pure ()
  | `(hl_exp| v($_)) => pure ()
  | `(hl_val| & $_) => pure ()
  | `(hl_val| # $_) => pure ()
  | `(hl_exp| λ $bs*, $e) => underBinders (bs.map (·.raw)) e
  | `(hl_exp| rec $f $xs* := $e) => underBinders (#[f.raw] ++ xs.map (·.raw)) e
  | `(hl_exp| let $b := $e1; $e2) =>
    analyze scope e1
    underBinders #[b.raw] e2
  | `(hl_exp| match $e with | $a1 => $e1 | $a2 => $e2) =>
    analyze scope e
    underBinders (matchArmBinder a1.raw).toArray e1.raw
    underBinders (matchArmBinder a2.raw).toArray e2.raw
  | `(hl_val| λ $bs*, $e) => underBinders (bs.map (·.raw)) e
  | `(hl_val| rec $f $xs* := $e) => underBinders (#[f.raw] ++ xs.map (·.raw)) e
  | _ => for arg in stx.getArgs do analyze scope arg

/-- The HeapLang free-variable linter, knowing Cryptis's binding forms. -/
def freeVarsLinter : Linter where
  run := fun stx => do
    unless getLinterValue linter.cryptis.heapLangFreeVars (← getLinterOptions) do return
    for entry in collectEntries stx #[] do
      analyze [] entry
  name := `Cryptis.HeapLangLinter.freeVars

initialize addLinter freeVarsLinter

end Cryptis.HeapLangLinter
