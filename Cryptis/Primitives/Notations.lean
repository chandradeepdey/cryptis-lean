module

public import Iris.HeapLang.Notation
public import Cryptis.Lib.HeapLangLinter

/-! HeapLang notations for code that returns options: `guard: e₁ in e₂` runs `e₂` if `e₁` holds
and returns `none()` otherwise, and `bind: x := e₁ in e₂` runs `e₂` on the value `x` of an
option `e₁`, propagating `none()`. As with `let`, the body `e₂` extends as far as possible, so
`bind: x := e in a; b` binds `x` in `a; b`. -/

@[expose] public section

namespace Cryptis

open Iris.HeapLang

/-- `guard: e₁ in e₂` is `if e₁ then e₂ else none()`. -/
syntax:10 "guard: " hl_exp:10 " in " hl_exp:1 : hl_exp

/-- `bind: x := e₁ in e₂` is `match e₁ with | some(x) => e₂ | none() => none()`. -/
syntax:10 (name := bindExp) "bind: " hl_binder " := " hl_exp:10 " in " hl_exp:1 : hl_exp

macro_rules
  | `(hl(guard: $e₁ in $e₂)) => `(hl(if $e₁ then $e₂ else none()))
  | `(hl(bind: $x := $e₁ in $e₂)) => `(hl(match $e₁ with | some($x) => $e₂ | none() => none()))

end Cryptis
