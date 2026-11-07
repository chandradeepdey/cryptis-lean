module

public import Iris.HeapLang.ProofMode

/-! Upstream candidate (Iris-Lean): substitution under `assert`, for the `wp_expr_simp` lemmas of
`Iris/HeapLang/ProofMode.lean`, so that the WP tactics evaluate programs that assert a condition
on a bound variable. -/

@[expose] public section

namespace Iris.ProofMode

open Iris.HeapLang

@[wp_expr_simp]
theorem subst_assert {x : String} {v : Val} {e : Exp} :
    Exp.subst (.named x) v (Exp.assert e) = Exp.assert (e.subst (.named x) v) :=
  Exp.assert_subst e

end Iris.ProofMode
