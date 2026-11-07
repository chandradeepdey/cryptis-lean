module

public import Cryptis.Primitives.Attacker

/-! Adequacy of Cryptis: if the program `f` satisfies a pure postcondition `φ` on every network
channel `c`, given the Cryptis invariant and the tokens of the sealing and hash predicates, then
running `f` against the attacker with `HL.runNetwork f` is safe, and its results satisfy `φ`. -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic

variable {GF : BundledGFunctors}

@[rocq_alias cryptis.cryptis_adequacy]
theorem cryptis_adequacy [HeapLangGpreS .hasLC GF] [CryptisGpreS GF] (f : Val) (σ : State)
    (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF] [CryptisGS GF] (c : Val),
      ⊢ cryptisCtx (GF := GF) -∗ channel c -∗
        sealPredToken .aenc ⊤ ∗ sealPredToken .sign ⊤ ∗ sealPredToken .senc ⊤ ∗
          hashPredToken ⊤ -∗
        WP hl(&f &c) {{ v, ⌜φ v⌝ }}) :
    adequate .NotStuck hl(&HL.runNetwork &f) σ (fun v _ => φ v) := by
  refine heap_adequacy (GF := GF) _ σ φ fun {_} => ?_
  iintro -
  imod cryptisGS_alloc (GF := GF) ⊤ with ⟨%_, #Hctx, Htok⟩
  iapply HL.wp_runNetwork $$ [Htok] Hctx
  iintro %c - #Hc
  iapply Hwp $$ Hctx Hc Htok

end Cryptis
