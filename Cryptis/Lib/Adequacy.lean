module

public import Iris.HeapLang.PrimitiveLaws
public import Cryptis.Lib.Misc
public import Cryptis.Lib.GenAdequacy

/-! Adequacy of total weakest preconditions for HeapLang.

A HeapLang thread with a total weakest precondition reaches a value that satisfies the
postcondition (`heap_twp_reflTransGen`). If it is a pure expression, it does so by pure steps
(`heap_twp_reflTransGen_pure`). -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Language Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors}

@[rocq_alias cryptis.heap_twp_thread_exec]
theorem heap_twp_reflTransGen [HeapLangGpreS hlc GF] (e : Exp) (σ : State) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS hlc GF], ⊢ invHeapInv -∗ WP e [{ v, ⌜φ v⌝ }]) :
    ∃ (v : Val) (σ' : State), Relation.ReflTransGen ThreadStep (e, σ) ((v : Exp), σ') ∧ φ v := by
  refine twp_reflTransGen (hlc := hlc) (GF := GF) e σ φ 0 fun {_} => ?_
  imod genHeap_init (GF := GF) (H := HeapF) σ.heap with ⟨%γh, Hh, -⟩
  imod invHeap_init Loc _ (GF := GF) (H := HeapF) (E := ⊤) with ⟨%γi, >Hi⟩
  imod ProphMap.init ([] : List Observation) σ.usedProphId with ⟨%γp, Hp⟩
  let : HeapLangGS hlc GF := ⟨γh, γp, γi⟩
  imodintro
  iexists (fun σ _ κs _ => iprop% genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId),
    (fun _ => 0), (fun _ => iprop(True)), heapLangInst.stateInterp_mono
  simp only []
  ihave Hwp := (@Hwp _) $$ Hi
  iframe

/-- A thread that only runs a pure expression takes pure steps. -/
@[rocq_alias cryptis.thread_exec_pure_exec]
theorem reflTransGen_purePrimStep_of_threadStep {e e' : Exp} {σ σ' : State}
    (h : Relation.ReflTransGen ThreadStep (e, σ) (e', σ')) (he : pureExp e) : e -ᵖ->* e' := by
  suffices ∀ p, Relation.ReflTransGen ThreadStep p (e', σ') → pureExp p.1 → p.1 -ᵖ->* e' from
    this _ h he
  intro p h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | head hstep _ ih =>
    obtain ⟨efs, hstep⟩ := hstep
    exact fun he => .head (purePrimStep_of_pureExp hstep he) (ih (pureExp_of_primStep hstep he))

@[rocq_alias cryptis.heap_twp_pure_exec]
theorem heap_twp_reflTransGen_pure [HeapLangGpreS hlc GF] {e : Exp} {φ : Val → Prop}
    (he : pureExp e) (Hwp : ∀ [HeapLangGS hlc GF], ⊢ invHeapInv -∗ WP e [{ v, ⌜φ v⌝ }]) :
    ∃ v : Val, e -ᵖ->* v ∧ φ v := by
  obtain ⟨v, _, h, hφ⟩ := heap_twp_reflTransGen e default φ Hwp
  exact ⟨v, reflTransGen_purePrimStep_of_threadStep h he, hφ⟩

end Cryptis
