module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.Instances.Lib.FUpd
public import Mathlib.Logic.Relation

/-! Adequacy of total weakest preconditions for a single thread.

A total weakest precondition of `e` not only rules out divergence: it ensures that `e` alone
reaches a value satisfying the postcondition, ignoring the threads that it forks
(`twp_reflTransGen`). -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.ProgramLogic OFE Language Language.Notation

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]

/-- A step of a thread that makes no observation, discarding the threads it forks. -/
@[rocq_alias cryptis.thread_step]
def ThreadStep (p₁ p₂ : Expr × State) : Prop := ∃ efs, p₁ -<[]>-> (p₂.1, p₂.2, efs)

section RunsUntil

variable {hlc : HasLC} {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]
local bi (IProp GF)

/-- From any state, the thread `e` reaches a value that satisfies `Φ`. -/
@[rocq_alias cryptis.runs_until]
def runsUntil (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF := iprop%
  ∀ σ ns obs nt, stateInterp σ ns obs nt ={E}=∗ ∃ (v : Val), ∃ σ' ns' obs' nt',
    ⌜Relation.ReflTransGen ThreadStep (e, σ) ((v : Expr), σ')⌝ ∗ stateInterp σ' ns' obs' nt' ∗ Φ v

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

@[rocq_alias cryptis.runs_until_proper]
instance runsUntil_ne :
    NonExpansive fun x : twp.Internal.Args Expr Val GF => runsUntil x.1 x.2.1 x.2.2 where
  ne _ := fun ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ => by
    obtain rfl := show E₁ = E₂ from hE
    obtain rfl := show e₁ = e₂ from he
    dsimp only [runsUntil]
    refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
      wand_ne.ne .rfl <| BIFUpdate.ne.ne <| exists_ne fun v => exists_ne fun _ =>
        exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
          sep_ne.ne .rfl <| sep_ne.ne .rfl (hΦ v)

@[rocq_alias cryptis.twp_runs_until]
theorem runsUntil_of_twp (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    WP e @ Stuckness.NotStuck ; E [{ Φ }] ⊢ runsUntil E e Φ := by
  iintro He
  iapply twp.induction Stuckness.NotStuck (fun E e Φ => runsUntil E e Φ) $$ [] %e %E %Φ He
  iintro !> %e %E %Φ IH
  unfold runsUntil twp.pre
  iintro %σ %ns %obs %nt Hσ
  cases hv : toVal e <;> dsimp only []
  · imod IH $$ Hσ with ⟨%⟨e', σ', efs, hstep⟩, IH⟩
    imod IH $$ %([] : List Obs) %e' %σ' %efs %hstep with ⟨-, Hσ, ⟨IH, -⟩, -⟩
    imod IH $$ Hσ with ⟨%v, %σ'', %ns', %obs', %nt', %hexec, Hσ, HΦ⟩
    iexists v, σ'', ns', obs', nt'
    iframe
    ipureintro
    exact .head ⟨efs, hstep⟩ hexec
  · imod IH
    iexists _, σ, ns, obs, nt
    iframe
    ipureintro
    rw [coe_of_toVal_eq_some hv]

end RunsUntil

/-- If a total weakest precondition holds for `e` under some state interpretation, then `e` reaches
a value that satisfies the postcondition. -/
@[rocq_alias cryptis.twp_rtc]
theorem twp_reflTransGen {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF]
    (e : Expr) (σ : State) (φ : Val → Prop) (n : Nat)
    (Hwp : ∀ [InvGS_gen hlc GF],
      ⊢ |={⊤}=>
        ∃ (stateI : State → Nat → List Obs → Nat → IProp GF)
          (numLatersPerStep : Nat → Nat)
          (forkPost : Val → IProp GF)
          (mono : ∀ σ ns obs nt,
            stateI σ ns obs nt ⊢ |={∅}=> stateI σ (ns + 1) obs nt),
        let _ : IrisGS_gen hlc Expr GF :=
          .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
        iprop% stateI σ n [] 0 ∗ WP e @ Stuckness.NotStuck ; ⊤ [{ v, ⌜φ v⌝ }]) :
    ∃ (v : Val) (σ' : State), Relation.ReflTransGen ThreadStep (e, σ) ((v : Expr), σ') ∧ φ v := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine fupd_soundness hlc 0 (E1 := ⊤) (E2 := ⊤) fun _ => ?_
  iintro -
  imod Hwp with ⟨%stateI, %numLatersPerStep, %forkPost, %mono, Hσ, Htwp⟩
  let : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
  ihave Hrun := runsUntil_of_twp ⊤ e _ $$ Htwp
  unfold runsUntil
  imod Hrun $$ %σ %n %([] : List Obs) %0 Hσ with ⟨%v, %σ', %_, %_, %_, %hexec, -, %hφ⟩
  ipureintro
  exact ⟨v, σ', hexec, hφ⟩

end Cryptis
