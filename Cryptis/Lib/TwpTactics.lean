module

public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.TotalLifting

/-! Proof-mode tactics for total weakest preconditions of HeapLang.

- `twp_pure`, `twp_pures`, `twp_rec`, `twp_bind`, `twp_apply` and `twp_smart_apply` work like the
  WP tactics of `Iris.HeapLang.ProofMode`, on goals `WP e [{ Φ }]`.
- `twp_alloc` specifies allocation, and `triple_of_twp` turns a specification in continuation form
  into a Hoare triple.
- The opt-in simp set `Cryptis.WpLit`: after `open scoped Cryptis.WpLit`, the WP tactics also
  decide equalities and comparisons of literals. -/

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang Iris.BI

@[expose] public section

theorem tac_twp_value [ι : IrisGS_gen hlc Exp GF] {Δ : IProp GF} {s : Stuckness} {E : CoPset}
    {v : Val} {Φ : Val → IProp GF} (H : Δ ⊢ |={E}=> Φ v) :
    Δ ⊢ WP (v : Exp) @ s ; E [{ Φ }] :=
  H.trans (twp.value_fupd ⟨rfl⟩).2

theorem tac_twp_value_nofupd [ι : IrisGS_gen hlc Exp GF] {Δ : IProp GF} {s : Stuckness}
    {E : CoPset} {v : Val} {Φ : Val → IProp GF} (H : Δ ⊢ Φ v) :
    Δ ⊢ WP (v : Exp) @ s ; E [{ Φ }] :=
  tac_twp_value (H.trans fupd_intro)

theorem tac_twp_expr_simp [ι : IrisGS_gen hlc Exp GF] {Δ : IProp GF} {s : Stuckness}
    {E : CoPset} {e e' : Exp} {Φ : Val → IProp GF}
    (h : Δ ⊢ WP e' @ s ; E [{ Φ }]) (heq : e = e') : Δ ⊢ WP e @ s ; E [{ Φ }] :=
  heq ▸ h

theorem tac_twp_bind [ι : IrisGS_gen hlc Exp GF] {Δ : IProp GF} {s : Stuckness} {E : CoPset}
    {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
    (H : Δ ⊢ WP e' @ s ; E
      [{ v, WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ s ; E [{ Φ }] }]) :
    Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E [{ Φ }] :=
  H.trans (twp.bind (ProgramLogic.fill K))

theorem tac_twp_pure [ι : IrisGS_gen hlc Exp GF] {Δ : IProp GF} {s : Stuckness} {E : CoPset}
    {K : List ECtxItem} {e₁ e₂ : Exp} {φ : Prop} {n : Nat} {Φ : Val → IProp GF}
    (hexec : ProgramLogic.Language.PureExec φ n e₁ e₂) (hφ : φ)
    (H : Δ ⊢ WP (ProgramLogic.fill K e₂) @ s ; E [{ Φ }]) :
    Δ ⊢ WP (ProgramLogic.fill K e₁) @ s ; E [{ Φ }] :=
  H.trans (ProgramLogic.twp.pure_step (ProgramLogic.EctxLanguage.pureExec_fill φ n hexec) hφ)

end

public meta section

/-- The parts of a goal `Δ ⊢ WP e @ s; E [{ Φ }]`. -/
structure TwpGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  {hlc : Q(HasLC)}
  ι : Q(IrisGS_gen $hlc Exp $GF)
  s : Q(Stuckness)
  E : Q(CoPset)
  e : Q(Exp)
  Φ : Q(Val → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

def ProofModeM.runTacticTwp {α} (tacName : Name) (k : MVarId → TwpGoal → ProofModeM α) :
    TacticM α := do
  ProofModeM.runTactic tacName fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwIPMError "The goal {goal} must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwIPMError "The goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwIPMError "Expected the BI implementation of `IProp` to be `UPred.instBIUPred`"
    let ~q(TotalWp.totalWp (A := Stuckness) (Expr := Exp)
        (self := twp.instTotalWp (ι := $ι)) $s $E $e $Φ) := goal
      | throwIPMError "The goal {goal} must be a total WP"
    k mvar {hyps, ι, s, E, e, Φ, hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩}

/-- Strip `WP v [{ Φ }]` to `Φ v`, under a fupd unless `Φ v` can absorb one. -/
def iTwpValueHead {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (ι : Q(IrisGS_gen $hlc Exp $GF)) (s : Q(Stuckness)) (E : Q(CoPset)) (e : Q(Exp))
    (Φ : Q(Val → $prop))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(TotalWp $prop Exp Val Stuckness) := q(twp.instTotalWp))
    (_hκ : $κ =Q twp.instTotalWp := ⟨⟩) :
    ProofModeM (Option Q($ehyps ⊢ TotalWp.totalWp $s $E $e $Φ)) := do
  let ~q(ProgramLogic.ToVal.ofVal $v) := e | return none
  have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
  have : $goal =Q $Φ $v := ⟨⟩
  let c : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let A' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
  let Q' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
  if let .some _ ← ProofModeM.trySynthInstanceQ
      q(ElimModal $c false .out $p' iprop(|={$E}=> $goal) $A' $goal $Q') then
    if let some _ ← try? <| iSolveSidecondition c then
      let pf ← addBIGoal hyps q($goal)
      return some q(tac_twp_value_nofupd (s := $s) (E := $E) $pf)
  let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
  return some q(tac_twp_value (s := $s) $pf)

/-- Simplify the expression of the goal, and strip the total WP if it is a value. -/
def iTwpFinish {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (ι : Q(IrisGS_gen $hlc Exp $GF)) (s : Q(Stuckness)) (E : Q(CoPset)) (e : Q(Exp))
    (Φ : Q(Val → $prop))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(TotalWp $prop Exp Val Stuckness) := q(twp.instTotalWp))
    (_hκ : $κ =Q twp.instTotalWp := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ TotalWp.totalWp $s $E $e $Φ) := do
  let ⟨e', pfeq⟩ ← iWpExprSimp e
  let nextPf ← (← iTwpValueHead hyps ι s E e' Φ).getDM
    (addBIGoal hyps q(TotalWp.totalWp $s $E $e' $Φ))
  return q(tac_twp_expr_simp $nextPf $pfeq)

/-- Bind the evaluation context `K` of `e = K[e']`, and continue with the goal for `e'`. -/
def iTwpBindCore {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} (ehyps : Q($prop)) (ι : Q(IrisGS_gen $hlc Exp $GF))
    (s : Q(Stuckness)) (E : Q(CoPset))
    (e : Q(Exp)) (Φ : Q(Val → $prop)) (K : Q(List ECtxItem)) (e' : Q(Exp))
    (k : (A : Q($prop)) → ProofModeM Q($ehyps ⊢ $A))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(TotalWp $prop Exp Val Stuckness) := q(twp.instTotalWp))
    (_hκ : $κ =Q twp.instTotalWp := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ TotalWp.totalWp $s $E (ProgramLogic.fill $K $e') $Φ) := do
  match K with
  | ~q([]) => k q(TotalWp.totalWp $s $E $e $Φ)
  | _ =>
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <| q(TotalWp.totalWp $s $E $(← HeapLang.fill K q(.ofVal $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => TotalWp.totalWp $s $E (ProgramLogic.fill $K (v : Exp)) $Φ) :=
      ⟨⟩
    let pf ← k q(TotalWp.totalWp $s $E $e' $Φ')
    return q(tac_twp_bind $pf)

/-- Take one pure step of a subexpression accepted by `findPureExec`. -/
def iTwpPure {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)} {prop : Q(Type u)}
    {bi : Q(BI $prop)} (ehyps : Q($prop)) (ι : Q(IrisGS_gen $hlc Exp $GF)) (s : Q(Stuckness))
    (E : Q(CoPset)) (e : Q(Exp)) (Φ : Q(Val → $prop)) (failOnUnsolved : Bool)
    (findPureExec : (e₁ : Q(Exp)) →
      ProofModeM ((φ : Q(Prop)) × (n : Q(Nat)) × (e₂ : Q(Exp)) ×
        Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂)))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(TotalWp $prop Exp Val Stuckness) := q(twp.instTotalWp))
    (_hκ : $κ =Q twp.instTotalWp := ⟨⟩) :
    ProofModeM ((e' : Q(Exp)) ×
      Q(($ehyps ⊢ TotalWp.totalWp $s $E $e' $Φ) → $ehyps ⊢ TotalWp.totalWp $s $E $e $Φ)) := do
  let some {result := ⟨φ, n, e₂, inst⟩, K, e' := e₁, ..} ←
    findECtx (α := ((_ : Q(Prop)) × (_ : Q(Nat)) × (_ : Q(Exp)) × Lean.Expr)) e
      fun _ => findPureExec
    | throwIPMError "Cannot find expression to evaluate"
  have inst : Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) := inst
  let ⟨inner, .up _⟩ ← HeapLang.fillQ K e₂
  let hφ ← iSolveSidecondition φ (failOnUnsolved := failOnUnsolved)
  return ⟨inner, q(fun nextPf => tac_twp_pure $inst $hφ nextPf)⟩

/-- Strip the total WP of a value. -/
elab "twp_value_head" : tactic =>
  ProofModeM.runTacticTwp `twp_value_head fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let some pf ← iTwpValueHead hyps ι s E e Φ | throwIPMError s!"{e} is not a value"
    mvar.assign pf

/-- `twp_bind e` focuses the total WP on the subexpression `e`. -/
elab "twp_bind" colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticTwp `twp_bind fun mvar {ehyps, hyps, s, ι, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let some {K, e', ..} ← findECtx e fun _ e => do guard <| ← isDefEq e focus
      | throwIPMError s!"Cannot unify {← ppExpr focus} with any possible evaluation context"
    mvar.assign <| ← iTwpBindCore ehyps ι s E e Φ K e' (addBIGoal hyps)

/-- `twp_pure e` takes a pure step of the subexpression `e`. -/
elab "twp_pure" failOnUnsolved:("+!failOnUnsolved")? colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticTwp `twp_pure fun mvar {bi, ehyps, hyps, ι, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let ⟨e', pf⟩ ← iTwpPure (bi := bi) ehyps ι s E e Φ failOnUnsolved.isSome fun e₁ => do
      guard <| ← isDefEq e₁ focus
      findAnyPureExec e₁
    mvar.assign q($pf $(← iTwpFinish hyps ι s E e' Φ))

macro "twp_pure" : tactic => `(tactic| twp_pure _)
macro "twp_pure" "+!failOnUnsolved" : tactic => `(tactic| twp_pure +!failOnUnsolved _)

/-- Reduce all pure redexes at the head of the total WP, then simplify the expression and
strip the total WP if it has become a value. -/
macro "twp_pures" : tactic =>
  `(tactic| first
    | (twp_pure +!failOnUnsolved; repeat twp_pure +!failOnUnsolved)
    | (twp_value_head))

/-- Beta-reduce the innermost application, unfolding a head hidden behind a definition. -/
elab "twp_rec" : tactic =>
  ProofModeM.runTacticTwp `twp_rec fun mvar {bi, ehyps, hyps, ι, s, E, e, Φ, ..} => do
    let ⟨e', pf⟩ ← iTwpPure (bi := bi) ehyps ι s E e Φ (failOnUnsolved := false) fun e₁ => do
      let ~q(Exp.app (Exp.ofVal $f) (Exp.ofVal $a)) := e₁ | failure
      let f' : Q(Val) ← whnf f
      let ~q(Val.rec_ $fb $xb $body) := f' | failure
      have : $f' =Q $f := ⟨⟩
      let e₂ := q(Exp.subst $xb $a (Exp.subst $fb $f $body))
      return ⟨_, _, e₂, q(instPureExecBeta)⟩
    mvar.assign q($pf $(← iTwpFinish hyps ι s E e' Φ))

macro "twp_lam" : tactic => `(tactic| twp_rec)
macro "twp_if" : tactic => `(tactic| twp_pure (if _ then _ else _))

/-- Apply a total-WP lemma under an evaluation context, taking pure steps first if `smart`. -/
partial def iTwpApplyCore {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (ι : Q(IrisGS_gen $hlc Exp $GF)) (s : Q(Stuckness)) (E : Q(CoPset))
    (e : Q(Exp)) (Φ : Q(Val → $prop)) (pmt : PMTerm) (smart : Bool)
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(TotalWp $prop Exp Val Stuckness) := q(twp.instTotalWp))
    (_hκ : $κ =Q twp.instTotalWp := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ TotalWp.totalWp $s $E $e $Φ) := do
  let ⟨_, hypsP, p, A, posePf⟩ ← iHave hyps q(TotalWp.totalWp $s $E $e $Φ) pmt true
  let lemIVar ← mkFreshIVarId (isTrue p)
  let ⟨_, hyps0, addPf⟩ := Hyps.add bi .anonymous lemIVar p A hypsP
  let failed ← addMessageContext m!"cannot apply {A}"
  let rec go {ehypsC : Q($prop)} (hypsC : Hyps bi ehypsC) (eC : Q(Exp))
      (prefixPf : Q(($ehypsC ⊢ TotalWp.totalWp $s $E $eC $Φ) →
        $ehyps ⊢ TotalWp.totalWp $s $E $e $Φ)) :
      ProofModeM Q($ehyps ⊢ TotalWp.totalWp $s $E $e $Φ) := do
    let ⟨ehypsR, hypsR, _, A', p', _, remPf⟩ := Hyps.remove (rp := true) hypsC lemIVar
    let applied ←
      findECtx (α := Q($ehypsR ∗ □?$p' $A' ⊢ TotalWp.totalWp $s $E $eC $Φ)) eC fun K e' =>
        iTwpBindCore _ ι s E eC Φ K e' (iApply hypsR p' A' ·)
    if let some {result := pf, ..} := applied then
      return q($prefixPf <| $(remPf).mp.trans $pf)
    unless smart do throwIPMError failed
    let ⟨eN, purePf⟩ ←
      try iTwpPure (bi := bi) ehypsC ι s E eC Φ (failOnUnsolved := true) findAnyPureExec
      catch err =>
        if err.isInterrupt || err.isMaxHeartbeat then throw err
        throwIPMError failed
    let ⟨eN', pfeq⟩ ← iWpExprSimp eN
    go hypsC eN' q(fun pf => $prefixPf ($purePf (tac_twp_expr_simp pf $pfeq)))
  go hyps0 e q(fun pf => $posePf ($(addPf).mp.trans pf))

def twpApplyRaw (tacName : Name) (smart : Bool) (pmt : TSyntax `pmTerm) : TacticM Unit := do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTacticTwp tacName fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    mvar.assign (← iTwpApplyCore hyps ι s E e Φ pmt smart)

elab "twp_apply_raw" colGt pmt:pmTerm : tactic => twpApplyRaw `twp_apply false pmt
elab "twp_smart_apply_raw" colGt pmt:pmTerm : tactic => twpApplyRaw `twp_smart_apply true pmt

/-- `twp_apply lem` is `wp_apply lem` for total WPs. -/
syntax (name := twpApply) "twp_apply " colGt pmTerm (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| twp_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then `(tactic| focusLastIrisGoal (iintro $pats*))
      else `(tactic| skip)
    `(tactic| focus ((twp_apply_raw $pmt); $t:tactic))

/-- `twp_smart_apply lem` is `wp_smart_apply lem` for total WPs. -/
syntax (name := twpSmartApply) "twp_smart_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| twp_smart_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then `(tactic| focusLastIrisGoal (iintro $pats*))
      else `(tactic| skip)
    `(tactic| focus ((twp_smart_apply_raw $pmt); $t:tactic))

end

end Iris.ProofMode

namespace Iris.HeapLang

open Iris.BI

@[expose] public section

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] {s : Stuckness} {E : CoPset}
local bi (IProp GF)

/-- `wp_alloc` for total WPs. -/
theorem twp_alloc (v : Val) :
    [{ True }] hl(ref(&v)) @ s; E [{ l, RET hl_val(#l); l ↦ some v ∗ metaToken l ⊤ }] := by
  iintro %Φ - HΦ
  iapply twp_allocN_seq (by omega)
  · itrivial
  iintro %l H
  iapply HΦ
  rw [Int.toNat_one, List.range_one, BigSepL.bigSepL_singleton.to_eq, show l + 0 = l from loc_add_zero l]
  iexact H

/-- A specification in continuation form, as a Hoare triple. -/
theorem triple_of_twp {e : Exp} {v : Val}
    (h : ∀ Ψ : Val → IProp GF, Ψ v ⊢ WP e @ s; E [{ Ψ }]) :
    [{ True }] e @ s; E [{ RET v; True }] := by
  iintro %Φ - HΦ
  iapply h
  iapply HΦ $$ [//]

end

end Iris.HeapLang

/-! ### Literal evaluation -/

-- Negations of boolean literals, which `~ #true` produces.
attribute [wp_expr_simp] Bool.not_true Bool.not_false

namespace Cryptis.WpLit

@[expose] public section

/-- `Int.reduceEq`, for the simp set of the WP tactics. -/
simproc_decl reduceIntEq ((_ : Int) = _) := Int.reduceEq
/-- `Int.reduceLT`, for the simp set of the WP tactics. -/
simproc_decl reduceIntLT ((_ : Int) < _) := Int.reduceLT
/-- `Int.reduceLE`, for the simp set of the WP tactics. -/
simproc_decl reduceIntLE ((_ : Int) ≤ _) := Int.reduceLE

attribute [scoped wp_expr_simp] Bool.beq_eq_decide_eq Iris.HeapLang.Val.lit.injEq
  Iris.HeapLang.BaseLit.int.injEq Iris.HeapLang.BaseLit.bool.injEq Iris.HeapLang.BaseLit.loc.injEq
  _root_.decide_true _root_.decide_false reduceIntEq reduceIntLT reduceIntLE

end

end Cryptis.WpLit
