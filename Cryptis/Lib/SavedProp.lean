module

public import Iris.Instances.Lib.SavedProp

/-! Saved propositions and predicates as camera elements.

Iris-Lean's `saved_prop_own` and `saved_pred_own` own a saved proposition at a ghost name. Cryptis
also stores saved propositions inside other ghost state, such as the namespace-indexed ownership
of `NOwn`, so this file names the camera elements themselves. The ghost-state classes are
Iris-Lean's `SavedPropG` and `SavedPredG`, which use the same cameras. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI COFE

attribute [rocq_alias cryptis.savedPropG] SavedPropG
attribute [rocq_alias cryptis.savedPredG] SavedPredG

#rocq_ignore cryptis.«savedPropΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.«savedPredΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.subG_savedPropG "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.subG_savedPredG "Subsumed by BundledGFunctors typeclass synthesis"

/-- The camera of saved propositions. -/
@[rocq_alias cryptis.savedPropR]
abbrev SavedPropR (GF : BundledGFunctors) : Type _ :=
  (DFracAgree.DFracAgreeRF (LaterOF IdOF)).ap (IProp GF)

/-- The camera of saved predicates over `A`. -/
@[rocq_alias cryptis.savedPredR]
abbrev SavedPredR (GF : BundledGFunctors) (A : Type _) : Type _ :=
  (DFracAgree.DFracAgreeRF (DiscreteFunOF fun _ : A => LaterOF IdOF)).ap (IProp GF)

variable {GF : BundledGFunctors} {PROP : Type _} [Sbi PROP]
local bi PROP

section SavedProp

variable {dq dq1 dq2 : DFrac} {P Q : IProp GF}

/-- The saved proposition `P` with fraction `dq`. -/
@[rocq_alias cryptis.saved_prop]
def savedProp (dq : DFrac) (P : IProp GF) : SavedPropR GF := DFracAgree.mk dq (Later.next P)

instance savedProp_coreId (P : IProp GF) : ORA.CoreId (savedProp .discard P) :=
  DFracAgree.mk_discarded_coreId

@[rocq_alias cryptis.saved_prop_valid]
theorem savedProp_valid : ✓ savedProp dq P ↔ ✓ dq := DFracAgree.mk_valid

@[rocq_alias cryptis.saved_prop_validI]
theorem savedProp_validI : ✓ savedProp dq P ⊣⊢@{PROP} ⌜✓ dq⌝ := dfrac_agree_validI _ _

@[rocq_alias cryptis.saved_prop_op_validI]
theorem savedProp_op_validI :
    ✓ (savedProp dq1 P • savedProp dq2 Q) ⊣⊢@{PROP} ⌜✓ (dq1 • dq2)⌝ ∧ ▷ (P ≡ Q) :=
  (dfrac_agree_validI_2 _ _ _ _).trans (and_congr .rfl (later_equivI P Q))

@[rocq_alias cryptis.saved_prop_op]
theorem savedProp_op (dq1 dq2 : DFrac) (P : IProp GF) :
    savedProp (dq1 • dq2) P = savedProp dq1 P • savedProp dq2 P := DFracAgree.mk_op

@[rocq_alias cryptis.saved_prop_persist]
theorem savedProp_persist (dq : DFrac) (P : IProp GF) :
    savedProp dq P ~~> savedProp .discard P := DFracAgree.persist

@[rocq_alias cryptis.saved_prop_update_2]
theorem savedProp_update₂ {P1 P2 : IProp GF} (P' : IProp GF) (h : dq1 • dq2 = .own 1) :
    savedProp dq1 P1 • savedProp dq2 P2 ~~> savedProp dq1 P' • savedProp dq2 P' :=
  DFracAgree.update₂ h

end SavedProp

section SavedPred

variable {A : Type _} {dq dq1 dq2 : DFrac} {φ ψ : A → IProp GF}

/-- The saved predicate `φ` with fraction `dq`. -/
@[rocq_alias cryptis.saved_pred]
def savedPred (dq : DFrac) (φ : A → IProp GF) : SavedPredR GF A :=
  DFracAgree.mk dq fun x => Later.next (φ x)

instance savedPred_coreId (φ : A → IProp GF) : ORA.CoreId (savedPred .discard φ) :=
  DFracAgree.mk_discarded_coreId

@[rocq_alias cryptis.saved_pred_valid]
theorem savedPred_valid : ✓ savedPred dq φ ↔ ✓ dq := DFracAgree.mk_valid

@[rocq_alias cryptis.saved_pred_validI]
theorem savedPred_validI : ✓ savedPred dq φ ⊣⊢@{PROP} ⌜✓ dq⌝ := dfrac_agree_validI _ _

@[rocq_alias cryptis.saved_pred_op_validI]
theorem savedPred_op_validI [BIAffine PROP] :
    ✓ (savedPred dq1 φ • savedPred dq2 ψ) ⊣⊢@{PROP} ⌜✓ (dq1 • dq2)⌝ ∧ □ (∀ x, ▷ (φ x ≡ ψ x)) :=
  (dfrac_agree_validI_2 _ _ _ _).trans <| and_congr .rfl <|
    (discreteFun_equivI _ _).trans <| (forall_congr fun _ => later_equivI _ _).trans
      intuitionistic_intuitionistically_alias.symm

@[rocq_alias cryptis.saved_pred_op]
theorem savedPred_op (dq1 dq2 : DFrac) (φ : A → IProp GF) :
    savedPred (dq1 • dq2) φ = savedPred dq1 φ • savedPred dq2 φ := DFracAgree.mk_op

@[rocq_alias cryptis.saved_pred_persist]
theorem savedPred_persist (dq : DFrac) (φ : A → IProp GF) :
    savedPred dq φ ~~> savedPred .discard φ := DFracAgree.persist

@[rocq_alias cryptis.saved_pred_update_2]
theorem savedPred_update₂ {φ1 φ2 : A → IProp GF} (φ' : A → IProp GF) (h : dq1 • dq2 = .own 1) :
    savedPred dq1 φ1 • savedPred dq2 φ2 ~~> savedPred dq1 φ' • savedPred dq2 φ' :=
  DFracAgree.update₂ h

end SavedPred

end Cryptis
