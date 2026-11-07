module

public import Iris.Instances.Lib.Invariants
public import Iris.BI.Lib.GenHeap
public import Cryptis.Upstream.Iris.BILemmas
public import Cryptis.Upstream.Iris.NamespaceMap
public import Cryptis.Upstream.Iris.ProofModeInstances

/-! Switches and escrows.

A switch from `P` to `Q` lets `P` be exchanged for a persistent witness `R`, such that `P` and `R`
together give `Q`. From `▷ Q` and such a switch, `escrow_intro` allocates an escrow: a persistent
right, backed by an invariant, to exchange `P` for `▷ Q` in any mask that contains its namespace.

The module also re-exports the generic BI, reservation-map and proof-mode lemmas of
`Cryptis.Upstream.Iris`. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.Std

section Switch

variable {PROP : Type _} [BI PROP] [BIUpdate PROP]
local bi PROP

/-- `switch P Q`: `P` can be exchanged for a persistent `R`, and `P` together with `R` gives `Q`. -/
@[rocq_alias cryptis.switch]
def switch (P Q : PROP) : PROP := iprop(∃ R, □ (P ∗ □ R -∗ Q) ∗ □ (P ==∗ □ R))

end Switch

section Escrow

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
local bi (IProp GF)

/-- `escrow N P Q` exchanges `P` for `▷ Q` in any mask containing `N`. -/
@[rocq_alias cryptis.escrow]
def escrow (N : Namespace) (P Q : IProp GF) : IProp GF :=
  iprop(□ ∀ E, ⌜(↑N : CoPset) ⊆ E⌝ -∗ P ={E}=∗ ▷ Q)

@[rocq_alias cryptis.escrow_persistent]
instance escrow_persistent (N : Namespace) (P Q : IProp GF) : Persistent (escrow N P Q) := by
  unfold escrow; infer_instance

@[rocq_alias cryptis.escrowI]
theorem escrow_intro (N : Namespace) (E : CoPset) (P Q : IProp GF) :
    ▷ Q -∗ switch P Q ={E}=∗ escrow N P Q := by
  unfold switch escrow
  iintro HQ ⟨%R, #Hcontra, #Hmint⟩
  imod inv_alloc N E iprop(Q ∨ □ R) $$ [HQ] with #Hinv
  · inext; ileft; iexact HQ
  imodintro
  iintro !> %E' %hsub HP
  iinv Hinv with (H | #H)
  · imod Hmint $$ HP with #HR
    imodintro
    isplitr [H]
    · inext; iright; iexact HR
    · iexact H
  · imodintro
    isplitr
    · inext; iright; iexact H
    · imodintro; inext; iapply Hcontra; isplitl [HP] <;> iassumption

@[rocq_alias cryptis.escrowE]
theorem escrow_elim {N : Namespace} {E : CoPset} (h : (↑N : CoPset) ⊆ E) (P Q : IProp GF) :
    escrow N P Q -∗ P ={E}=∗ ▷ Q := by
  unfold escrow
  iintro #He HP
  iapply He $$ %E %h HP

end Escrow

attribute [rocq_alias cryptis.dom_ne] PartialMap.dom_eq_of_dist
attribute [rocq_alias cryptis.meta_meta_token] meta_metaToken_valid'

end Cryptis
