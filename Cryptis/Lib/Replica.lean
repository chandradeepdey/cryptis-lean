module

public import Cryptis.Logic
public import Iris.Instances.Lib.GhostVar

/-! Replicated state between a client `kI` and a server `kR`.

`replica kI kR N s a` is half of a ghost variable holding `a`, stored in the meta data of the
client at the namespace `N.@"client".@kR.@"replica".@s`. The client keeps a main replica, which it
updates, and a copy, which the server keeps in sync. `neverConnected kI kR N` is a token of the
server that is spent on its first connection with the client. Until then, the server's copy is the
initial value `a₀`. The ghost state of a replica is Iris-Lean's `GhostVarG`. -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.Std Iris.HeapLang Iris.ProofMode DFracAgree

attribute [rocq_alias cryptis.replicaG] GhostVarG

#rocq_ignore cryptis.«replicaΣ» "Subsumed by BundledGFunctors typeclass synthesis"

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
variable {A : Type} [GhostVarG GF A]
variable {kI kR : Term} {N : Namespace} {s : String} {a a₀ a₁ a₂ a' : A} {E : CoPset}
local bi (IProp GF)

/-- Half of the replica `s` of `a`, held by the client `kI` for the server `kR`. -/
@[rocq_alias cryptis.replica]
def replica (kI kR : Term) (N : Namespace) (s : String) (a : A) : IProp GF :=
  termOwn (F := GhostVarF A) kI ((((N.@"client").@kR).@"replica").@s) (Frac.mk (1 : Qp).half ⟨a⟩)

@[rocq_alias cryptis.replica_alloc]
theorem replica_alloc (a : A) (h : ↑((((N.@"client").@kR).@"replica").@s) ⊆ E) :
    termToken (GF := GF) kI E ==∗ replica kI kR N s a ∗ replica kI kR N s a ∗
      termToken kI (E \ ↑((((N.@"client").@kR).@"replica").@s)) := by
  unfold replica
  iintro Htok
  have hv : ✓ (Frac.mk (1 : Qp).half (⟨a⟩ : DiscreteO A) •
      Frac.mk (1 : Qp).half (⟨a⟩ : DiscreteO A)) :=
    Frac.op_valid.mpr ⟨by simp, rfl⟩
  imod termOwn_alloc (F := GhostVarF A) _ h hv $$ Htok with ⟨Ho, Htok⟩
  icases termOwn_op.mp $$ Ho with ⟨H1, H2⟩
  imodintro
  iframe

@[rocq_alias cryptis.replica_agree]
theorem replica_agree : replica (GF := GF) kI kR N s a₁ -∗ replica kI kR N s a₂ -∗ ⌜a₁ = a₂⌝ := by
  unfold replica
  iintro H1 H2
  icases termOwn_valid_2 $$ H1 H2 with %h
  exact pure_intro (DiscreteO.mk.inj (Frac.op_valid.mp h).2)

@[rocq_alias cryptis.replica_update]
theorem replica_update (a : A) :
    replica (GF := GF) kI kR N s a₁ -∗ replica kI kR N s a₂ ==∗
      replica kI kR N s a ∗ replica kI kR N s a := by
  unfold replica
  iintro H1 H2
  imod termOwn_update_2 (Frac.update₂ (Qp.half_add_half 1) (a' := ⟨a⟩)) $$ H1 H2 with H
  icases termOwn_op.mp $$ H with ⟨H1, H2⟩
  imodintro
  iframe

/-- The client `kI` has never connected to the server `kR`. -/
@[rocq_alias cryptis.never_connected]
abbrev neverConnected (kI kR : Term) (N : Namespace) : IProp GF :=
  termToken kR ↑((N.@"server").@kI)

@[rocq_alias cryptis.first_connection]
theorem first_connection :
    neverConnected (GF := GF) kI kR N ==∗ □ ¬ neverConnected kI kR N := by
  iintro Htok
  imod termMeta_set () LawfulSet.subset_refl $$ Htok with #Hm
  iintro !> !> Htok
  iapply termMeta_token LawfulSet.subset_refl $$ Htok Hm

/-- The main replica of the client. -/
@[rocq_alias cryptis.rep_main]
abbrev repMain (kI kR : Term) (N : Namespace) (a : A) : IProp GF :=
  replica kI kR N "main" a

/-- The copy of the replica, whose other half the server keeps. -/
@[rocq_alias cryptis.rep_copy']
abbrev repCopy' (kI kR : Term) (N : Namespace) (a : A) : IProp GF :=
  replica kI kR N "copy" a

/-- The client's view of the replica `a` with initial value `a₀`, when the server is in sync. -/
@[rocq_alias cryptis.rep_sync]
def repSync (kI kR : Term) (N : Namespace) (a₀ a : A) : IProp GF :=
  iprop(repMain kI kR N a ∗ repCopy' kI kR N a ∗
    (⌜a = a₀⌝ ∗ repCopy' kI kR N a₀ ∨ □ ¬ neverConnected kI kR N))

/-- The client's view of the replica, after it updated its main replica from `a` to `a'`. -/
@[rocq_alias cryptis.rep_update]
def repUpdate (kI kR : Term) (N : Namespace) (a₀ a a' : A) : IProp GF :=
  iprop(repMain kI kR N a' ∗ repCopy' kI kR N a ∗
    (⌜a = a₀⌝ ∗ repCopy' kI kR N a₀ ∨ □ ¬ neverConnected kI kR N))

/-- The server's view of the replica `a` with initial value `a₀`. -/
@[rocq_alias cryptis.rep_copy]
def repCopy (kI kR : Term) (N : Namespace) (a₀ a : A) : IProp GF :=
  iprop(⌜a = a₀⌝ ∗ neverConnected kI kR N ∨
    repCopy' kI kR N a ∗ □ ¬ neverConnected kI kR N)

@[rocq_alias cryptis.rep_main_sync]
theorem repMain_sync :
    repMain (GF := GF) kI kR N a -∗ repSync kI kR N a₀ a' -∗ ⌜a = a'⌝ := by
  unfold repSync
  iintro H1 ⟨H2, -⟩
  iapply replica_agree $$ H1 H2

@[rocq_alias cryptis.rep_main_alloc]
theorem repMain_alloc (a₀ : A) (h : ↑(((N.@"client").@kR).@"replica") ⊆ E) :
    termToken (GF := GF) kI E ==∗ repMain kI kR N a₀ ∗ repSync kI kR N a₀ a₀ ∗
      termToken kI (E \ ↑(((N.@"client").@kR).@"replica")) := by
  have hm := nclose_subseteq' "main" h
  have hc := nclose_subset_diff (nclose_subseteq' "copy" h)
    (ndot_ne_disjoint (x := "copy") (y := "main") _ (by decide))
  iintro Htok
  imod replica_alloc a₀ hm $$ Htok with ⟨Hm1, Hm2, Htok⟩
  imod replica_alloc a₀ hc $$ Htok with ⟨Hc1, Hc2, Htok⟩
  imodintro
  unfold repSync
  isplitl [Hm1]
  · iexact Hm1
  isplitl [Hm2 Hc1 Hc2]
  · isplitl [Hm2]
    · iexact Hm2
    isplitl [Hc1]
    · iexact Hc1
    ileft
    isplitr
    · ipureintro; rfl
    · iexact Hc2
  · iapply termToken_drop ?_ $$ Htok
    intro p hp
    simp only [LawfulSet.mem_diff] at hp ⊢
    exact ⟨⟨hp.1, fun hp' => hp.2 (nclose_subseteq _ _ p hp')⟩,
      fun hp' => hp.2 (nclose_subseteq _ _ p hp')⟩

@[rocq_alias cryptis.rep_copy_alloc]
theorem repCopy_alloc (a₀ : A) (h : ↑((N.@"server").@kI) ⊆ E) :
    termToken (GF := GF) kR E ==∗ repCopy kI kR N a₀ a₀ ∗
      termToken kR (E \ ↑((N.@"server").@kI)) := by
  unfold repCopy
  iintro Htok
  icases (termToken_difference h).mp $$ Htok with ⟨H1, H2⟩
  imodintro
  isplitl [H1]
  · ileft
    isplitr
    · ipureintro; rfl
    · iexact H1
  · iexact H2

@[rocq_alias cryptis.rep_main_update]
theorem repMain_update (a' : A) :
    repMain (GF := GF) kI kR N a -∗ repSync kI kR N a₀ a ==∗
      repMain kI kR N a' ∗ repUpdate kI kR N a₀ a a' := by
  unfold repSync repUpdate
  iintro H1 ⟨H2, Hs, Hc⟩
  imod replica_update a' $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iframe H1 H2 Hs Hc

@[rocq_alias cryptis.rep_copy_update]
theorem repCopy_update :
    repCopy (GF := GF) kI kR N a₀ a₁ -∗ repUpdate kI kR N a₀ a₂ a' ==∗
      ⌜a₁ = a₂⌝ ∗ repCopy kI kR N a₀ a' ∗ repSync kI kR N a₀ a' := by
  unfold repCopy repUpdate repSync
  iintro Hs ⟨Hc1, Hs2, Hu⟩
  icases Hs with (⟨%rfl, Hn⟩ | ⟨Hs1, #Hf1⟩) <;> icases Hu with (⟨%rfl, Hs3⟩ | #Hf2)
  · imod first_connection $$ Hn with #Hf
    imod replica_update a' $$ Hs2 Hs3 with ⟨Hs2, Hs3⟩
    imodintro
    isplitr
    · ipureintro; rfl
    isplitl [Hs2]
    · iright; iframe Hs2 Hf
    · iframe Hc1 Hs3; iright; iexact Hf
  · iexfalso; iapply Hf2 $$ Hn
  all_goals
    icases replica_agree $$ Hs1 Hs2 with %rfl
    imod replica_update a' $$ Hs1 Hs2 with ⟨Hs1, Hs2⟩
    imodintro
    isplitr
    · ipureintro; rfl
    isplitl [Hs1]
    · iright; iframe Hs1 Hf1
    · iframe Hc1 Hs2; iright; iexact Hf1

end Cryptis
