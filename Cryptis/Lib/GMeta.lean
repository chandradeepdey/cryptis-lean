module

public import Cryptis.Lib.BaseLogic

/-! Meta data attached to ghost names.

A ghost name carries data at each of its namespaces, in the way that `gen_heap` attaches meta data
to heap locations. `gmetaToken γ E` is the right to associate data with the namespaces in `E`, and
`gmeta γ N x` records that `x` is associated with `N`. Associating data spends the token for `N`,
and the data of a namespace is unique. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.Std ReservationMap

/-- Ghost state for meta data attached to ghost names. -/
@[rocq_alias cryptis.metaGS]
class MetaGS (GF : BundledGFunctors) where
  elemG : ElemG GF (constOF MetaUR)

#rocq_ignore cryptis.«metaΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.«subG_metaGS» "Subsumed by BundledGFunctors typeclass synthesis"

attribute [reducible] MetaGS.elemG
attribute [local instance] MetaGS.elemG

variable {GF : BundledGFunctors} [MetaGS GF] {L : Type} [Pos.Countable L]
local bi (IProp GF)

/-- The datum `x` is associated with the namespace `N` of the ghost name `γ`. -/
@[rocq_alias cryptis.gmeta]
def gmeta (γ : GName) (N : Namespace) (x : L) : IProp GF :=
  iOwn (F := constOF MetaUR) γ (ReservationMap.namespaceData N (toAgree ⟨Pos.Countable.encode x⟩))

/-- No data has been associated with the namespaces in `E` of the ghost name `γ`. -/
@[rocq_alias cryptis.gmeta_token]
def gmetaToken (γ : GName) (E : CoPset) : IProp GF :=
  iOwn (F := constOF MetaUR) γ (mkToken E)

@[rocq_alias cryptis.gmeta_timeless]
instance gmeta_timeless (γ : GName) (N : Namespace) (x : L) :
    Timeless (gmeta (GF := GF) γ N x) := by
  unfold gmeta ReservationMap.namespaceData; infer_instance

@[rocq_alias cryptis.gmeta_token_timeless]
instance gmetaToken_timeless (γ : GName) (E : CoPset) : Timeless (gmetaToken (GF := GF) γ E) := by
  unfold gmetaToken; infer_instance

@[rocq_alias cryptis.gmeta_persistent]
instance gmeta_persistent (γ : GName) (N : Namespace) (x : L) :
    Persistent (gmeta (GF := GF) γ N x) := by
  unfold gmeta; infer_instance

@[rocq_alias cryptis.gmeta_token_alloc]
theorem gmetaToken_alloc : ⊢ |==> ∃ γ, gmetaToken (GF := GF) γ ⊤ :=
  iOwn_alloc _ valid_token

@[rocq_alias cryptis.gmeta_token_disj]
theorem gmetaToken_disj {γ : GName} {E1 E2 : CoPset} :
    gmetaToken (GF := GF) γ E1 -∗ gmetaToken γ E2 -∗ ⌜E1 ## E2⌝ := by
  unfold gmetaToken
  iintro H1 H2
  icombine H1 H2 gives %h
  ipureintro
  exact valid_token_op_iff_disj.mp h

@[rocq_alias cryptis.gmeta_set]
theorem gmeta_set {γ : GName} {E : CoPset} {N : Namespace} (x : L) (h : ↑N ⊆ E) :
    gmetaToken (GF := GF) γ E ==∗ gmeta γ N x := by
  unfold gmetaToken gmeta
  iintro H
  iapply iOwn_update (ReservationMap.alloc_namespaceData h Agree.toAgree_valid) $$ H

@[rocq_alias cryptis.gmeta_gmeta_token]
theorem gmetaToken_gmeta {γ : GName} {E : CoPset} {N : Namespace} {x : L} (h : ↑N ⊆ E) :
    gmetaToken (GF := GF) γ E -∗ gmeta γ N x -∗ False := by
  unfold gmetaToken gmeta
  iintro H1 H2
  icombine H1 H2 gives %hv
  exact (ReservationMap.not_valid_mkToken_op_namespaceData h hv).elim

@[rocq_alias cryptis.gmeta_agree]
theorem gmeta_agree {γ : GName} {N : Namespace} {x1 x2 : L} :
    gmeta (GF := GF) γ N x1 -∗ gmeta γ N x2 -∗ ⌜x1 = x2⌝ := by
  unfold gmeta ReservationMap.namespaceData
  iintro H1 H2
  icombine H1 H2 gives %hv
  ipureintro
  rw [← singleton_op, valid_singleton, toAgree_op_valid_iff_eq] at hv
  exact Pos.encode_inj (DiscreteO.eqv_inj hv)

@[rocq_alias cryptis.gmeta_token_difference]
theorem gmetaToken_difference {γ : GName} {E1 E2 : CoPset} (h : E1 ⊆ E2) :
    gmetaToken (GF := GF) γ E2 ⊣⊢ gmetaToken γ E1 ∗ gmetaToken γ (E2 \ E1) := by
  unfold gmetaToken
  rw [token_difference h]
  exact iOwn_op

@[rocq_alias cryptis.gmeta_set']
theorem gmeta_set_difference {γ : GName} {E : CoPset} {N : Namespace} (x : L) (h : ↑N ⊆ E) :
    gmetaToken (GF := GF) γ E ==∗ gmeta γ N x ∗ gmetaToken γ (E \ ↑N) := by
  iintro H
  icases (gmetaToken_difference h).mp $$ H with ⟨H1, H2⟩
  imod gmeta_set x LawfulSet.subset_refl $$ H1 with H1
  imodintro
  iframe

@[rocq_alias cryptis.gmeta_token_drop]
theorem gmetaToken_drop {γ : GName} {E1 E2 : CoPset} (h : E1 ⊆ E2) :
    gmetaToken (GF := GF) γ E2 -∗ gmetaToken γ E1 :=
  entails_wand <| (gmetaToken_difference h).mp.trans sep_elim_left

end Cryptis
