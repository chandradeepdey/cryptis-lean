module

public import Cryptis.Lib.GMeta

/-! Ghost state indexed by namespaces.

`nown γ N a` owns `a` at a ghost name that the meta data of `γ` associates with the namespace
`N`. Allocating it consumes the meta token of `γ` for `N`, so each namespace of `γ` names at most
one ghost location. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.Std Iris.ProofMode COFE

variable {GF : BundledGFunctors} [MetaGS GF] {F : OFunctorPre} [RFunctorContractive F]
  [ElemG GF F]
local bi (IProp GF)

/-- Ownership of `a` at the ghost name associated with the namespace `N` of `γ`. -/
@[rocq_alias cryptis.nown]
def nown (γ : GName) (N : Namespace) (a : F.ap (IProp GF)) : IProp GF :=
  iprop(∃ γ', gmeta γ N γ' ∧ iOwn γ' a)

variable {γ : GName} {N : Namespace}

@[rocq_alias cryptis.nown_alloc]
theorem nown_alloc {E : CoPset} (a : F.ap (IProp GF)) (h : ↑N ⊆ E) (ha : ✓ a) :
    gmetaToken (GF := GF) γ E ==∗ nown γ N a ∗ gmetaToken γ (E \ ↑N) := by
  unfold nown
  iintro H
  imod iOwn_alloc a ha with ⟨%γ', Ha⟩
  imod gmeta_set_difference γ' h $$ H with ⟨#Hm, H⟩
  imodintro
  iframe
  iexact Hm

@[rocq_alias cryptis.nown_token]
theorem nown_token {E : CoPset} {a : F.ap (IProp GF)} (h : ↑N ⊆ E) :
    gmetaToken (GF := GF) γ E -∗ nown γ N a -∗ False := by
  unfold nown
  iintro H ⟨%γ', #Hm, -⟩
  iapply gmetaToken_gmeta h $$ H Hm

@[rocq_alias cryptis.nown_valid]
theorem nown_valid {a : F.ap (IProp GF)} : nown γ N a -∗ ✓ a := by
  unfold nown
  iintro ⟨%γ', -, Ha⟩
  iapply iOwn_cmraValid $$ Ha

@[rocq_alias cryptis.nown_valid_2]
theorem nown_valid_2 {a1 a2 : F.ap (IProp GF)} : nown γ N a1 -∗ nown γ N a2 -∗ ✓ (a1 • a2) := by
  unfold nown
  iintro ⟨%γ1, #Hm1, H1⟩ ⟨%γ2, #Hm2, H2⟩
  icases gmeta_agree $$ Hm1 Hm2 with %rfl
  iapply iOwn_cmraValid_op $$ [H1 H2]
  isplitl [H1] <;> iassumption

@[rocq_alias cryptis.nown_update]
theorem nown_update {a a' : F.ap (IProp GF)} (h : a ~~> a') : nown γ N a ==∗ nown γ N a' := by
  unfold nown
  iintro ⟨%γ', #Hm, Ha⟩
  imod iOwn_update h $$ Ha with Ha
  imodintro
  iexists γ'
  isplit <;> iassumption

@[rocq_alias cryptis.nown_core_persistent]
instance nown_persistent {a : F.ap (IProp GF)} [ORA.CoreId a] : Persistent (nown γ N a) := by
  unfold nown; infer_instance

@[rocq_alias cryptis.nown_timeless]
instance nown_timeless {a : F.ap (IProp GF)} [OFE.DiscreteE a] : Timeless (nown γ N a) := by
  unfold nown; infer_instance

@[rocq_alias cryptis.nown_ne]
instance nown_ne : OFE.NonExpansive (nown (GF := GF) (F := F) γ N) where
  ne _ _ _ h := exists_ne fun _ => and_ne.ne .rfl (iOwn_ne.ne h)

#rocq_ignore cryptis.nown_proper "Derivable using NonExpansive.eqv"

@[rocq_alias cryptis.nown_op]
theorem nown_op {a1 a2 : F.ap (IProp GF)} : nown γ N (a1 • a2) ⊣⊢ nown γ N a1 ∗ nown γ N a2 := by
  unfold nown
  constructor
  · iintro ⟨%γ', #Hm, H⟩
    icases iOwn_op.mp $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists γ'; isplit <;> iassumption
    · iexists γ'; isplit <;> iassumption
  · iintro ⟨⟨%γ1, #Hm1, H1⟩, ⟨%γ2, #Hm2, H2⟩⟩
    icases gmeta_agree $$ Hm1 Hm2 with %rfl
    iexists γ1
    isplit
    · iassumption
    · iapply iOwn_op.mpr; isplitl [H1] <;> iassumption

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.from_sep_nown]
instance fromSep_nown {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    FromSep (nown γ N a) (nown γ N b1) (nown γ N b2) where
  from_sep := by rw [h.is_op]; exact nown_op.mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.combine_sep_as_nown]
instance combineSepAs_nown {a b1 b2 : F.ap (IProp GF)} [h : IsOp .merge a b1 b2] :
    CombineSepAs (nown γ N b1) (nown γ N b2) (nown γ N a) where
  combine_sep_as := by rw [h.is_op]; exact nown_op.mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.into_sep_nown]
instance intoSep_nown {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    IntoSep (nown γ N a) (nown γ N b1) (nown γ N b2) where
  into_sep := by rw [h.is_op]; exact nown_op.mp

@[rocq_alias cryptis.nown_mono]
theorem nown_mono {a1 a2 : F.ap (IProp GF)} (h : a1 ≼ a2) : nown γ N a2 -∗ nown γ N a1 := by
  obtain ⟨c, rfl⟩ := h
  exact entails_wand <| nown_op.mp.trans sep_elim_left

@[rocq_alias cryptis.nown_update_2]
theorem nown_update_2 {a1 a2 a' : F.ap (IProp GF)} (h : a1 • a2 ~~> a') :
    nown γ N a1 -∗ nown γ N a2 ==∗ nown γ N a' := by
  iintro H1 H2
  iapply nown_update h
  iapply nown_op.mpr
  isplitl [H1] <;> iassumption

end Cryptis
