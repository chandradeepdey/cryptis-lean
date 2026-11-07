module

public import Cryptis.Core.Minted
public import Cryptis.Lib.NOwn
public import Cryptis.Lib.SavedProp
public import Iris.Instances.Lib.GhostMap

/-! Meta data attached to terms.

Protocol proofs attach ghost state to terms, at namespaces: a nonce may record the session it
belongs to, or carry a saved proposition. An invariant gives each minted term a ghost name, and
the meta data of the term lives at that ghost name. `termToken t E` is the right to attach data
to the namespaces in `E` of the term `t`; it is created once for each term, when the term is
minted, and spent as data is attached.

- The invariant, ghost names, tokens, and data attached with `termMeta`.
- `termOwn` owns a ghost resource at a namespace of a term.
- Allocation: the tokens of a set of terms, allocated in the step that mints them.
- `termProp` and `termPred` attach a saved proposition or predicate to a namespace of a term. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.Std Iris.HeapLang Iris.ProofMode COFE Term BigSepFinset

/-- Finite maps keyed by terms. -/
abbrev TermMap (V : Type) : Type := Std.ExtTreeMap Term V compare

/-- The ghost state of term meta data, without its ghost name. -/
@[rocq_alias cryptis.term_metaGpreS]
class TermMetaGpreS (GF : BundledGFunctors) where
  metaGS : MetaGS GF
  names : GhostMapG GF Term GName TermMap

/-- The ghost state of term meta data. -/
@[rocq_alias cryptis.term_metaGS]
class TermMetaGS (GF : BundledGFunctors) extends TermMetaGpreS GF where
  name : GName

attribute [rocq_alias cryptis.TermMetaGPreS] TermMetaGpreS.mk
attribute [rocq_alias cryptis.term_meta_meta] TermMetaGpreS.metaGS
attribute [rocq_alias cryptis.term_meta_names] TermMetaGpreS.names
attribute [rocq_alias cryptis.TermMetaGS] TermMetaGS.mk
attribute [rocq_alias cryptis.term_meta_name] TermMetaGS.name
attribute [rocq_alias cryptis.term_meta_inG] TermMetaGS.toTermMetaGpreS

#rocq_ignore cryptis.«term_metaΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.«subG_term_metaGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

attribute [local instance_reducible, local instance] TermMetaGpreS.metaGS TermMetaGpreS.names

/-- The namespace of the term meta data invariant. -/
def termMetaN : Namespace := (nroot.@"cryptis").@"meta"

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

/-- The invariant of term meta data: the terms with a ghost name are minted. -/
@[rocq_alias cryptis.term_meta_inv]
def termMetaInv [TermMetaGS GF] : IProp GF :=
  iprop(∃ names : TermMap GName, (TermMetaGS.name GF ↪●MAP names) ∗
    [∗map] t ↦ _γ ∈ names, minted t)

/-- The invariant of term meta data. -/
@[rocq_alias cryptis.term_meta_ctx]
def termMetaCtx [TermMetaGS GF] : IProp GF := inv termMetaN termMetaInv

@[rocq_alias cryptis.term_metaGS_alloc]
theorem termMetaGS_alloc [TermMetaGpreS GF] (E : CoPset) :
    ⊢ |={E}=> ∃ _ : TermMetaGS GF, termMetaCtx := by
  imod ghost_map_alloc_empty (K := Term) (V := GName) (H := TermMap) with ⟨%γ, Hauth⟩
  let G : TermMetaGS GF := ⟨γ⟩
  iexists G
  unfold termMetaCtx termMetaInv
  iapply inv_alloc
  inext
  iexists ∅
  iframe Hauth
  iapply BigSepM.bigSepM_empty.mpr
  iempintro

variable [TermMetaGS GF]

@[rocq_alias cryptis.term_meta_inv_timeless]
instance termMetaInv_timeless : Timeless (termMetaInv (GF := GF)) := by
  unfold termMetaInv; infer_instance

@[rocq_alias cryptis.term_meta_ctx_persistent]
instance termMetaCtx_persistent : Persistent (termMetaCtx (GF := GF)) := by
  unfold termMetaCtx; infer_instance

/-- `ctx` is a persistent proposition that contains the term meta data invariant. -/
@[rocq_alias cryptis.HasTermMetaCtx]
class HasTermMetaCtx (ctx : IProp GF) : Prop where
  entails : ctx ⊢ termMetaCtx
  [persistent : Persistent ctx]

attribute [rocq_alias cryptis.has_term_meta_ctx] HasTermMetaCtx.entails
attribute [rocq_alias cryptis.has_term_meta_ctx_persistent] HasTermMetaCtx.persistent
attribute [instance] HasTermMetaCtx.persistent

/-- The ghost name `γ` holds the meta data of the minted term `t`. -/
@[rocq_alias cryptis.term_name]
def termName (t : Term) (γ : GName) : IProp GF :=
  iprop(minted t ∗ (TermMetaGS.name GF ↪◯MAP[t]{.discard} γ))

@[rocq_alias cryptis.term_name_persistent]
instance termName_persistent (t : Term) (γ : GName) : Persistent (termName (GF := GF) t γ) := by
  unfold termName; infer_instance

@[rocq_alias cryptis.term_name_timeless]
instance termName_timeless (t : Term) (γ : GName) : Timeless (termName (GF := GF) t γ) := by
  unfold termName; infer_instance

variable {t : Term} {γ γ1 γ2 : GName} {N : Namespace} {E E1 E2 : CoPset}

@[rocq_alias cryptis.term_name_agree]
theorem termName_agree : termName (GF := GF) t γ1 -∗ termName t γ2 -∗ ⌜γ1 = γ2⌝ := by
  unfold termName
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  iapply ghost_map_elem_agree $$ [H1 H2]
  isplitl [H1] <;> iassumption

@[rocq_alias cryptis.term_name_minted]
theorem termName_minted : termName (GF := GF) t γ -∗ minted t := by
  unfold termName
  iintro ⟨H, -⟩
  iexact H

/-- No data has been associated with the namespaces in `E` of the term `t`. -/
@[rocq_alias cryptis.term_token]
def termToken (t : Term) (E : CoPset) : IProp GF := iprop(∃ γ, termName t γ ∗ gmetaToken γ E)

/-- The datum `x` is associated with the namespace `N` of the term `t`. -/
@[rocq_alias cryptis.term_meta]
def termMeta {L : Type} [Pos.Countable L] (t : Term) (N : Namespace) (x : L) : IProp GF :=
  iprop(∃ γ, termName t γ ∗ gmeta γ N x)

variable {L : Type} [Pos.Countable L]

@[rocq_alias cryptis.term_token_minted]
theorem termToken_minted : termToken (GF := GF) t E -∗ minted t := by
  unfold termToken
  iintro ⟨%γ, #Hn, -⟩
  iapply termName_minted $$ Hn

@[rocq_alias cryptis.term_meta_minted]
theorem termMeta_minted {x : L} : termMeta (GF := GF) t N x -∗ minted t := by
  unfold termMeta
  iintro ⟨%γ, #Hn, -⟩
  iapply termName_minted $$ Hn

@[rocq_alias cryptis.term_token_timeless]
instance termToken_timeless (t : Term) (E : CoPset) : Timeless (termToken (GF := GF) t E) := by
  unfold termToken; infer_instance

@[rocq_alias cryptis.term_meta_timeless]
instance termMeta_timeless (t : Term) (N : Namespace) (x : L) :
    Timeless (termMeta (GF := GF) t N x) := by
  unfold termMeta; infer_instance

@[rocq_alias cryptis.term_meta_persistent]
instance termMeta_persistent (t : Term) (N : Namespace) (x : L) :
    Persistent (termMeta (GF := GF) t N x) := by
  unfold termMeta; infer_instance

@[rocq_alias cryptis.term_token_drop]
theorem termToken_drop (h : E1 ⊆ E2) : termToken (GF := GF) t E2 -∗ termToken t E1 := by
  unfold termToken
  iintro ⟨%γ, #Hn, H⟩
  iexists γ
  isplit
  · iexact Hn
  · iapply gmetaToken_drop h $$ H

@[rocq_alias cryptis.term_token_disj]
theorem termToken_disj : termToken (GF := GF) t E1 -∗ termToken t E2 -∗ ⌜E1 ## E2⌝ := by
  unfold termToken
  iintro ⟨%γ1, #Hn1, H1⟩ ⟨%γ2, #Hn2, H2⟩
  icases termName_agree $$ Hn1 Hn2 with %rfl
  iapply gmetaToken_disj $$ H1 H2

@[rocq_alias cryptis.term_token_difference]
theorem termToken_difference (h : E1 ⊆ E2) :
    termToken (GF := GF) t E2 ⊣⊢ termToken t E1 ∗ termToken t (E2 \ E1) := by
  unfold termToken
  constructor
  · iintro ⟨%γ, #Hn, H⟩
    icases (gmetaToken_difference h).mp $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists γ; iframe Hn H1
    · iexists γ; iframe Hn H2
  · iintro ⟨⟨%γ1, #Hn1, H1⟩, ⟨%γ2, #Hn2, H2⟩⟩
    icases termName_agree $$ Hn1 Hn2 with %rfl
    iexists γ1
    iframe Hn1
    iapply (gmetaToken_difference h).mpr
    iframe

@[rocq_alias cryptis.term_meta_token]
theorem termMeta_token {x : L} (h : ↑N ⊆ E) :
    termToken (GF := GF) t E -∗ termMeta t N x -∗ False := by
  unfold termToken termMeta
  iintro ⟨%γ1, #Hn1, H1⟩ ⟨%γ2, #Hn2, #H2⟩
  icases termName_agree $$ Hn1 Hn2 with %rfl
  iapply gmetaToken_gmeta h $$ H1 H2

@[rocq_alias cryptis.term_meta_set']
theorem termMeta_set_difference (x : L) (h : ↑N ⊆ E) :
    termToken (GF := GF) t E ==∗ termMeta t N x ∗ termToken t (E \ ↑N) := by
  unfold termToken termMeta
  iintro ⟨%γ, #Hn, H⟩
  imod gmeta_set_difference x h $$ H with ⟨#Hm, H⟩
  imodintro
  isplitr [H]
  · iexists γ; iframe Hn Hm
  · iexists γ; iframe Hn H

@[rocq_alias cryptis.term_meta_set]
theorem termMeta_set (x : L) (h : ↑N ⊆ E) : termToken (GF := GF) t E ==∗ termMeta t N x := by
  iintro H
  imod termMeta_set_difference x h $$ H with ⟨#Hm, -⟩
  imodintro
  iexact Hm

@[rocq_alias cryptis.term_meta_agree]
theorem termMeta_agree {x1 x2 : L} :
    termMeta (GF := GF) t N x1 -∗ termMeta t N x2 -∗ ⌜x1 = x2⌝ := by
  unfold termMeta
  iintro ⟨%γ1, #Hn1, #H1⟩ ⟨%γ2, #Hn2, #H2⟩
  icases termName_agree $$ Hn1 Hn2 with %rfl
  iapply gmeta_agree $$ H1 H2

@[rocq_alias cryptis.term_token_switch]
theorem termToken_switch (t : Term) (N : Namespace) (Q : IProp GF) :
    ⊢ switch (termToken t ↑N) Q := by
  unfold switch
  iexists termMeta t N ()
  isplit <;> iintro !>
  · iintro ⟨H, #Hm⟩
    iexfalso
    iapply termMeta_token LawfulSet.subset_refl $$ H Hm
  · iintro H
    imod termMeta_set () LawfulSet.subset_refl $$ H with #Hm
    imodintro
    iexact Hm

section TermOwn

variable {F : OFunctorPre} [RFunctorContractive F] [ElemG GF F]

/-- Ownership of `a` at the namespace `N` of the term `t`. -/
@[rocq_alias cryptis.term_own]
def termOwn (t : Term) (N : Namespace) (a : F.ap (IProp GF)) : IProp GF :=
  iprop(∃ γ, termName t γ ∗ nown γ N a)

@[rocq_alias cryptis.term_own_alloc]
theorem termOwn_alloc (a : F.ap (IProp GF)) (h : ↑N ⊆ E) (ha : ✓ a) :
    termToken (GF := GF) t E ==∗ termOwn t N a ∗ termToken t (E \ ↑N) := by
  unfold termOwn termToken
  iintro ⟨%γ, #Hn, H⟩
  imod nown_alloc a h ha $$ H with ⟨Ho, H⟩
  imodintro
  isplitl [Ho]
  · iexists γ; iframe Hn Ho
  · iexists γ; iframe Hn H

@[rocq_alias cryptis.term_token_own]
theorem termToken_own {a : F.ap (IProp GF)} (h : ↑N ⊆ E) :
    termToken (GF := GF) t E -∗ termOwn t N a -∗ False := by
  unfold termOwn termToken
  iintro ⟨%γ1, #Hn1, H1⟩ ⟨%γ2, #Hn2, H2⟩
  icases termName_agree $$ Hn1 Hn2 with %rfl
  iapply nown_token h $$ H1 H2

@[rocq_alias cryptis.term_own_valid]
theorem termOwn_valid {a : F.ap (IProp GF)} : termOwn (GF := GF) t N a -∗ ✓ a := by
  unfold termOwn
  iintro ⟨%γ, -, H⟩
  iapply nown_valid $$ H

@[rocq_alias cryptis.term_own_valid_2]
theorem termOwn_valid_2 {a1 a2 : F.ap (IProp GF)} :
    termOwn (GF := GF) t N a1 -∗ termOwn t N a2 -∗ ✓ (a1 • a2) := by
  unfold termOwn
  iintro ⟨%γ1, #Hn1, H1⟩ ⟨%γ2, #Hn2, H2⟩
  icases termName_agree $$ Hn1 Hn2 with %rfl
  iapply nown_valid_2 $$ H1 H2

@[rocq_alias cryptis.term_own_update]
theorem termOwn_update {a a' : F.ap (IProp GF)} (h : a ~~> a') :
    termOwn (GF := GF) t N a ==∗ termOwn t N a' := by
  unfold termOwn
  iintro ⟨%γ, #Hn, H⟩
  imod nown_update h $$ H with H
  imodintro
  iexists γ
  iframe Hn H

@[rocq_alias cryptis.term_own_core_persistent]
instance termOwn_persistent {a : F.ap (IProp GF)} [ORA.CoreId a] :
    Persistent (termOwn (GF := GF) t N a) := by
  unfold termOwn; infer_instance

@[rocq_alias cryptis.term_own_timeless]
instance termOwn_timeless {a : F.ap (IProp GF)} [OFE.DiscreteE a] :
    Timeless (termOwn (GF := GF) t N a) := by
  unfold termOwn; infer_instance

@[rocq_alias cryptis.term_own_ne]
instance termOwn_ne : OFE.NonExpansive (termOwn (GF := GF) (F := F) t N) where
  ne _ _ _ h := exists_ne fun _ => sep_ne.ne .rfl (nown_ne.ne h)

#rocq_ignore cryptis.term_own_proper "Derivable using NonExpansive.eqv"

@[rocq_alias cryptis.term_own_op]
theorem termOwn_op {a1 a2 : F.ap (IProp GF)} :
    termOwn (GF := GF) t N (a1 • a2) ⊣⊢ termOwn t N a1 ∗ termOwn t N a2 := by
  unfold termOwn
  constructor
  · iintro ⟨%γ, #Hn, H⟩
    icases nown_op.mp $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists γ; iframe Hn H1
    · iexists γ; iframe Hn H2
  · iintro ⟨⟨%γ1, #Hn1, H1⟩, ⟨%γ2, #Hn2, H2⟩⟩
    icases termName_agree $$ Hn1 Hn2 with %rfl
    iexists γ1
    iframe Hn1
    iapply nown_op.mpr
    iframe

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.from_sep_term_own]
instance fromSep_termOwn {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    FromSep (termOwn (GF := GF) t N a) (termOwn t N b1) (termOwn t N b2) where
  from_sep := by rw [h.is_op]; exact termOwn_op.mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.combine_sep_as_term_own]
instance combineSepAs_termOwn {a b1 b2 : F.ap (IProp GF)} [h : IsOp .merge a b1 b2] :
    CombineSepAs (termOwn (GF := GF) t N b1) (termOwn t N b2) (termOwn t N a) where
  combine_sep_as := by rw [h.is_op]; exact termOwn_op.mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias cryptis.into_sep_term_own]
instance intoSep_termOwn {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    IntoSep (termOwn (GF := GF) t N a) (termOwn t N b1) (termOwn t N b2) where
  into_sep := by rw [h.is_op]; exact termOwn_op.mp

@[rocq_alias cryptis.combine_sep_gives_term_own]
instance combineSepGives_termOwn {a1 a2 : F.ap (IProp GF)} :
    CombineSepGives (termOwn (GF := GF) t N a1) (termOwn t N a2) iprop(✓ (a1 • a2)) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    ihave #H := termOwn_valid_2 $$ H1 H2
    iintro !>
    iexact H

@[rocq_alias cryptis.term_own_mono]
theorem termOwn_mono {a1 a2 : F.ap (IProp GF)} (h : a1 ≼ a2) :
    termOwn (GF := GF) t N a2 -∗ termOwn t N a1 := by
  obtain ⟨c, rfl⟩ := h
  exact entails_wand <| termOwn_op.mp.trans sep_elim_left

@[rocq_alias cryptis.term_own_update_2]
theorem termOwn_update_2 {a1 a2 a' : F.ap (IProp GF)} (h : a1 • a2 ~~> a') :
    termOwn (GF := GF) t N a1 -∗ termOwn t N a2 ==∗ termOwn t N a' := by
  iintro H1 H2
  iapply termOwn_update h
  iapply termOwn_op.mpr
  isplitl [H1] <;> iassumption

end TermOwn

/-- Allocate a ghost name for each term of `T`, and its token once the term is minted. -/
theorem termToken_alloc_names (T : Finset Term) (names : TermMap GName)
    (h : ∀ t ∈ T, PartialMap.get? names t = none) :
    (TermMetaGS.name GF ↪●MAP names) ==∗ ∃ names' : TermMap GName,
      ⌜∀ t, PartialMap.dom names' t ↔ PartialMap.dom names t ∨ t ∈ T⌝ ∗
      (TermMetaGS.name GF ↪●MAP names') ∗ [∗finset] t ∈ T, (minted t -∗ termToken t ⊤) := by
  induction T using Finset.induction_on generalizing names with
  | empty =>
    iintro H
    imodintro
    iexists names
    iframe H
    isplitr
    · ipureintro; simp
    · iapply bigSepFinset_empty.mpr
      iempintro
  | insert t T ht ih =>
    rw [(bigSepFinset_insert ht).to_eq]
    iintro H
    imod gmetaToken_alloc with ⟨%γ, Hγ⟩
    imod ghost_map_insert_persist t γ (h t (Finset.mem_insert_self t T)) $$ H with ⟨H, #Ht⟩
    imod ih _ (fun u hu => by
        rw [get?_insert_ne (by rintro rfl; exact ht hu), h u (Finset.mem_insert_of_mem hu)]) $$ H
      with ⟨%names', %hdom, H, Hts⟩
    imodintro
    iexists names'
    iframe H Hts
    isplitr
    · ipureintro
      intro u
      rw [hdom, LawfulPartialMap.dom_insert_iff]
      simp [eq_comm, or_assoc, or_left_comm]
    · iintro #Hm
      iunfold termToken, termName
      iexists γ
      iframe Hm Ht Hγ

@[rocq_alias cryptis.term_token_alloc_aux]
theorem termToken_alloc_inv (T : Finset Term) (P Q : IProp GF) (E : CoPset) :
    (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted t -∗ False) -∗
    (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted t) -∗
    (P ∧ |={E}=> Q) -∗
    termMetaInv ={E}=∗ termMetaInv ∗ Q ∗ [∗finset] t ∈ T, termToken t ⊤ := by
  unfold termMetaInv
  iintro HPE HQE HPQ ⟨%names, Hauth, #Hnames⟩
  ihave #Hnames := BigSepM.bigSepM_forall.mp $$ Hnames
  ihave %hdis : ⌜∀ t ∈ T, PartialMap.get? names t = none⌝ $$ [#]
  · by_cases hc : ∀ t ∈ T, PartialMap.get? names t = none
    · ipureintro; exact hc
    obtain ⟨t, ht, γ, hγ⟩ : ∃ t ∈ T, ∃ γ, PartialMap.get? names t = some γ := by
      simpa [Option.ne_none_iff_exists'] using hc
    icases HPQ with ⟨HP, -⟩
    iexfalso
    iapply HPE $$ %t %ht HP
    iapply Hnames $$ %t %γ %hγ
  imod termToken_alloc_names T names hdis $$ Hauth with ⟨%names', %hdom, Hauth, Htoks⟩
  icases HPQ with ⟨-, HQ⟩
  imod HQ with HQ
  ihave #HT : ∀ t, ⌜t ∈ T⌝ → minted t $$ [#]
  · iintro %t %ht
    iapply HQE $$ %t %ht HQ
  imodintro
  isplitl [Hauth]
  · iexists names'
    iframe Hauth
    iapply BigSepM.bigSepM_forall.mpr
    iintro %t %γ %ht
    rcases (hdom t).mp (Option.isSome_iff_exists.mpr ⟨γ, ht⟩) with h | h
    · obtain ⟨γ', hγ'⟩ := Option.isSome_iff_exists.mp h
      iapply Hnames $$ %t %γ' %hγ'
    · iapply HT $$ %t %h
  iframe HQ
  iapply BigSepMS.bigSepMS_impl $$ Htoks
  iintro !> %t %ht Ht
  iapply Ht
  iapply HT $$ %t %(Multiset.mem_toIris.mp ht)

@[rocq_alias cryptis.term_token_alloc]
theorem termToken_alloc {ctx : IProp GF} [HasTermMetaCtx ctx] (T : Finset Term) (P Q : IProp GF)
    (h : ↑termMetaN ⊆ E) :
    ctx -∗
    (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted t -∗ False) -∗
    (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted t) -∗
    (P ∧ |={E \ ↑termMetaN}=> Q) ={E}=∗
    Q ∗ [∗finset] t ∈ T, termToken t ⊤ := by
  iintro #Hctx H1 H2 H3
  ihave #Hinv := (HasTermMetaCtx.entails : ctx ⊢ termMetaCtx) $$ Hctx
  iunfold termMetaCtx at Hinv
  iinv Hinv with >Hi
  imod termToken_alloc_inv T P Q _ $$ H1 H2 H3 Hi with ⟨Hi, HQ, HT⟩
  imodintro
  isplitl [Hi]
  · inext; iexact Hi
  · iframe

section TermProp

variable [SavedPropG GF]

/-- The proposition saved at the namespace `N` of the term `t` holds. -/
@[rocq_alias cryptis.term_prop]
def termProp (t : Term) (N : Namespace) : IProp GF :=
  iprop(∃ P : IProp GF, termOwn t N (savedProp .discard P) ∧ ▷ P)

@[rocq_alias cryptis.term_prop_alloc]
theorem termProp_alloc (N : Namespace) (P : IProp GF) (h : ↑N ⊆ E) :
    termToken (GF := GF) t E ==∗ □ (termProp t N ↔ ▷ P) ∗ termToken t (E \ ↑N) := by
  unfold termProp
  iintro H
  imod termOwn_alloc _ h (savedProp_valid.mpr DFrac.valid_discard) $$ H with ⟨#Ho, H⟩
  imodintro
  iframe H
  iintro !>
  isplit
  · iintro ⟨%Q, #Ho', HQ⟩
    ihave #Hv := termOwn_valid_2 $$ Ho Ho'
    icases (savedProp_op_validI (P := P) (Q := Q)).mp $$ Hv with ⟨-, #Heq⟩
    inext
    irewrite [Heq]
    · exact OFE.id_ne
    iexact HQ
  · iintro HP
    iexists P
    isplit
    · iexact Ho
    · iexact HP

@[rocq_alias cryptis.term_token_prop]
theorem termToken_prop (h : ↑N ⊆ E) : termToken (GF := GF) t E -∗ termProp t N -∗ False := by
  unfold termProp
  iintro H ⟨%P, #Ho, -⟩
  iapply termToken_own h $$ H Ho

end TermProp

section TermPred

variable {A : Type} [SavedPredG GF A]

/-- The predicate saved at the namespace `N` of the term `t` holds of `x`. -/
@[rocq_alias cryptis.term_pred]
def termPred (t : Term) (N : Namespace) (x : A) : IProp GF :=
  iprop(∃ φ : A → IProp GF, termOwn t N (savedPred .discard φ) ∧ ▷ φ x)

@[rocq_alias cryptis.term_pred_alloc]
theorem termPred_alloc (N : Namespace) (φ : A → IProp GF) (h : ↑N ⊆ E) :
    termToken (GF := GF) t E ==∗ □ (∀ x, termPred t N x ↔ ▷ φ x) ∗ termToken t (E \ ↑N) := by
  unfold termPred
  iintro H
  imod termOwn_alloc _ h (savedPred_valid.mpr DFrac.valid_discard) $$ H with ⟨#Ho, H⟩
  imodintro
  iframe H
  iintro !> %x
  isplit
  · iintro ⟨%ψ, #Ho', Hψ⟩
    ihave #Hv := termOwn_valid_2 $$ Ho Ho'
    icases (savedPred_op_validI (φ := φ) (ψ := ψ)).mp $$ Hv with ⟨-, #Heq⟩
    ispecialize Heq $$ %x
    inext
    irewrite [Heq]
    · exact OFE.id_ne
    iexact Hψ
  · iintro Hφ
    iexists φ
    isplit
    · iexact Ho
    · iexact Hφ

@[rocq_alias cryptis.term_token_pred]
theorem termToken_pred {x : A} (h : ↑N ⊆ E) :
    termToken (GF := GF) t E -∗ termPred t N x -∗ False := by
  unfold termPred
  iintro H ⟨%φ, #Ho, -⟩
  iapply termToken_own h $$ H Ho

end TermPred

end Cryptis
