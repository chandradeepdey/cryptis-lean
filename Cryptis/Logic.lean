module

public import Iris.HeapLang.Lib.TicketLock
public import Cryptis.Core.Public

/-! The ghost state of Cryptis: term meta data, public terms, and the ticket lock of the network
channels. `cryptisCtx` is the invariant that protocol proofs carry around. Allocating the ghost
state also yields the tokens that let a protocol register the predicates of sealed messages and
hashes. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode

/-- The namespace of Cryptis. -/
@[rocq_alias cryptis.cryptisN]
def cryptisN : Namespace := nroot.@"cryptis"

/-- The ghost state of Cryptis, without its ghost names. Its parts are fields, so that the term
meta data and the public terms each keep the `MetaGS` they were allocated with. -/
@[rocq_alias cryptis.cryptisGpreS]
class CryptisGpreS (GF : BundledGFunctors) where
  termMeta : TermMetaGpreS GF
  isPublic : PublicGpreS GF
  tlock : TicketLock.TicketLockG GF

/-- The ghost state of Cryptis. -/
@[rocq_alias cryptis.cryptisGS]
class CryptisGS (GF : BundledGFunctors) where
  termMeta : TermMetaGS GF
  isPublic : PublicGS GF
  tlock : TicketLock.TicketLockG GF

attribute [instance_reducible, instance] CryptisGpreS.termMeta CryptisGpreS.isPublic
  CryptisGS.termMeta CryptisGS.isPublic

attribute [rocq_alias cryptis.CryptisGPreS] CryptisGpreS.mk
attribute [rocq_alias cryptis.cryptisGpreS_term_meta] CryptisGpreS.termMeta
attribute [rocq_alias cryptis.cryptisGpreS_public] CryptisGpreS.isPublic
attribute [rocq_alias cryptis.cryptisGpreS_tlock] CryptisGpreS.tlock
attribute [rocq_alias cryptis.CryptisGS] CryptisGS.mk
attribute [rocq_alias cryptis.cryptisGS_term_meta] CryptisGS.termMeta
attribute [rocq_alias cryptis.cryptisGS_public] CryptisGS.isPublic
attribute [rocq_alias cryptis.cryptisGS_tlock] CryptisGS.tlock

#rocq_ignore cryptis.«cryptisΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.subG_cryptisGpreS "Subsumed by BundledGFunctors typeclass synthesis"

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

/-- The invariant of Cryptis. -/
@[rocq_alias cryptis.cryptis_ctx]
def cryptisCtx [CryptisGS GF] : IProp GF := termMetaCtx

@[rocq_alias cryptis.cryptis_ctx_persistent]
instance cryptisCtx_persistent [CryptisGS GF] : Persistent (cryptisCtx (GF := GF)) := by
  unfold cryptisCtx; infer_instance

@[rocq_alias cryptis.cryptis_ctx_has_term_meta_ctx]
instance cryptisCtx_hasTermMetaCtx [CryptisGS GF] : HasTermMetaCtx (cryptisCtx (GF := GF)) :=
  ⟨.rfl⟩

@[rocq_alias cryptis.cryptisGS_alloc]
theorem cryptisGS_alloc [CryptisGpreS GF] (E : CoPset) :
    ⊢ |={E}=> ∃ _ : CryptisGS GF, cryptisCtx ∗ sealPredToken .aenc ⊤ ∗
      sealPredToken .sign ⊤ ∗ sealPredToken .senc ⊤ ∗ hashPredToken ⊤ := by
  imod termMetaGS_alloc (GF := GF) E with ⟨%tm, #Hctx⟩
  imod publicGS_alloc (GF := GF) E with ⟨%pub, Ha, Hs, He, Hh⟩
  imodintro
  iexists ⟨tm, pub, CryptisGpreS.tlock⟩
  iframe
  unfold cryptisCtx
  iexact Hctx

end Cryptis
