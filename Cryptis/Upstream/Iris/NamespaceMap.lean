module

public import Iris.Algebra.ReservationMap
public import Iris.Algebra.Updates
public import Cryptis.Upstream.Iris.Namespaces

/-! Upstream candidate (Iris-Lean): reservation-map entries at the position of a namespace, for
`Iris/Algebra/ReservationMap.lean`.

`ReservationMap.namespaceData N a` is the entry `a` at the position that the namespace `N` owns.
It is allocated from a token for a mask that contains `N`, and it is incompatible with such a
token. -/

@[expose] public section

namespace Iris

open Iris.Std ReservationMap

variable {A : Type} [ORA A] {H : Type → Type} [LawfulPartialMap H Pos]

@[rocq_alias cryptis.reservation_map_disj]
theorem ReservationMap.not_mem_of_valid_mkToken_singleton {E : CoPset} {k : Pos} {a : A}
    (h : ✓ (mkToken (H := H) E • singleton k a)) : k ∉ E :=
  have h' : ✓ (mkData (H := H) (PartialMap.singleton k a) • mkToken E) := by rwa [ORA.comm'] at h
  (disj_of_valid_data_op_token _ E h' k).resolve_left <| by
    rw [LawfulPartialMap.get?_singleton_eq rfl]; exact Option.some_ne_none _

/-- The reservation-map entry `a` at the position that namespace `N` owns. -/
@[rocq_alias cryptis.namespace_map_data]
def ReservationMap.namespaceData (N : Namespace) (a : A) : ReservationMap A H :=
  .singleton (Pos.flatten N) a

@[rocq_alias cryptis.namespace_map_alloc_update]
theorem ReservationMap.alloc_namespaceData {E : CoPset} {N : Namespace} {a : A} (h : ↑N ⊆ E)
    (ha : ✓ a) :
    mkToken (H := H) E ~~> namespaceData N a :=
  alloc (h _ (flatten_mem_nclose N)) ha

@[rocq_alias cryptis.namespace_map_disj]
theorem ReservationMap.not_valid_mkToken_op_namespaceData {E : CoPset} {N : Namespace} {a : A}
    (h : ↑N ⊆ E) :
    ¬ ✓ (mkToken (H := H) E • namespaceData N a) :=
  fun hv => not_mem_of_valid_mkToken_singleton hv (h _ (flatten_mem_nclose N))

@[rocq_alias cryptis.namespace_map_data_core_id]
instance ReservationMap.instCoreIdNamespaceData {N : Namespace} {a : A} [ORA.CoreId a] :
    ORA.CoreId (namespaceData (H := H) N a) := by
  unfold namespaceData; infer_instance

end Iris
