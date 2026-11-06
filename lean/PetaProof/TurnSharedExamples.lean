import PetaProof.TurnSharedScc
import PetaProof.SccIndexedExamples

namespace PetaProof.TurnSharedExamples

def view := SccIndexedView.Examples.view
def allow (edge : Fin 7 × Bool) : Bool := SccIndexedView.Examples.allow edge.1
def selective (edge : Fin 7 × Bool) : Bool := allow edge && !(edge.1 == 0 && edge.2)
def oneSelfDirection (edge : Fin 7 × Bool) : Bool := allow edge && !(edge.1 == 4 && edge.2)

theorem numeric_order :
    (TurnEncoding.vertices 3).map (fun state => (state.1.val, state.2)) =
      [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)] := by decide

theorem numeric_round_trip (index : Fin 6) : TurnEncoding.encode (TurnEncoding.decode (n := 3) index) = index :=
  TurnEncoding.encode_decode (n := 3) index

theorem pair_round_trip (state : TurnEncoding.State 3) : TurnEncoding.decode (TurnEncoding.encode state) = state :=
  TurnEncoding.decode_encode state

theorem empty_vertices : TurnEncoding.vertices 0 = [] := by decide

/-- 0↔1の基礎循環は二つの手番別SCCに分かれ、2の自己辺は二状態のSCCになる。 -/
theorem distinct_parity_components :
    (TurnEncoding.vertices 3).map (TurnSharedScc.component view 0 allow) = [2, 1, 1, 2, 0, 0] := by decide

theorem all_states_cyclic :
    (TurnSharedScc.core view 0 allow).map (fun state => (TurnEncoding.encode state).val) = [0, 1, 2, 3, 4, 5] := by decide

theorem turn_sensitive_core :
    (TurnSharedScc.core view 0 selective).map (fun state => (TurnEncoding.encode state).val) = [0, 3, 4, 5] := by decide

theorem parent_turn_is_flipped_before_allow :
    (TurnSharedGraph.parents view 0 selective (1, true)).map (fun state => (TurnEncoding.encode state).val) = [0] ∧
    (TurnSharedGraph.parents view 0 selective (1, false)).map (fun state => (TurnEncoding.encode state).val) = [] := by decide

theorem base_self_edge_is_two_edges :
    (TurnSharedGraph.expanded view).child (4, false) = some (2, true) ∧
    (TurnSharedGraph.expanded view).child (4, true) = some (2, false) := by decide

theorem leaf_does_not_become_internal :
    (TurnSharedGraph.expanded view).child (5, false) = none ∧
    (TurnSharedGraph.expanded view).child (5, true) = none := by decide

theorem one_direction_does_not_make_cycle :
    (TurnSharedScc.core view 0 oneSelfDirection).map (fun state => (TurnEncoding.encode state).val) = [0, 1, 2, 3] := by decide

theorem no_expanded_self_flag (state : TurnEncoding.State 3) :
    TurnSharedGraph.selfLoop view 0 allow state = false :=
  TurnSharedGraph.selfLoop_false view 0 allow state

theorem storage_is_not_doubled :
    (CsrConstructArray.build 3 0 (SccCsrView.target view) (SccCsrView.edges view)).state.memory.size = 5 :=
  TurnSharedScc.shared_storage_capacity view 0

theorem constructed_core_exact (state : TurnEncoding.State 3) :
    state ∈ TurnSharedScc.core view 0 selective ↔
      CyclicVertex (SccIndexedView.relation (TurnSharedGraph.expanded view) selective) state :=
  TurnSharedScc.core_correct view 0 selective state

theorem component_meaning (a b : TurnEncoding.State 3) :
    TurnSharedScc.component view 0 selective a = TurnSharedScc.component view 0 selective b ↔
      ForwardDfs.Mutual (SccIndexedView.outgoing (TurnSharedGraph.expanded view) selective) a b :=
  TurnSharedScc.component_eq_iff view 0 selective a b

theorem numeric_parent :
    (TurnSharedGraph.parents view 0 allow (1, true)).map (fun state => (TurnEncoding.encode state).val) = [0] := by decide

end PetaProof.TurnSharedExamples
