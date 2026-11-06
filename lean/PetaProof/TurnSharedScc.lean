import PetaProof.TurnSharedGraph

/-!
基礎CSRを共有する二状態グラフの両DFS、SCC分割と循環core。
根の列は2*基礎番号+手番の昇順をdecodeしたもので、逆辺だけを共有する。
-/
namespace PetaProof.TurnSharedScc

universe u
variable {n : Nat} {E : Type u}
open SccIndexedView
open TurnEncoding (State vertices vertices_unique vertices_cover)
open TurnSharedGraph (expanded parents selfLoop)

def component (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) : State n → Nat :=
  ComponentNumbering.component (vertices n)
    (ForwardDfs.order (vertices n) (vertices n) (outgoing (expanded view) allow)) (parents view seed allow)

def partition (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) :
    SccPartition (ForwardDfs.Edge (outgoing (expanded view) allow)) :=
  KosarajuStep.computedPartition _ (vertices_unique n) (vertices_cover n) _ (vertices_cover n)
    _ _ (TurnSharedGraph.parents_transpose view seed allow)

theorem component_eq_iff (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (a b : State n) :
    component view seed allow a = component view seed allow b ↔ ForwardDfs.Mutual (outgoing (expanded view) allow) a b :=
  KosarajuStep.component_eq_iff_mutual _ (vertices_unique n) (vertices_cover n) _ (vertices_cover n)
    _ _ (TurnSharedGraph.parents_transpose view seed allow) a b

theorem component_bound (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) :
    component view seed allow state < 2 * n := by
  let out := outgoing (expanded view) allow
  have covered := ForwardDfs.order_covers (vertices n) (vertices_unique n) (vertices_cover n)
    (vertices n) (vertices_cover n) out
  have bound := ComponentNumbering.component_bound (vertices n) (vertices_unique n) (vertices_cover n)
    (ForwardDfs.order (vertices n) (vertices n) out) covered
    (parents view seed allow) state
  simpa only [component, TurnEncoding.vertices_length] using bound

def core (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) : List (State n) :=
  CoreEnumeration.core
    (ComponentCycleFlags.keep (vertices n) (component view seed allow) (selfLoop view seed allow)) (vertices n)

theorem core_correct (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) :
    state ∈ core view seed allow ↔ CyclicVertex (relation (expanded view) allow) state := by
  have actual := KosarajuStep.computed_core_correct _ (vertices_unique n) (vertices_cover n) _ (vertices_cover n)
    _ _ (TurnSharedGraph.parents_transpose view seed allow) _ (TurnSharedGraph.selfLoop_correct view seed allow) state
  exact actual.trans (SccIndexedView.cyclic_relation (expanded view) allow state)

/-- 訪問状態は2*n個だが、辺格納は基礎CSRの内部辺数だけである。 -/
theorem shared_storage_capacity (view : View (Fin n) E) (seed : E) :
    (CsrConstructArray.build n seed (SccCsrView.target view) (SccCsrView.edges view)).state.memory.size =
      (SccCsrView.edges view).length := by
  have bounded : ∀ edge ∈ SccCsrView.edges view, SccCsrView.target view edge < n :=
    fun edge _ => (SccIndexedView.target view edge).isLt
  rw [CsrConstructArray.build_exact n seed _ _ bounded]
  exact (CsrPayloadArray.built_sizes n seed _ _ bounded).2

theorem construction_safe (view : View (Fin n) E) (seed : E) :
    CsrConstructArray.Safe n seed (SccCsrView.target view) (SccCsrView.edges view) :=
  SccConstructedView.construction_safe view seed

theorem parent_number (view : View (Fin n) E) (edge : E) (child_turn : Bool) :
    (TurnEncoding.encode ((expanded view).source (edge, !child_turn))).val =
      2 * (view.source edge).val + (1 - TurnEncoding.bit child_turn) :=
  TurnEncoding.encode_flip (view.source edge) child_turn

/-- /2と下位bitによる復元に対し、本番と同じ親番号の算式を得る（自然数版）。 -/
theorem parent_number_from_index (view : View (Fin n) E) (edge : E) (index : Fin (2 * n)) :
    (TurnEncoding.encode ((expanded view).source (edge, !(TurnEncoding.decode index).2))).val =
      2 * (view.source edge).val + (1 - (index.val &&& 1)) := by
  rw [parent_number, TurnEncoding.decode_bit, Nat.and_one_is_mod]

theorem child_number_from_index (view : View (Fin n) E) (edge : E) (index : Fin (2 * n))
    (child : Fin n) (found : view.child edge = some child) :
    ((expanded view).child (edge, (TurnEncoding.decode index).2)).map
        (fun state => (TurnEncoding.encode state).val) =
      some (2 * child.val + (1 - (index.val &&& 1))) := by
  simp only [expanded, found, Option.map_some]
  change some (TurnEncoding.encode (child, !(TurnEncoding.decode index).2)).val =
    some (2 * child.val + (1 - (index.val &&& 1)))
  rw [TurnEncoding.encode_flip, TurnEncoding.decode_bit, Nat.and_one_is_mod]

end PetaProof.TurnSharedScc
