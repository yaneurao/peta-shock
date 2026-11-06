import PetaProof.IncrementalThreshold

/-!
キューの未確定頂点に2単位を与える。一度の新規投入で1単位を使い、将来のpop用に1単位を残す。
逆辺は経路ではなく辺IDで数え、分岐・合流による経路列挙は行わない。
-/
namespace PetaProof

universe u
variable {V : Type u} [DecidableEq V]

namespace AdmissionQueue

def workBudget (vertices : List V) (queue : AdmissionQueue V) : Nat :=
  2 * remainingEdges queue.admitted vertices + queue.pending.length

/-- 未確定頂点の投入で、未確定残数が1減り、待機列が1増えるので予算は正確に1減る。 -/
theorem admit_work_fresh (vertices : List V) (unique : vertices.Nodup) (queue : AdmissionQueue V)
    (vertex : V) (member : vertex ∈ vertices) (fresh : queue.admitted vertex = false) :
    workBudget vertices (queue.admit vertex) + 1 = workBudget vertices queue := by
  have decrement := remaining_mark_fresh queue.admitted vertex vertices unique member fresh
  simp only [admit, fresh, Bool.false_eq_true, ite_false, workBudget, List.length_append, List.length_singleton]
  omega

/-- 確定済みガードで無視する投入も予算を増やさない。 -/
theorem admit_work_le (vertices : List V) (unique : vertices.Nodup) (queue : AdmissionQueue V)
    (vertex : V) (member : vertex ∈ vertices) : workBudget vertices (queue.admit vertex) ≤ workBudget vertices queue := by
  cases fresh : queue.admitted vertex with
  | false => have decrease := admit_work_fresh vertices unique queue vertex member fresh; omega
  | true => simp [admit, fresh]

omit [DecidableEq V] in
theorem pop_work (vertices : List V) (queue : AdmissionQueue V) (nonempty : queue.pending ≠ []) :
    workBudget vertices queue.pop + 1 = workBudget vertices queue := by
  cases pending : queue.pending with
  | nil => exact False.elim (nonempty pending)
  | cons vertex rest => simp [pop, pending, workBudget, Nat.add_assoc]

end AdmissionQueue

end PetaProof

namespace PetaProof.ThresholdGame.PropagationState

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

def workBudget (vertices : List V) (edges : List E) (state : PropagationState V E) : Nat :=
  remainingEdges state.notified edges + state.queue.workBudget vertices

theorem notify_work (indexed : G.IndexedMoves E) (vertices : List V) (vertices_unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    (state : PropagationState V E) (edge : E) (member : edge ∈ edges) (fresh : state.notified edge = false) :
    workBudget vertices edges (state.notify indexed edge) + 1 ≤ workBudget vertices edges state := by
  have decrement := remaining_mark_fresh state.notified edge edges edges_unique member fresh
  have queue_bound := AdmissionQueue.admit_work_le vertices vertices_unique state.queue
    (indexed.source edge) (covered _)
  unfold workBudget
  change remainingEdges (markSeen state.notified edge) edges +
    AdmissionQueue.workBudget vertices
      (if (HitCounter.hit (decide (G.owner (indexed.source edge) = G.player))
        (state.counters (indexed.source edge)) edge).admitted then state.queue.admit (indexed.source edge) else state.queue) + 1 ≤ _
  split <;> omega

omit [DecidableEq E] in
theorem add_work (vertices : List V) (unique : vertices.Nodup) (edges : List E)
    (state : PropagationState V E) (vertex : V) (member : vertex ∈ vertices)
    (fresh : state.queue.admitted vertex = false) :
    workBudget vertices edges (state.add vertex) + 1 = workBudget vertices edges state := by
  have decrease := AdmissionQueue.admit_work_fresh vertices unique state.queue vertex member fresh
  change remainingEdges state.notified edges + AdmissionQueue.workBudget vertices (state.queue.admit vertex) + 1 =
    remainingEdges state.notified edges + AdmissionQueue.workBudget vertices state.queue
  omega

omit [DecidableEq E] in
theorem add_work_le (vertices : List V) (unique : vertices.Nodup) (edges : List E)
    (state : PropagationState V E) (vertex : V) (member : vertex ∈ vertices) :
    workBudget vertices edges (state.add vertex) ≤ workBudget vertices edges state := by
  have bound := AdmissionQueue.admit_work_le vertices unique state.queue vertex member
  change remainingEdges state.notified edges + AdmissionQueue.workBudget vertices (state.queue.admit vertex) ≤
    remainingEdges state.notified edges + AdmissionQueue.workBudget vertices state.queue
  omega

omit [DecidableEq E] in
theorem addMany_work_le (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (edges : List E) (state : PropagationState V E) (batch : List V) :
    workBudget vertices edges (state.addMany batch) ≤ workBudget vertices edges state := by
  induction batch generalizing state with
  | nil => exact Nat.le_refl _
  | cons vertex rest ih =>
    exact Nat.le_trans (ih (state.add vertex)) (add_work_le vertices unique edges state vertex (covered vertex))

omit [DecidableEq E] in
/-- 局所安全集合が非空で、未確定頂点だけを含むなら、集合全体の投入で予算は厳密に減る。 -/
theorem addMany_work (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (edges : List E) (state : PropagationState V E) (batch : List V) (nonempty : batch ≠ [])
    (fresh : ∀ vertex ∈ batch, state.queue.admitted vertex = false) :
    workBudget vertices edges (state.addMany batch) + 1 ≤ workBudget vertices edges state := by
  cases batch with
  | nil => exact False.elim (nonempty rfl)
  | cons vertex rest =>
    have first := add_work vertices unique edges state vertex (covered vertex) (fresh vertex (by simp))
    have remaining := addMany_work_le vertices unique covered edges (state.add vertex) rest
    change workBudget vertices edges ((state.add vertex).addMany rest) + 1 ≤ _
    omega

omit [DecidableEq V] [DecidableEq E] in
theorem pop_work (vertices : List V) (edges : List E) (state : PropagationState V E) (nonempty : state.queue.pending ≠ []) :
    workBudget vertices edges state.pop + 1 = workBudget vertices edges state := by
  have decrease := AdmissionQueue.pop_work vertices state.queue nonempty
  change remainingEdges state.notified edges + AdmissionQueue.workBudget vertices state.queue.pop + 1 =
    remainingEdges state.notified edges + AdmissionQueue.workBudget vertices state.queue
  omega

omit [DecidableEq V] [DecidableEq E] in
theorem initial_work (indexed : G.IndexedMoves E) (vertices : List V) (edges : List E) :
    workBudget vertices edges (initial indexed) = edges.length + 2 * vertices.length := by
  simp [workBudget, initial, AdmissionQueue.workBudget, AdmissionQueue.initial, remaining_initial]

end PetaProof.ThresholdGame.PropagationState
