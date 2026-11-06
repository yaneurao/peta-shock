import PetaProof.OrdinaryClosure
import PetaProof.CertifiedPropagation
import PetaProof.History

/-!
通常FIFOを実際に排出する手続きと、最小通常閉包の一致。
一つの子の全逆辺通知を終えてから次の子を取り出す。通知履歴とfuelは証明用である。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

theorem OrdinaryRun.trans {a b c : V → Prop} (first : G.OrdinaryRun a b)
    (second : G.OrdinaryRun b c) : G.OrdinaryRun a c := by
  induction second with
  | refl => exact first
  | add _ sub ready ih => exact OrdinaryRun.add ih sub ready

/-- 逆辺は子で重複除去せず、元の指し手IDをすべて残す。 -/
structure ParentLists (indexed : G.IndexedMoves E) where
  incoming : V → List E
  unique : ∀ child, (incoming child).Nodup
  exact : ∀ child edge, edge ∈ incoming child ↔ indexed.move edge = .node child

namespace PropagationState

variable [DecidableEq V] [DecidableEq E]

/-- 既に通知済みならスキップする。新しい通知だけがhitカウンターを減らす。 -/
def notifyFresh (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge : E) :
    PropagationState V E := if state.notified edge then state else state.notify indexed edge

def notifyFreshMany (indexed : G.IndexedMoves E) : PropagationState V E → List E → PropagationState V E
  | state, [] => state
  | state, edge :: rest => notifyFreshMany indexed (state.notifyFresh indexed edge) rest

theorem notifyFresh_mono (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge : E) :
    ∀ vertex, state.won vertex → (state.notifyFresh indexed edge).won vertex := by
  cases seen : state.notified edge <;> simp only [notifyFresh, seen, Bool.false_eq_true, ite_false, ite_true]
  · exact won_notify_mono indexed state edge
  · exact fun _ h => h

theorem notifyFresh_history (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge other : E) :
    (state.notifyFresh indexed edge).notified other = true ↔ state.notified other = true ∨ other = edge := by
  cases seen : state.notified edge with
  | false => simp [notifyFresh, seen, notify, markSeen_true_iff, or_comm]
  | true =>
    simp only [notifyFresh, seen, ite_true]
    constructor
    · exact Or.inl
    · rintro (old | same)
      · exact old
      · simpa only [same] using seen

theorem notifyFresh_popped (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge : E) :
    (state.notifyFresh indexed edge).queue.popped = state.queue.popped := by
  cases seen : state.notified edge <;> simp only [notifyFresh, seen, Bool.false_eq_true, ite_false, ite_true]
  · simp only [notify]
    split
    · simp only [AdmissionQueue.admit]
      split <;> rfl
    · rfl

noncomputable def notifyFresh_certificate (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edge : E)
    (good : G.GoodExit state.won (indexed.move edge)) :
    StateCertificate indexed (state.notifyFresh indexed edge) := by
  cases seen : state.notified edge with
  | false => simpa only [notifyFresh, seen, Bool.false_eq_true, ite_false] using
      StateCertificate.notify indexed state certificate edge seen good
  | true => simpa only [notifyFresh, seen, ite_true] using certificate

/-- hitで増える親は、通知直前の集合に対する通常OR/AND条件を満たす。 -/
theorem notify_ordinary (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edge : E) (fresh : state.notified edge = false)
    (good : G.GoodExit state.won (indexed.move edge)) : G.OrdinaryRun state.won (state.notify indexed edge).won := by
  refine OrdinaryRun.add (.refl state.won) (won_notify_mono indexed state edge) ?_
  intro vertex inside outside
  rcases (won_notify_iff indexed state edge vertex).mp inside with old | ⟨same, ready⟩
  · exact False.elim (outside old)
  · subst vertex
    have pending : (state.counters (indexed.source edge)).admitted = false := by
      cases flag : (state.counters (indexed.source edge)).admitted
      · rfl
      · exact False.elim (outside flag)
    apply indexed.hit_ready state.won (indexed.source edge) (state.counters (indexed.source edge)) edge
      (certificate.invariant.counters _) (indexed.at_source edge)
      (fresh_at_parent indexed state certificate.invariant edge fresh pending) pending
    · intro other member seen
      rw [certificate.invariant.history _ pending other member] at seen
      exact certificate.notifications other seen
    · exact good
    · simpa only [won, notify, if_pos rfl] using ready

theorem notifyFresh_ordinary (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edge : E)
    (good : G.GoodExit state.won (indexed.move edge)) : G.OrdinaryRun state.won (state.notifyFresh indexed edge).won := by
  cases seen : state.notified edge with
  | false => simpa only [notifyFresh, seen, Bool.false_eq_true, ite_false] using
      notify_ordinary indexed state certificate edge seen good
  | true => simpa only [notifyFresh, seen, ite_true] using OrdinaryRun.refl (G := G) state.won

theorem notifyFreshMany_mono (indexed : G.IndexedMoves E) (state : PropagationState V E) (edges : List E) :
    ∀ vertex, state.won vertex → (state.notifyFreshMany indexed edges).won vertex := by
  induction edges generalizing state with
  | nil => exact fun _ h => h
  | cons edge rest ih => exact fun vertex inside => ih _ vertex (notifyFresh_mono indexed state edge vertex inside)

theorem notifyFreshMany_history (indexed : G.IndexedMoves E) (state : PropagationState V E) (edges : List E) (other : E) :
    (state.notifyFreshMany indexed edges).notified other = true ↔ state.notified other = true ∨ other ∈ edges := by
  induction edges generalizing state with
  | nil => simp [notifyFreshMany]
  | cons edge rest ih =>
    rw [notifyFreshMany, ih, notifyFresh_history, List.mem_cons]
    simp only [or_assoc]

theorem notifyFreshMany_popped (indexed : G.IndexedMoves E) (state : PropagationState V E) (edges : List E) :
    (state.notifyFreshMany indexed edges).queue.popped = state.queue.popped := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih => rw [notifyFreshMany, ih, notifyFresh_popped]

theorem notifyFreshMany_certified (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edges : List E)
    (good : ∀ edge ∈ edges, G.GoodExit state.won (indexed.move edge)) :
    Nonempty (StateCertificate indexed (state.notifyFreshMany indexed edges)) := by
  induction edges generalizing state with
  | nil => exact ⟨certificate⟩
  | cons edge rest ih =>
    apply ih _ (notifyFresh_certificate indexed state certificate edge (good edge (by simp)))
    intro other member
    exact goodExit_mono (notifyFresh_mono indexed state edge) _ (good other (by simp [member]))

theorem notifyFreshMany_ordinary (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edges : List E)
    (good : ∀ edge ∈ edges, G.GoodExit state.won (indexed.move edge)) :
    G.OrdinaryRun state.won (state.notifyFreshMany indexed edges).won := by
  induction edges generalizing state with
  | nil => exact .refl _
  | cons edge rest ih =>
    have next_certificate := notifyFresh_certificate indexed state certificate edge (good edge (by simp))
    have next_good := fun other member => goodExit_mono (notifyFresh_mono indexed state edge)
      (indexed.move other) (good other (List.mem_cons_of_mem edge member))
    exact (notifyFresh_ordinary indexed state certificate edge (good edge (by simp))).trans
      (ih _ next_certificate next_good)

/-- popした子の逆辺をすべて通知してから、次の子へ移る。 -/
def queueVisit (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (state : PropagationState V E) :
    PropagationState V E := match state.queue.pending with
  | [] => state
  | child :: _ => state.pop.notifyFreshMany indexed (parents.incoming child)

def drainQueue (indexed : G.IndexedMoves E) (parents : ParentLists indexed) : Nat → PropagationState V E → PropagationState V E
  | 0, state => state
  | fuel + 1, state => drainQueue indexed parents fuel (state.queueVisit indexed parents)

omit [DecidableEq V] [DecidableEq E] in
theorem popped_child (state : PropagationState V E) (child : V) (rest : List V)
    (pending : state.queue.pending = child :: rest) : child ∈ state.pop.queue.popped := by
  simp [pop, AdmissionQueue.pop, pending]

theorem queueVisit_certified (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) : Nonempty (StateCertificate indexed (state.queueVisit indexed parents)) := by
  cases pending : state.queue.pending with
  | nil => simpa only [queueVisit, pending] using Nonempty.intro certificate
  | cons child rest =>
    simp only [queueVisit, pending]
    apply notifyFreshMany_certified indexed state.pop (certificate.pop indexed state)
    intro edge member
    exact StateCertificate.node_good indexed state.pop (certificate.pop indexed state) child
      (popped_child state child rest pending) edge ((parents.exact child edge).mp member)

theorem queueVisit_ordinary (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) : G.OrdinaryRun state.won (state.queueVisit indexed parents).won := by
  cases pending : state.queue.pending with
  | nil => simpa only [queueVisit, pending] using OrdinaryRun.refl (G := G) state.won
  | cons child rest =>
    simp only [queueVisit, pending]
    apply notifyFreshMany_ordinary indexed state.pop (certificate.pop indexed state)
    intro edge member
    exact StateCertificate.node_good indexed state.pop (certificate.pop indexed state) child
      (popped_child state child rest pending) edge ((parents.exact child edge).mp member)

theorem drainQueue_certified (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) (certificate : StateCertificate indexed state) :
    Nonempty (StateCertificate indexed (drainQueue indexed parents fuel state)) := by
  induction fuel generalizing state with
  | zero => exact ⟨certificate⟩
  | succ fuel ih =>
    obtain ⟨next⟩ := queueVisit_certified indexed parents state certificate
    exact ih _ next

theorem drainQueue_ordinary (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) (certificate : StateCertificate indexed state) :
    G.OrdinaryRun state.won (drainQueue indexed parents fuel state).won := by
  induction fuel generalizing state with
  | zero => exact .refl _
  | succ fuel ih =>
    obtain ⟨next⟩ := queueVisit_certified indexed parents state certificate
    exact (queueVisit_ordinary indexed parents state certificate).trans (ih _ next)

theorem queueVisit_history_mono (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (state : PropagationState V E) (edge : E) (seen : state.notified edge = true) :
    (state.queueVisit indexed parents).notified edge = true := by
  cases pending : state.queue.pending with
  | nil => simpa only [queueVisit, pending] using seen
  | cons child rest =>
    simp only [queueVisit, pending]
    exact (notifyFreshMany_history indexed state.pop (parents.incoming child) edge).mpr (Or.inl seen)

theorem drainQueue_history_mono (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) (edge : E) (seen : state.notified edge = true) :
    (drainQueue indexed parents fuel state).notified edge = true := by
  induction fuel generalizing state with
  | zero => exact seen
  | succ fuel ih => exact ih _ (queueVisit_history_mono indexed parents state edge seen)

/-- 以前取り出した子の通知が済んでいる、という通常処理の境界条件。 -/
def NodesComplete (indexed : G.IndexedMoves E) (state : PropagationState V E) : Prop :=
  ∀ child ∈ state.queue.popped, ∀ edge, indexed.move edge = .node child → state.notified edge = true

theorem queueVisit_nodes_complete (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (state : PropagationState V E) (complete : NodesComplete indexed state) :
    NodesComplete indexed (state.queueVisit indexed parents) := by
  cases pending : state.queue.pending with
  | nil => simpa only [queueVisit, pending] using complete
  | cons head rest =>
    intro child popped edge same
    simp only [queueVisit, pending, notifyFreshMany_popped] at popped ⊢
    simp only [pop, AdmissionQueue.pop, pending] at popped
    change child ∈ state.queue.popped ++ [head] at popped
    apply (notifyFreshMany_history indexed state.pop (parents.incoming head) edge).mpr
    rcases List.mem_append.mp popped with earlier | latest
    · exact Or.inl (complete child earlier edge same)
    · have equal : child = head := by simpa only [List.mem_singleton] using latest
      subst child
      exact Or.inr ((parents.exact head edge).mpr same)

theorem drainQueue_nodes_complete (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) (complete : NodesComplete indexed state) :
    NodesComplete indexed (drainQueue indexed parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact complete
  | succ fuel ih => exact ih _ (queueVisit_nodes_complete indexed parents state complete)

private theorem unique_count_lt_two (items : List V) (unique : items.Nodup) (vertex : V) : items.count vertex < 2 := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = vertex
    · subst head
      simp [List.count_cons, List.count_eq_zero_of_not_mem parts.1]
    · simpa [List.count_cons, same, Ne.symm same] using ih parts.2

omit [DecidableEq E] in
/-- 同じ頂点を二度投入しないので、取り出し済みと待機中の総数はN以下である。 -/
theorem queue_total_bound (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (state : PropagationState V E) (valid : state.queue.Invariant) : state.queue.total.length ≤ vertices.length := by
  have bound := history_length_bound vertices state.queue.total 2
    (fun vertex _ => covered vertex) (fun vertex _ => unique_count_lt_two _ valid.unique vertex)
  simpa using bound

theorem queueVisit_popped_length (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (state : PropagationState V E) (nonempty : state.queue.pending ≠ []) :
    (state.queueVisit indexed parents).queue.popped.length = state.queue.popped.length + 1 := by
  cases pending : state.queue.pending with
  | nil => exact False.elim (nonempty pending)
  | cons child rest => simp [queueVisit, pending, notifyFreshMany_popped, pop, AdmissionQueue.pop]

theorem drainQueue_empty_fixed (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) (empty : state.queue.pending = []) :
    drainQueue indexed parents fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [drainQueue, queueVisit, empty] using ih

/-- N回のpop予算で必ずキューが空になる。進捗可能性や終了時の空性は仮定しない。 -/
theorem drainQueue_drained (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (fuel : Nat)
    (state : PropagationState V E) (certificate : StateCertificate indexed state)
    (budget : vertices.length ≤ state.queue.popped.length + fuel) :
    (drainQueue indexed parents fuel state).queue.pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := queue_total_bound vertices covered state certificate.invariant.queue
    simp only [AdmissionQueue.total, List.length_append] at bound
    change state.queue.pending = []
    apply List.length_eq_zero_iff.mp
    omega
  | succ fuel ih =>
    by_cases empty : state.queue.pending = []
    · rw [drainQueue_empty_fixed indexed parents (fuel + 1) state empty]
      exact empty
    · obtain ⟨next⟩ := queueVisit_certified indexed parents state certificate
      have growth := queueVisit_popped_length indexed parents state empty
      exact ih _ next (by omega)

/-- 全逆辺を通知する実際の排出手続きは、最小通常閉包と同じ集合を返す。 -/
theorem drainQueue_closure (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (state : PropagationState V E) (certificate : StateCertificate indexed state)
    (leaves : ∀ edge score, indexed.move edge = .leaf score → G.threshold ≤ score → state.notified edge = true)
    (nodes : NodesComplete indexed state) :
    (drainQueue indexed parents vertices.length state).won = G.ordinaryClosure vertices state.won := by
  obtain ⟨final⟩ := drainQueue_certified indexed parents vertices.length state certificate
  have empty := drainQueue_drained indexed parents vertices covered vertices.length state certificate (by omega)
  have complete := drainQueue_nodes_complete indexed parents vertices.length state nodes
  have closed := ordinary_closed indexed _ final.invariant empty
    (fun edge score same good => drainQueue_history_mono indexed parents vertices.length state edge (leaves edge score same good)) complete
  exact OrdinaryRun.closed_result_eq G vertices covered
    (drainQueue_ordinary indexed parents vertices.length state certificate) closed

end PropagationState
end PetaProof.ThresholdGame
