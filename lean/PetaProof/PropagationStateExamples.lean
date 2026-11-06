import PetaProof.PropagationState
import PetaProof.CounterQueueExamples

/-! 全体状態での親間の分離、局所追加、通知完了とFIFOの接続例。 -/
namespace PetaProof.PropagationStateExamples

open ThresholdGame CounterQueueExamples

def start : PropagationState Bool ParentEdge := PropagationState.initial parentIndexed
def leafReady := start.notify parentIndexed .exit
def childTaken := leafReady.pop
def firstNotified := childTaken.notify parentIndexed .first
def bothNotified := firstNotified.notify parentIndexed .second
def finished := bothNotified.pop

theorem leaf_only_changes_its_parent : leafReady.queue.pending = [false] ∧
    (leafReady.counters true).left = 2 ∧ (leafReady.counters true).admitted = false := by decide

theorem first_callback_is_not_completion : firstNotified.queue.pending = [] ∧
    (firstNotified.counters true).left = 1 ∧ (firstNotified.counters true).admitted = false := by decide

theorem second_callback_enqueues_parent : bothNotified.queue.pending = [true] ∧
    (bothNotified.counters true).left = 0 ∧ (bothNotified.counters true).admitted = true := by decide

theorem first_notified_invariant : firstNotified.Invariant parentIndexed := by
  apply PropagationState.notify_preserves parentIndexed childTaken
  · apply PropagationState.pop_preserves
    apply PropagationState.notify_preserves parentIndexed start
    · exact PropagationState.initial_invariant parentIndexed
    · decide
  · decide

def second_callback_safe_batch : parentGame.SafeBatch firstNotified.won
    (fun vertex => vertex = true) := by
  apply PropagationState.new_parent_batch parentIndexed firstNotified first_notified_invariant .second
  · decide
  · change ¬ (firstNotified.counters true).admitted = true
    decide
  · intro edge member _
    change edge ∈ [ParentEdge.first, .second] at member
    cases edge with
    | first => change (firstNotified.counters false).admitted = true; decide
    | second => change (firstNotified.counters false).admitted = true; decide
    | exit => simp at member
  · change (firstNotified.counters false).admitted = true
    decide
  · change (bothNotified.counters true).admitted = true
    decide

theorem finished_run : PropagationState.Run parentIndexed finished := by
  apply PropagationState.Run.pop
  apply PropagationState.Run.notify (edge := ParentEdge.second)
  · apply PropagationState.Run.notify (edge := ParentEdge.first)
    · apply PropagationState.Run.pop
      apply PropagationState.Run.notify (edge := ParentEdge.exit)
      · exact PropagationState.Run.initial
      · decide
    · decide
  · decide

theorem finished_invariant : finished.Invariant parentIndexed := finished_run.invariant parentIndexed

theorem finished_closed : parentGame.OrdinaryClosed finished.won := by
  apply PropagationState.ordinary_closed parentIndexed finished finished_invariant (by decide)
  · intro edge score same _
    cases edge <;> simp_all [parentIndexed, parentMove]
    decide
  · intro child _ edge same
    cases edge <;> simp_all [parentIndexed, parentMove]
    all_goals decide

/-- 局所追加後は、後続hitが確定済み親を無視しても未確定親の不変条件に影響しない。 -/
def earlyAdded := firstNotified.add true
def ignoredCallback := earlyAdded.notify parentIndexed .second

theorem ignored_callback_keeps_fifo_unique : ignoredCallback.queue.pending = [true] ∧
    (ignoredCallback.counters true).left = 1 ∧
    (ignoredCallback.counters true).seen .second = false ∧
    ignoredCallback.notified .second = true := by decide

theorem interleaved_addition_invariant : ignoredCallback.Invariant parentIndexed := by
  apply PropagationState.notify_preserves parentIndexed earlyAdded
  · apply PropagationState.add_preserves parentIndexed firstNotified
    apply PropagationState.notify_preserves parentIndexed childTaken
    · apply PropagationState.pop_preserves
      apply PropagationState.notify_preserves parentIndexed start
      · exact PropagationState.initial_invariant parentIndexed
      · decide
    · decide
  · decide

/-- この検査はaddの機械的不変条件だけを対象とし、任意の追加の値保証を主張しない。 -/
theorem batch_invariant :
    (start.notifyMany parentIndexed [.exit, .first, .second]).Invariant parentIndexed :=
  PropagationState.notifyMany_preserves parentIndexed start
    (PropagationState.initial_invariant parentIndexed) _ (by decide) (by intro e _; rfl)

theorem batch_records_all_edges (edge : ParentEdge) :
    (start.notifyMany parentIndexed [.exit, .first, .second]).notified edge = true := by
  apply (PropagationState.notifyMany_history parentIndexed start _ edge).mpr
  right
  cases edge <;> decide

end PetaProof.PropagationStateExamples
