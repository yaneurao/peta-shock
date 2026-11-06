import PetaProof.SafetyExecutionTermination
import PetaProof.SafetyCounterExamples

namespace PetaProof.SafetyExecution.Examples

open SafetyCounter.Examples (Edge pair initialBad)

def vertices : List Bool := [false, true]
def view (v : Bool) : SafetyCounter.View Edge := if v then pair else initialBad
def source : Edge → Bool
  | .first | .second => true
  | .exit | .bad => false

/-- 二本の内部辺は、同じ親から同じ子へ向かう別々の辺ID。 -/
def graph (parentOwn : Bool) : Graph Bool Edge := {
  view := view
  own := fun v => if v then parentOwn else false
  eligible := fun _ => true
  source := source
  target := fun _ => false
  source_of_mem := by intro v e h; cases v <;> cases e <;> simp_all [view, pair, initialBad, source]
  source_eligible := by simp
  target_eligible := by simp
  incoming := fun v => if v then [] else [.first, .second]
  incoming_unique := by intro v; cases v <;> decide
  incoming_spec := by intro v e; cases v <;> cases e <;> simp [view, pair, initialBad, source]
}

def state (own : Bool) : Nat → State Bool Edge
  | 0 => initial (graph own) vertices
  | n + 1 => tick (graph own) (state own n)

theorem and_duplicate_queue : (state false 3).pending = [true, true] := by decide
theorem and_countdown : ((state false 1).counters true).count = 2 ∧
    ((state false 2).counters true).count = 1 ∧ ((state false 3).counters true).count = 0 := by decide
theorem notify_before_parent_pop : (state false 2).pending = [true] ∧
    (state false 3).deleted true = false ∧ (state false 3).work = [] := by decide

theorem and_run : Run (graph false) (initial (graph false) vertices) 5 (state false 5) :=
  Run.next (Run.next (Run.next (Run.next (Run.next (Run.done _)))))

theorem and_stopped : Stopped (state false 5) := by constructor <;> decide
theorem and_all_deleted : (state false 5).deleted false = true ∧ (state false 5).deleted true = true := by decide
theorem duplicate_pop_changes_no_counter : (state false 4).counters true = (state false 5).counters true := rfl

theorem and_final_invariant : Invariant (graph false) (state false 5) :=
  and_run.invariant _ (initial_invariant _ vertices (by intro v; cases v <;> simp [vertices]))

theorem and_final_safe : (graph false).SafeSet (alive (state false 5)) :=
  halted_safe _ _ and_final_invariant and_stopped.1 and_stopped.2

theorem and_exact_budget : budget (graph false) vertices (state false 0) = 5 ∧
    budget (graph false) vertices (state false 1) = 4 ∧
    budget (graph false) vertices (state false 2) = 3 ∧
    budget (graph false) vertices (state false 3) = 2 ∧
    budget (graph false) vertices (state false 4) = 1 ∧
    budget (graph false) vertices (state false 5) = 0 := by decide

theorem or_only_last_enqueues : (state true 2).pending = [] ∧ (state true 3).pending = [true] := by decide
theorem or_run : Run (graph true) (initial (graph true) vertices) 4 (state true 4) :=
  Run.next (Run.next (Run.next (Run.next (Run.done _))))
theorem or_stopped : Stopped (state true 4) := by constructor <;> decide

def loopView (seed : Bool) : SafetyCounter.View Bool := {
  good := []
  internal := [false]
  bad := if seed then [true] else []
  internal_unique := by decide
  internal_not_good := by simp
  bad_disjoint := by intro e h; cases seed <;> cases e <;> simp_all
}

/-- 自己辺への通知は、親自身が削除済みなのでcountを触らず読み飛ばす。 -/
def loopGraph (seed : Bool) : Graph Unit Bool := {
  view := fun _ => loopView seed
  own := fun _ => false
  eligible := fun _ => true
  source := fun _ => ()
  target := fun _ => ()
  source_of_mem := by simp
  source_eligible := by simp
  target_eligible := by simp
  incoming := fun _ => [false]
  incoming_unique := by intro vertex; decide
  incoming_spec := by intro v e; cases v; simp [loopView]
}

def loopStart (seed : Bool) := initial (loopGraph seed) [()]
def loopFinish := tick (loopGraph true) (tick (loopGraph true) (loopStart true))

theorem self_edge_skipped : Stopped loopFinish ∧ (loopFinish.counters ()).count = 1 ∧
    loopFinish.handled false = true := by
  constructor
  · constructor <;> decide
  · constructor <;> decide

theorem self_run : Run (loopGraph true) (loopStart true) 2 loopFinish :=
  Run.next (Run.next (Run.done _))

theorem self_final_invariant : Invariant (loopGraph true) loopFinish :=
  self_run.invariant _ (initial_invariant _ [()] (by intro v; cases v; simp))

theorem unseeded_loop_survives : Stopped (loopStart false) ∧ alive (loopStart false) () := by
  constructor
  · constructor <;> decide
  · rfl

theorem unseeded_loop_safe : (loopGraph false).SafeSet (alive (loopStart false)) :=
  halted_safe _ _ (initial_invariant _ [()] (by intro v; cases v; simp))
    unseeded_loop_survives.1.1 unseeded_loop_survives.1.2

end PetaProof.SafetyExecution.Examples
