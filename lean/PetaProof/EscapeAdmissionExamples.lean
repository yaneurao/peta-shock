import PetaProof.EscapeNone
import PetaProof.EscapePropagationExamples

/-! 一般の初期化を使った空目標・重複目標・有限/無限循環の回帰例。 -/
namespace PetaProof.EscapeAdmissionExamples

open EscapePropagationExamples
open EscapeFifoExamples (Node vertices input)

theorem empty_start : EscapePropagation.State.start indexed ([] : List Node) = none := rfl

theorem duplicate_goals_are_unique : (EscapeFifo.seeded [Node.goal, .goal]).pending = [(Node.goal, 0)] := rfl

theorem repeated_goal_table_accepted :
    input.tableCheck (EscapePropagation.State.runLabels indexed [Node.goal, .goal] vertices) vertices = true := by decide

theorem repeated_goal_exact (vertex : Node) :
    EscapePropagation.State.runLabels indexed [Node.goal, .goal] vertices vertex = input.computedDistance vertices.length vertex :=
  input.checked_exact _ vertices EscapeFifoExamples.covered repeated_goal_table_accepted vertex

theorem target_zero_from_general_run :
    EscapePropagation.State.runLabels indexed [Node.goal, .goal] vertices .goal = some 0 :=
  EscapePropagation.State.runLabels_goal_zero indexed _ _ _ (by simp)

namespace Trap
abbrev trapIndexed := EscapePropagationExamples.Trap.indexed

theorem table_accepted :
    EscapeExamples.exitInput.tableCheck
      (EscapePropagation.State.runLabels trapIndexed [EscapeExamples.Node.exit] EscapeExamples.vertices)
      EscapeExamples.vertices = true := by decide

theorem whole_table_exact (vertex : EscapeExamples.Node) :
    EscapePropagation.State.runLabels trapIndexed [EscapeExamples.Node.exit] EscapeExamples.vertices vertex =
      EscapeExamples.exitInput.computedDistance EscapeExamples.vertices.length vertex :=
  EscapeExamples.exitInput.checked_exact _ EscapeExamples.vertices EscapeExamples.covered table_accepted vertex

/-- 未確定自分番Uの子Tも未確定であることを、一般の停止定理から得る。 -/
theorem unresolved_child_from_general_run :
    EscapePropagation.State.runLabels trapIndexed [EscapeExamples.Node.exit] EscapeExamples.vertices .t = none := by
  have child := EscapePropagation.State.runLabels_own_infinite trapIndexed [EscapeExamples.Node.exit]
    EscapeExamples.vertices EscapeExamples.covered .u (by decide) (by decide) (11 : Fin 13) (by decide)
  exact child

def noGoalInput : HistoryArena.EscapeInput EscapeExamples.arena (fun _ => False) where
  successors := EscapeExamples.successors
  edges := fun _ _ => Iff.rfl
  goal := fun _ => false
  goal_correct := by intro vertex; simp

theorem empty_goals_exact (vertex : EscapeExamples.Node) :
    EscapePropagation.State.runLabels trapIndexed [] EscapeExamples.vertices vertex =
      noGoalInput.computedDistance EscapeExamples.vertices.length vertex := by
  have empty := HistoryArena.empty_target_exact noGoalInput (fun _ impossible => impossible)
    EscapeExamples.vertices EscapeExamples.covered vertex
  rw [empty]
  rfl

theorem arena_matches : EscapePropagation.ArenaMatch trapIndexed EscapeExamples.arena := by
  constructor
  · intro vertex child
    change child ∈ EscapeExamples.successors vertex ↔ ∃ edge : Fin 13,
      edge ∈ EscapePropagationExamples.Trap.outgoing vertex ∧ EscapePropagationExamples.Trap.child edge = child
    cases vertex <;> cases child <;> decide
  · intro vertex
    cases vertex <;> decide

theorem no_strategy_escapes_trap (strategy : EscapeExamples.arena.Strategy)
    (past : List EscapeExamples.Node) (bound : Nat) :
    ¬ EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy past bound .t :=
  EscapePropagation.State.runLabels_none_no_guarantee trapIndexed arena_matches
    [EscapeExamples.Node.exit] EscapeExamples.vertices (by intro vertex; simp) EscapeExamples.covered .t
    (by decide) strategy past bound

end Trap
end PetaProof.EscapeAdmissionExamples
