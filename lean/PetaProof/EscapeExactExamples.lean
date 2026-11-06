import PetaProof.EscapeChoices
import PetaProof.EscapeSoundExamples

/-! 最終表の評価による受理を仮定せず、一般定理から実FIFOの正しさと候補を得る。 -/
namespace PetaProof.EscapeExactExamples

abbrev indexed := EscapePropagationExamples.Trap.indexed
def goals : List EscapeExamples.Node := [.exit]
theorem goals_correct (vertex : EscapeExamples.Node) : vertex = .exit ↔ vertex ∈ goals := by simp [goals]

theorem output_exact (vertex : EscapeExamples.Node) :
    EscapePropagation.State.runLabels indexed goals EscapeExamples.vertices vertex =
      EscapeExamples.exitInput.computedDistance EscapeExamples.vertices.length vertex :=
  EscapePropagation.State.runLabels_reference indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered EscapeExamples.exitInput vertex

theorem accepted_without_output_assumption :
    EscapeExamples.exitInput.tableCheck (EscapePropagation.State.runLabels indexed goals EscapeExamples.vertices)
      EscapeExamples.vertices = true :=
  EscapePropagation.State.runLabels_checked indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered EscapeExamples.exitInput

theorem a_is_three : EscapePropagation.State.runLabels indexed goals EscapeExamples.vertices .a = some 3 := by
  rw [output_exact]
  decide

theorem a_full_minimax :
    (∃ strategy : EscapeExamples.arena.Strategy,
      EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy [] 3 .a) ∧
    ∀ strategy : EscapeExamples.arena.Strategy, ∀ past earlier, earlier < 3 →
      ¬ EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy past earlier .a :=
  EscapePropagation.State.runLabels_minimax indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered .a 3 a_is_three

theorem minimizing_ties : EscapePropagation.State.minimizingFlag indexed goals EscapeExamples.vertices .a .c = true ∧
    EscapePropagation.State.minimizingFlag indexed goals EscapeExamples.vertices .a .f = true ∧
    EscapePropagation.State.minimizingFlag indexed goals EscapeExamples.vertices .a .b = false := by decide

theorem chosen_child : EscapePropagation.State.nextChild indexed goals EscapeExamples.vertices .a = some .c := by decide

end PetaProof.EscapeExactExamples
