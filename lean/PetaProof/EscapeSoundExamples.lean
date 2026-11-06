import PetaProof.EscapeSound
import PetaProof.EscapeAdmissionExamples

/-! 一般初期化と実FIFOの有限結果から、戦略の存在と到達可能性の完全一致へ接続する。 -/
namespace PetaProof.EscapeSoundExamples

abbrev indexed := EscapePropagationExamples.Trap.indexed
def goals : List EscapeExamples.Node := [.exit]

theorem goals_correct (vertex : EscapeExamples.Node) : vertex = .exit ↔ vertex ∈ goals := by simp [goals]

theorem a_guarantees_three : ∃ strategy : EscapeExamples.arena.Strategy,
    EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy [] 3 .a :=
  (EscapePropagation.State.runLabels_guarantees indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered .a 3 (by decide)).2

theorem b_guarantees_four : ∃ strategy : EscapeExamples.arena.Strategy,
    EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy [] 4 .b :=
  (EscapePropagation.State.runLabels_guarantees indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered .b 4 (by decide)).2

theorem complete_winning_classification (vertex : EscapeExamples.Node) :
    (∃ distance, EscapePropagation.State.runLabels indexed goals EscapeExamples.vertices vertex = some distance) ↔
      ∃ strategy : EscapeExamples.arena.Strategy, ∃ bound,
        EscapeExamples.arena.escapeWithin (fun vertex => vertex = .exit) strategy [] bound vertex :=
  EscapePropagation.State.runLabels_finite_iff_guarantee indexed EscapeAdmissionExamples.Trap.arena_matches
    goals EscapeExamples.vertices goals_correct EscapeExamples.covered vertex

theorem no_finite_result_in_trap :
    ¬ ∃ distance, EscapePropagation.State.runLabels indexed goals EscapeExamples.vertices .t = some distance := by
  intro finite
  obtain ⟨strategy, bound, guarantee⟩ := (complete_winning_classification .t).mp finite
  exact EscapeAdmissionExamples.Trap.no_strategy_escapes_trap strategy [] bound guarantee

end PetaProof.EscapeSoundExamples
