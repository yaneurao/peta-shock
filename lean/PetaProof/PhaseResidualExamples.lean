import PetaProof.PhaseResidual
import PetaProof.SharedWitnessExamples

/-! 実phaseから有限残余・CSR・FIFO・元の吸収反証へ至る経路を数値計算で検査する。 -/
namespace PetaProof.PhaseResidualExamples

open ThresholdGame ThresholdGame.QueueContext HistoryArena.DeletionInput
open SharedWitnessExamples.TwoLeaves

set_option maxRecDepth 8192

def highResidual := context.phaseResidualInput context.seeded ⟨context.seeded_certificate⟩
  context.seeded_boundary own_core 40 (by decide) (by decide)

def lowResidual := context.phaseResidualInput context.seeded ⟨context.seeded_certificate⟩
  context.seeded_boundary own_core 20 (by decide) (by decide)

theorem high_labels : fifoTable highResidual.builtIndex = #[some 2, some 2, some 1, some 1] := by decide
theorem low_labels : fifoTable lowResidual.builtIndex = #[some 1, some 2, some 1, some 1] := by decide
theorem high_success : highResidual.builtCounter.isSome = true := by decide
theorem low_success : lowResidual.builtCounter.isSome = true := by decide
theorem high_count : highResidual.reachEdges.length = 5 := by decide
theorem low_count : lowResidual.reachEdges.length = 5 := by decide
theorem bad_leaf_preserved : lowResidual.next 1 = [3] := by decide
theorem won_node_dummy : lowResidual.next 0 = [0] := by decide
theorem success_dummy : lowResidual.next 2 = [2] := by decide
theorem failure_preserved : lowResidual.next 3 = [3] := by decide

def originalHigh := context.phaseOriginalCounter context.seeded ⟨context.seeded_certificate⟩
  context.seeded_boundary own_core 40 (by decide) (by decide)

theorem original_rank : originalHigh.ranking.rank ⟨.node 0, by
    change ¬ ((context.phase 40 (by decide) (by decide) context.seeded).counters 0).admitted = true
    decide⟩ = 2 := by decide
theorem original_failure_rank : originalHigh.ranking.rank ⟨.failure, by simp [extendWon]⟩ = 1 := by decide
theorem original_response_failure :
    (match (originalHigh.response ⟨.node 1, by
      change ¬ ((context.phase 40 (by decide) (by decide) context.seeded).counters 1).admitted = true
      decide⟩).val with | .failure => true | _ => false) = true := by decide

theorem low_excluded_node_not_winning :
    ¬ (game.retune 20 (by decide) (by decide)).FourfoldWinning 1 :=
  context.phaseOriginal_refutes context.seeded ⟨context.seeded_certificate⟩ context.seeded_boundary own_core
    20 (by decide) (by decide) 1 (by
      change ¬ ((context.phase 20 (by decide) (by decide) context.seeded).counters 1).admitted = true
      decide)

end PetaProof.PhaseResidualExamples
