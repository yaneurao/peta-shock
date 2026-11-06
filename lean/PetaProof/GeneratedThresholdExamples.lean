import PetaProof.GeneratedThresholds
import PetaProof.MainRunAccountingExamples

/-! 重複・非正・範囲外leaf、leaf不在の上限維持、反対視点を検査する。 -/
namespace PetaProof.GeneratedThresholdExamples

open ThresholdGame

def scores : List (Option Int) := [some 20, some 20, some 40, none, some 0, some (-3), some 41]
def marks := PositiveLeafMarks.flags id 40 scores

theorem finite_marks : marks.size = 41 ∧ marks[20]? = some true ∧ marks[40]? = some true ∧
    marks[0]? = some false ∧ marks[41]? = none := by decide

theorem duplicate_scores_one_level : processedLevels 40 (fun level => (marks[level.toNat]?).getD false) = [40, 20] := by decide

theorem no_leaf_still_keeps_top : processedLevels 5
    (fun level => ((PositiveLeafMarks.flags id 5 ([none, none] : List (Option Int)))[level.toNat]?).getD false) = [5] := by decide

theorem input_edges_generate_levels : QueueThresholdScanExamples.context.generatedLevels = [40, 30, 20] := by decide

theorem opposite_levels_only_top : (QueueThresholdScanExamples.context.opposite (fun _ => false)).generatedLevels = [40] := by decide

theorem two_leaf_schedule_work : QueueThresholdScanExamples.context.scheduleGenerationWork = 292 := by decide

theorem two_leaf_schedule_bound : QueueThresholdScanExamples.context.scheduleGenerationWork ≤ 336 :=
  QueueThresholdScanExamples.context.scheduleGenerationWork_bound

theorem generated_value_twenty : QueueThresholdScanExamples.context.generatedPositiveValues () = 20 := by
  change QueueThresholdScanExamples.context.positiveStreamingValues QueueThresholdScanExamples.criticalLevels
    (fun t member => ⟨(QueueThresholdScanExamples.critical_valid t member).1,
      (QueueThresholdScanExamples.critical_valid t member).2.1⟩) () = 20
  rw [QueueThresholdScanExamples.context.positiveStreamingValues_eq _ _ (by decide)]
  decide

end PetaProof.GeneratedThresholdExamples
