import PetaProof.LocalPreparationAccounting
import PetaProof.LocalWorkAccountingExamples

/-! core外の祖先を準備走査から除外し、空返却でも準備費用が残ることを検査する。 -/
namespace PetaProof.LocalPreparationAccountingExamples

open ThresholdGame

theorem cycle_core_only : QueueThresholdControlExamples.context.coreVertices = [.other, .own] := by decide

theorem quiet_classifies_two_edges : (QueueThresholdControlExamples.quietContext.classificationEdges
    QueueThresholdControlExamples.quietStart).length = 2 := by decide

theorem quiet_registers_one_internal_edge :
    (SafetyClassification.allInternal
      (QueueThresholdControlExamples.quietContext.localInput QueueThresholdControlExamples.quietStart)
      QueueThresholdControlExamples.quietContext.coreVertices).length = 1 := by decide

theorem quiet_preparation_and_deletion_cost_ten : QueueThresholdControlExamples.quietContext.preparedLocalWork
    QueueThresholdControlExamples.quietStart = 10 := by decide

theorem safe_cycle_preparation_not_free : QueueThresholdControlExamples.context.preparedLocalWork
    QueueThresholdControlExamples.start = 8 := by decide

theorem quiet_three_levels_cost_thirty : scanPreparedWork QueueThresholdControlExamples.quietGame
    QueueThresholdControlExamples.quietContext LocalWorkAccountingExamples.levels LocalWorkAccountingExamples.valid
    QueueThresholdControlExamples.quietStart = 30 := by decide

theorem cycle_full_events_twenty_eight : QueueThresholdControlExamples.context.preparedPropagationWork
    LocalCallAccountingExamples.levels LocalCallAccountingExamples.valid = 28 := by decide

theorem no_core_preparation_zero : QueueScanAccountingExamples.context.preparedLocalWork
    QueueScanAccountingExamples.context.seeded = 0 := by decide

theorem no_core_only_ordinary_work : QueueScanAccountingExamples.context.preparedPropagationWork
    QueueScanAccountingExamples.levels QueueScanAccountingExamples.valid = 9 := by decide

theorem cycle_full_bound : QueueThresholdControlExamples.context.preparedPropagationWork
    LocalCallAccountingExamples.levels LocalCallAccountingExamples.valid ≤ 78 :=
  QueueThresholdControlExamples.context.preparedPropagationWork_bound
    LocalCallAccountingExamples.levels LocalCallAccountingExamples.valid (by decide)
    (by intro t member; simp only [LocalCallAccountingExamples.levels, List.mem_cons, List.not_mem_nil, or_false]
          at member
        rcases member with same | same | same <;> subst t <;> decide)

end PetaProof.LocalPreparationAccountingExamples
