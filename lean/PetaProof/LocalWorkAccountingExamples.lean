import PetaProof.LocalWorkAccounting
import PetaProof.LocalCallAccountingExamples
import PetaProof.SafetyExecutionExamples

/-! 重複pop、停止後の余剰予算、空返却でも必要な削除作業を検査する。 -/
namespace PetaProof.LocalWorkAccountingExamples

open ThresholdGame

theorem duplicate_pop_is_counted : SafetyExecution.executionWork
    (SafetyExecution.Examples.graph false) 5
    (SafetyExecution.initial (SafetyExecution.Examples.graph false) SafetyExecution.Examples.vertices) = 5 := by decide

theorem stopped_ticks_are_not_work : SafetyExecution.executionWork
    (SafetyExecution.Examples.graph false) 20
    (SafetyExecution.initial (SafetyExecution.Examples.graph false) SafetyExecution.Examples.vertices) = 5 := by decide

theorem or_deletion_work : SafetyExecution.executionWork
    (SafetyExecution.Examples.graph true) 20
    (SafetyExecution.initial (SafetyExecution.Examples.graph true) SafetyExecution.Examples.vertices) = 4 := by decide

theorem safe_cycle_no_deletion_work : QueueThresholdControlExamples.context.localWork
    QueueThresholdControlExamples.start = 0 := by decide

theorem quiet_cycle_requires_three_ticks : QueueThresholdControlExamples.quietContext.localWork
    QueueThresholdControlExamples.quietStart = 3 := by decide

theorem quiet_core_has_two_edges : QueueThresholdControlExamples.quietContext.coreEdges.length = 2 := by decide

def levels : List Int := [10, 5, 1]
theorem valid : ∀ t ∈ levels, 0 < t ∧ t ≤ QueueThresholdControlExamples.quietGame.mate := by
  intro t member
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> subst t <;> decide

theorem empty_returns_still_cost_work : scanLocalWork QueueThresholdControlExamples.quietGame
    QueueThresholdControlExamples.quietContext levels valid QueueThresholdControlExamples.quietStart = 9 := by decide

theorem quiet_work_bounded : scanLocalWork QueueThresholdControlExamples.quietGame
    QueueThresholdControlExamples.quietContext levels valid QueueThresholdControlExamples.quietStart ≤ 30 :=
  QueueThresholdControlExamples.quietContext.scanLocalWork_bound levels valid QueueThresholdControlExamples.quietStart

end PetaProof.LocalWorkAccountingExamples
