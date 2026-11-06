import PetaProof.LocalCallAccounting
import PetaProof.QueueScanAccountingExamples

/-! 返却が空になる閾値と、王手循環を一度だけ追加する全走査の具体例。 -/
namespace PetaProof.LocalCallAccountingExamples

open ThresholdGame

theorem diamond_two_empty_calls :
    scanLocalCalls QueueScanAccountingExamples.game QueueScanAccountingExamples.context
      QueueScanAccountingExamples.levels QueueScanAccountingExamples.valid
      QueueScanAccountingExamples.context.seeded = [[], []] := by decide

theorem cycle_then_empty :
    QueueThresholdControlExamples.context.localCalls 3 QueueThresholdControlExamples.start =
      [[.other, .own], []] := by decide

def levels : List Int := [10, 5, 1]
theorem valid : ∀ t ∈ levels, 0 < t ∧ t ≤ QueueThresholdControlExamples.game.mate := by
  intro t member
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> subst t <;> decide

def calls := scanLocalCalls QueueThresholdControlExamples.game QueueThresholdControlExamples.context
  levels valid QueueThresholdControlExamples.start

theorem cycle_not_readded : calls = [[.other, .own], [], [], []] := by decide
theorem cycle_added_vertices_once : calls.flatten = [.other, .own] := by decide
theorem cycle_empty_calls : calls.count [] = levels.length := by decide
theorem cycle_nonempty_calls : calls.length - calls.count [] = 1 := by decide
theorem cycle_core_size : QueueThresholdControlExamples.context.coreSize = 2 := by decide

theorem cycle_calls_bounded : calls.length ≤ QueueThresholdControlExamples.context.coreSize + levels.length :=
  QueueThresholdControlExamples.context.scanLocalCalls_bound levels valid QueueThresholdControlExamples.start

theorem zero_fuel_no_local_call :
    QueueThresholdControlExamples.context.localCalls 0 QueueThresholdControlExamples.start = [] := rfl

end PetaProof.LocalCallAccountingExamples
