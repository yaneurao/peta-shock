import PetaProof.DeletionFifoIndex
import PetaProof.FiniteDeletionExamples

/-! 手書き索引を渡さず、CSRの構築からFIFO検査までを実計算で検査する。 -/
namespace PetaProof.DeletionIndexExamples

open HistoryArena HistoryArena.DeletionInput FiniteDeletionExamples

theorem original_example_labels : fifoTable input.builtIndex = #[some 2, some 1, some 1] := by decide
theorem original_example_success : input.builtCounter.isSome = true := by decide
theorem original_edge_ids : input.reachEdges.length = 5 := by decide
theorem original_capacity : input.reverseStorage.state.memory.size = 5 := by decide
theorem original_goal_incoming : (input.builtIndex.incoming none).length = 3 := by decide
theorem original_positive_incoming : (input.builtIndex.incoming (some 1)).length = 1 := by decide
theorem safe_labels : fifoTable safeInput.builtIndex = #[none] := by decide
theorem safe_rejected : safeInput.builtCounter.isSome = false := by decide

namespace Parallel

def next (v : Fin 2) : List (Fin 2) := if v = 0 then [1, 1] else [0]

def arena : HistoryArena (Fin 2) where
  edge := fun v w => w ∈ next v
  owner := fun v => v != 0
  player := false
  bad := fun v _ => v ≠ 0
  moves_exist := by
    intro v
    by_cases zero : v = 0
    · exact ⟨1, by simp [next, zero]⟩
    · exact ⟨0, by simp [next, zero]⟩

def input : DeletionInput arena where
  next := next
  edges := fun _ _ => Iff.rfl
  bad := fun v _ => v != 0
  bad_correct := by intro v w; simp [arena]

theorem edge_count : input.reachEdges.length = 4 := by decide
theorem outgoing_keeps_both : (input.builtIndex.outgoing (some 0)).length = 2 := by decide
theorem incoming_keeps_both : (input.builtIndex.incoming (some 1)).length = 2 := by decide
theorem labels : fifoTable input.builtIndex = #[some 2, some 1] := by decide
theorem success : input.builtCounter.isSome = true := by decide
theorem distinct_positions : (⟨some 0, ⟨0, by decide⟩⟩ : input.ReachEdge) ≠
    ⟨some 0, ⟨1, by decide⟩⟩ := by decide

end Parallel

namespace Empty

def arena : HistoryArena (Fin 0) where
  edge := fun _ _ => False
  owner := Fin.elim0
  player := false
  bad := fun _ _ => False
  moves_exist := Fin.elim0

def input : DeletionInput arena where
  next := Fin.elim0
  edges := fun v => Fin.elim0 v
  bad := fun _ _ => false
  bad_correct := fun v => Fin.elim0 v

theorem single_goal_id : input.reachEdges.length = 1 := by decide
theorem single_goal_storage : input.reverseStorage.state.memory.size = 1 := by decide
theorem no_original_labels : fifoTable input.builtIndex = #[] := by decide
theorem vacuous_success : input.builtCounter.isSome = true := by decide

end Empty
end PetaProof.DeletionIndexExamples
