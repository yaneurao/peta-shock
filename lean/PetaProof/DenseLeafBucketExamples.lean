import PetaProof.DenseLeafBuckets
import PetaProof.LeafBucketScanExamples

/-! 等しい開始閾値・整数配列の添字・未到達値・全走査の一致を検査する。 -/
namespace PetaProof.DenseLeafBucketExamples

open ThresholdGame

theorem monotone_sweep : ThresholdKeys.sweep 0 [40, 40, 30, 20, 10] [50, 40, 35, 30, 25, 20, 15, 10, 5, 0] =
    [(50, some 0), (40, some 0), (35, some 2), (30, some 2), (25, some 3),
      (20, some 3), (15, some 4), (10, some 4), (5, none), (0, none)] := by simp [ThresholdKeys.sweep]

theorem sweep_comparisons : ThresholdKeys.comparisons [40, 40, 30, 20, 10] [50, 40, 35, 30, 25, 20, 15, 10, 5, 0] = 13 := by simp [ThresholdKeys.comparisons]

theorem range_descends : ThresholdKeys.scoreRange 3 4 = [3, 2, 1, 0] := by decide

theorem dense_integer_index : (ThresholdKeys.dense [40, 40, 30, 20, 10] 40 41)[10]'(by rw [ThresholdKeys.dense_size]; decide) = some 2 := by
  rw [ThresholdKeys.dense_at _ _ _ 10 (by decide)]
  decide

theorem dense_bottom_is_none : (ThresholdKeys.dense [40, 40, 30, 20, 10] 40 41)[40]'(by rw [ThresholdKeys.dense_size]; decide) = none := by
  rw [ThresholdKeys.dense_at _ _ _ 40 (by decide)]
  decide

theorem valid : ∀ t ∈ ([40, 30, 20, 10] : List Int), 0 < t ∧ t ≤ QueueThresholdScanExamples.game.mate := by
  intro t member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same <;> subst t <;> decide

theorem dense_batches_match : QueueThresholdScanExamples.top.denseLeafBatches [40, 30, 20, 10] =
    [[], [], [false], [true], []] := by
  rw [QueueThresholdScanExamples.top.denseLeafBatches_eq _ valid]
  decide

theorem direct_keys :
    QueueThresholdScanExamples.top.directKey (QueueThresholdScanExamples.top.scoreKeyTable [40, 30, 20, 10]) false = some 2 ∧
    QueueThresholdScanExamples.top.directKey (QueueThresholdScanExamples.top.scoreKeyTable [40, 30, 20, 10]) true = some 3 := by
  simp only [QueueThresholdScanExamples.top.directKey_correct _ valid]
  decide

theorem array_key_work_ten : QueueThresholdScanExamples.top.inputKeyWork
    (QueueThresholdScanExamples.top.scoreKeyTable [40, 30, 20, 10]) QueueThresholdScanExamples.top.allEdges = 10 := by
  change QueueThresholdScanExamples.top.directKeyWork (QueueThresholdScanExamples.top.scoreKeyTable [40, 30, 20, 10]) false +
    (QueueThresholdScanExamples.top.directKeyWork (QueueThresholdScanExamples.top.scoreKeyTable [40, 30, 20, 10]) true + 0) = 10
  simp [QueueContext.directKeyWork, QueueContext.scoreKeyTable, ThresholdKeys.dense_size,
    QueueThresholdScanExamples.top, QueueThresholdScanExamples.context, QueueContext.atLevel,
    QueueThresholdScanExamples.indexed, QueueThresholdScanExamples.move, QueueThresholdScanExamples.game, ThresholdGame.retune]

theorem full_dense_scan_unchanged :
    let ctx := QueueScanAccountingExamples.context
    let levels := QueueScanAccountingExamples.levels
    let batches := ctx.denseLeafBatches levels
    scanFromBatches QueueScanAccountingExamples.game ctx levels QueueScanAccountingExamples.valid batches.tail
      ((PropagationState.initial ctx.indexed).notifyMany ctx.indexed (batches.headD [])) (fun _ => 0) =
      scanQueues QueueScanAccountingExamples.game ctx levels QueueScanAccountingExamples.valid ctx.seeded (fun _ => 0) :=
  denseBucketedScan_eq _ _ _ _ (by decide) (by
    intro t member
    simp only [QueueScanAccountingExamples.levels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst t <;> decide) _

end PetaProof.DenseLeafBucketExamples
