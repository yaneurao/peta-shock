import PetaProof.LeafBucketScan
import PetaProof.QueueScanAccountingExamples

/-! 閾値の等号、疎な帯、順序保持、対象外leafと内部辺の除外を検査する。 -/
namespace PetaProof.LeafBucketScanExamples

open ThresholdGame

theorem top_four_levels : QueueThresholdScanExamples.top.leafBatches [40, 30, 20, 10] =
    [[], [], [false], [true], []] := by decide

theorem initial_equal_and_empty_band : QueueThresholdScanExamples.context.leafBatches [30, 20, 10] =
    [[false], [], [true], []] := by decide

theorem sparse_band_preserves_order : QueueThresholdScanExamples.top.leafBatches [40, 10] =
    [[], [], [false, true]] := by decide

theorem leaf_below_final_threshold_discarded : QueueThresholdScanExamples.top.leafBatches [40, 25] =
    [[], [], [false]] := by decide

theorem internal_edges_not_registered : QueueScanAccountingExamples.context.leafBatches
    QueueScanAccountingExamples.levels = [[], [], [.exit]] := by decide

theorem only_one_registration : StableBuckets.registrations
    (StableBuckets.route (QueueScanAccountingExamples.context.leafSelectors QueueScanAccountingExamples.levels))
    QueueScanAccountingExamples.context.allEdges = 1 := by decide

theorem bucket_notification_bound :
    (QueueScanAccountingExamples.context.leafBatches QueueScanAccountingExamples.levels).flatten.length ≤ 5 :=
  QueueScanAccountingExamples.context.leafBatches_notifications_bound QueueScanAccountingExamples.levels
    QueueScanAccountingExamples.valid (by decide) (by
      intro t member
      simp only [QueueScanAccountingExamples.levels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst t <;> decide)

theorem full_state_and_values_unchanged :
    let ctx := QueueScanAccountingExamples.context
    let levels := QueueScanAccountingExamples.levels
    let batches := ctx.leafBatches levels
    scanFromBatches QueueScanAccountingExamples.game ctx levels QueueScanAccountingExamples.valid batches.tail
      ((PropagationState.initial ctx.indexed).notifyMany ctx.indexed (batches.headD [])) (fun _ => 0) =
      scanQueues QueueScanAccountingExamples.game ctx levels QueueScanAccountingExamples.valid ctx.seeded (fun _ => 0) :=
  bucketedScan_eq _ _ _ _ (by decide) (by
    intro t member
    simp only [QueueScanAccountingExamples.levels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst t <;> decide) _

end PetaProof.LeafBucketScanExamples
