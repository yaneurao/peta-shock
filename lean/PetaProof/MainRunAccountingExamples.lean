import PetaProof.MainRunAccounting
import PetaProof.StreamingRecordsExamples

/-! leaf通知の二重課金の除去、core空の局所項、記録回数、出力行の差を検査する。 -/
namespace PetaProof.MainRunAccountingExamples

open ThresholdGame

def ctx := QueueScanAccountingExamples.context
def levels := QueueScanAccountingExamples.levels
theorem valid : ∀ t ∈ levels, 0 < t ∧ t ≤ QueueScanAccountingExamples.game.mate := QueueScanAccountingExamples.valid
theorem descending : levels.Pairwise (fun a b => b < a) := by decide
theorem below : ∀ t ∈ levels, t ≤ QueueScanAccountingExamples.game.threshold := by
  intro t member
  simp only [levels, QueueScanAccountingExamples.levels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> subst t <;> decide

theorem initialization_seventeen : ctx.initializationWork = 17 := by decide
theorem bucket_preparation_twelve : ctx.bucketPreparationWork levels = 12 := by decide
theorem bucket_with_notification_thirteen : ctx.bucketEventWork levels = 13 := by decide
theorem leaf_notification_one : (ctx.leafBatches levels).flatten.length = 1 := by decide

theorem record_actions_four : (ctx.mainLedger levels valid).records = 4 := by
  rw [ctx.mainLedger_records levels valid descending below]
  decide

theorem local_control_twice : (ctx.mainLedger levels valid).localControl = 2 := by decide
theorem local_term_zero : ctx.localTerm levels = 0 := by decide
theorem local_analysis_zero : (ctx.mainLedger levels valid).localAnalysis = 0 := by decide
theorem batch_insertions_zero : (ctx.mainLedger levels valid).batchInsertions = 0 := by decide

theorem no_core_main_bound : ctx.mainWork levels valid ≤ 606 :=
  ctx.mainWork_without_core (by decide) levels valid descending below

theorem four_thresholds_bounded : ([40, 30, 20, 10] : List Int).length ≤ 40 :=
  QueueThresholdScanExamples.game.level_count_bound _ DenseLeafBucketExamples.valid (by decide)

theorem assemble_both_signs : assembleValueRows [false, true]
    (fun vertex => if vertex then 0 else 20) (fun vertex => if vertex then 30 else 0) =
      [(false, 20), (true, -30)] := by decide

end PetaProof.MainRunAccountingExamples
