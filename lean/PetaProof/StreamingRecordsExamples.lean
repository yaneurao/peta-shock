import PetaProof.StreamingRecords
import PetaProof.DenseLeafBucketExamples

/-! 初期leaf確定・AND残数・局所循環から祖先への伝播・低閾値での保持を検査する。 -/
namespace PetaProof.StreamingRecordsExamples

open ThresholdGame

def start : RecordingState Unit Bool := ⟨QueueThresholdScanExamples.initial, fun _ => 0, 0⟩
def after30 := QueueThresholdScanExamples.top.recordedPhase 30 (by decide) (by decide) start
def after20 := QueueThresholdScanExamples.at30.recordedPhase 20 (by decide) (by decide) after30
def after10 := QueueThresholdScanExamples.at20.recordedPhase 10 (by decide) (by decide) after20

theorem and_partial_not_recorded : after30.values () = 0 ∧ after30.attempts = 0 ∧
    (after30.state.counters ()).left = 1 := by decide

theorem and_recorded_at_twenty : after20.values () = 20 ∧ after20.attempts = 1 := by decide

theorem lower_threshold_keeps_value : after10.values () = 20 ∧ after10.attempts = 1 := by decide

def seededContext := QueueScanAccountingExamples.context.atLevel 20 (by decide) (by decide)
def seeded : RecordingState QueueScanAccountingExamples.Vertex QueueScanAccountingExamples.Edge :=
  ⟨seededContext.seeded, fun _ => 0, 0⟩
def afterSeeded := seededContext.recordedPhase 20 (by decide) (by decide) seeded

theorem seeded_pending_unrecorded : (seeded.state.counters .child).admitted = true ∧
    seeded.values .child = 0 ∧ seeded.attempts = 0 := by decide

theorem seeded_four_pop_records : afterSeeded.attempts = 4 ∧
    afterSeeded.values .child = 20 ∧ afterSeeded.values .left = 20 ∧
    afterSeeded.values .right = 20 ∧ afterSeeded.values .root = 20 := by decide

def cycleStart : RecordingState QueueThresholdControlExamples.Node QueueThresholdControlExamples.Node :=
  ⟨QueueThresholdControlExamples.start, fun _ => 0, 0⟩
def afterCycle := QueueThresholdControlExamples.context.recordedPhase 10 (by decide) (by decide) cycleStart

theorem cycle_and_ancestor_recorded : afterCycle.attempts = 3 ∧ afterCycle.values .own = 10 ∧
    afterCycle.values .other = 10 ∧ afterCycle.values .root = 10 := by decide

theorem positive_streaming_value_twenty :
    QueueThresholdScanExamples.context.positiveStreamingValues [40, 30, 20, 10] DenseLeafBucketExamples.valid () = 20 := by
  rw [QueueThresholdScanExamples.context.positiveStreamingValues_eq _ _ (by decide)]
  decide

theorem one_record_attempt_bound :
    (QueueThresholdScanExamples.context.positiveStreamingResult [40, 30, 20, 10] DenseLeafBucketExamples.valid).attempts ≤ 1 :=
  QueueThresholdScanExamples.context.positiveStreamingResult_attempts_bound _ _ (by decide)

end PetaProof.StreamingRecordsExamples
