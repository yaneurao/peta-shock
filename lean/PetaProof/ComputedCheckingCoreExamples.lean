import PetaProof.ComputedCheckingCore
import PetaProof.ReverseAdjacencyExamples

/-! 普通の循環と片側王手循環を区別し、循環外の祖先をcoreへ混入させない。 -/
namespace PetaProof.ComputedCheckingCoreExamples

open ThresholdGame

def cycle : CoreGraphInput QueueThresholdControlExamples.game QueueThresholdControlExamples.Node where
  vertices := QueueThresholdControlExamples.context.vertices
  unique := QueueThresholdControlExamples.context.unique
  covered := QueueThresholdControlExamples.context.covered
  indexed := QueueThresholdControlExamples.indexed
  checked := QueueThresholdControlExamples.context.checked
  check_correct := QueueThresholdControlExamples.context.check_correct

theorem cycle_core_only : cycle.prepared.1.core .root = false ∧
    cycle.prepared.1.core .other = true ∧ cycle.prepared.1.core .own = true := by decide

theorem opposite_cycle_broken : cycle.prepared.2 .root = false ∧
    cycle.prepared.2 .other = false ∧ cycle.prepared.2 .own = false := by decide

def quiet : CoreGraphInput QueueThresholdControlExamples.quietGame QueueThresholdControlExamples.Node where
  vertices := QueueThresholdControlExamples.context.vertices
  unique := QueueThresholdControlExamples.context.unique
  covered := QueueThresholdControlExamples.context.covered
  indexed := QueueThresholdControlExamples.quietIndexed
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [QueueThresholdControlExamples.quietGame]

theorem quiet_core_empty (vertex : QueueThresholdControlExamples.Node) :
    quiet.prepared.1.core vertex = false ∧ quiet.prepared.2 vertex = false := by
  cases vertex <;> decide

def diamond : CoreGraphInput QueueScanAccountingExamples.game QueueScanAccountingExamples.Edge where
  vertices := ReverseAdjacencyExamples.diamond.vertices
  unique := ReverseAdjacencyExamples.diamond.unique
  covered := ReverseAdjacencyExamples.diamond.covered
  indexed := ReverseAdjacencyExamples.diamond.indexed
  checked := ReverseAdjacencyExamples.diamond.checked
  check_correct := ReverseAdjacencyExamples.diamond.check_correct

theorem diamond_rows_four : diamond.valueRows.length = 4 := diamond.valueRows_length

theorem diamond_core_empty (vertex : QueueScanAccountingExamples.Vertex) :
    diamond.prepared.1.core vertex = false ∧ diamond.prepared.2 vertex = false := by
  cases vertex <;> decide

theorem diamond_positive_twenty : diamond.prepared.1.generatedPositiveValues .root = 20 := by
  change diamond.prepared.1.positiveStreamingValues ([40, 20] : List Int) (by
    intro level member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide) .root = 20
  rw [diamond.prepared.1.positiveStreamingValues_eq _ _ (by decide)]
  decide

def aggregate := LinearCycleFlags.build ([0, 1, 2] : List Nat)
  (fun vertex => if vertex = 2 then 1 else 0) (fun vertex => decide (vertex = 2))

theorem aggregate_two_and_self : aggregate.counts[0]? = some 2 ∧
    aggregate.counts[1]? = some 1 ∧ LinearCycleFlags.flag aggregate 0 = true ∧
    LinearCycleFlags.flag aggregate 1 = true ∧ LinearCycleFlags.flag aggregate 2 = false := by decide

theorem empty_aggregate : (LinearCycleFlags.build ([] : List Nat) id (fun _ => false)).counts.size = 0 := by decide

theorem singleton_without_self : LinearCycleFlags.flag
    (LinearCycleFlags.build [()] (fun _ => 0) (fun _ => false)) 0 = false := by decide

theorem singleton_with_self : LinearCycleFlags.flag
    (LinearCycleFlags.build [()] (fun _ => 0) (fun _ => true)) 0 = true := by decide

end PetaProof.ComputedCheckingCoreExamples
