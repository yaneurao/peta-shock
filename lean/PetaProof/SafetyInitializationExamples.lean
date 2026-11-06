import PetaProof.SafetyInitializedRun
import PetaProof.SafetyClassificationExamples

namespace PetaProof.SafetyClassification.InitializationExamples

open Examples (vertices vertices_unique vertices_cover loopInput parallelInput wonInput outsideInput leafInput)
open CounterQueueExamples (ParentEdge)

def parallelArrays := initializeRows parallelInput vertices emptyArrays

theorem parallel_counts_and_bad : parallelArrays.count false = 1 ∧ parallelArrays.count true = 2 ∧
    parallelArrays.bad false = false ∧ parallelArrays.bad true = false ∧ parallelArrays.pending = [] := by decide

theorem parallel_edges_kept : parallelArrays.incoming false = [ParentEdge.first, ParentEdge.second] := by decide
theorem parallel_parents_kept : (parallelArrays.incoming false).map parallelInput.indexed.source = [true, true] := by decide

theorem parallel_spec : Processed parallelInput vertices parallelArrays :=
  initialize_spec parallelInput vertices vertices_unique

theorem actual_initial_state : executionOf parallelInput parallelArrays =
    SafetyExecution.initial (graph parallelInput vertices vertices_unique vertices_cover) vertices :=
  initialize_state_eq parallelInput vertices vertices_unique vertices_cover

def wonArrays := initializeRows wonInput vertices emptyArrays
theorem excluded_parent_untouched : wonArrays.count false = 0 ∧ wonArrays.bad false = false ∧
    wonArrays.count true = 1 ∧ wonArrays.pending = [] := by decide

def outsideArrays := initializeRows outsideInput vertices emptyArrays
theorem outside_bad_queues : outsideArrays.count true = 0 ∧ outsideArrays.bad true = true ∧
    outsideArrays.pending = [true] := by decide

def leafArrays := initializeRows leafInput vertices emptyArrays
theorem nonchecking_bad_queues : leafArrays.count false = 1 ∧ leafArrays.bad false = false ∧
    leafArrays.count true = 0 ∧ leafArrays.bad true = true ∧ leafArrays.pending = [true] := by decide

def actualLeafGraph := initializedGraph leafInput vertices vertices_unique vertices_cover
def actualLeafStart := executionOf leafInput leafArrays
def actualLeafFinish := SafetyExecution.tick actualLeafGraph actualLeafStart

theorem initialized_leaf_run : SafetyExecution.Run actualLeafGraph actualLeafStart 1 actualLeafFinish :=
  SafetyExecution.Run.next (SafetyExecution.Run.done _)
theorem initialized_leaf_stopped : SafetyExecution.Stopped actualLeafFinish := by constructor <;> decide
theorem initialized_leaf_survivors : SafetyExecution.alive actualLeafFinish false ∧
    ¬ SafetyExecution.alive actualLeafFinish true := by
  constructor
  · rfl
  · intro impossible; cases impossible

-- 初期化の外側で親を重複走査するとcountが二重加算される。Nodup前提は飾りではない。
theorem duplicate_scan_double_counts :
    (initializeRows leafInput [false, false] emptyArrays).count false = 2 ∧ initCount leafInput false = 1 := by decide

open PropagationExamples (ordinaryGame)

def ordinaryIndexed : ordinaryGame.IndexedMoves Bool := {
  outgoing := fun _ => [false, true]
  source := fun _ => ()
  move := fun edge => if edge then .leaf (-20) else .leaf 20
  unique := by intro _; decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge _; cases vertex; rfl
  legal := by intro _ edge _; cases edge <;> simp [ordinaryGame]
  covers := by
    intro vertex move legal
    rcases legal with positive | negative
    · exact ⟨false, by decide, positive.symm⟩
    · exact ⟨true, by decide, negative.symm⟩
}

def ordinaryInput : Input ordinaryGame Bool := {
  indexed := ordinaryIndexed
  won := fun _ => false
  core := fun _ => true
  checked := fun _ _ => false
  check_correct := by simp [ordinaryGame]
}

def orArrays := initializeRows ordinaryInput [()] emptyArrays
theorem or_ignores_bad_leaf : orArrays.count () = 1 ∧ orArrays.bad () = false ∧
    orArrays.pending = [] ∧ badEdges ordinaryInput () = [true] := by decide

def andGame : ThresholdGame Unit := { ordinaryGame with player := true }
def andIndexed : andGame.IndexedMoves Bool := { ordinaryIndexed with }
def andInput : Input andGame Bool := { ordinaryInput with indexed := andIndexed }
def andArrays := initializeRows andInput [()] emptyArrays

theorem and_bad_overrides_positive_count : andArrays.count () = 1 ∧ andArrays.bad () = true ∧
    andArrays.pending = [()] := by decide

end PetaProof.SafetyClassification.InitializationExamples
