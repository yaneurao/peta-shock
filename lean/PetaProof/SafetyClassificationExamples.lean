import PetaProof.SafetyIncomingBuild
import PetaProof.SafetyReturnedChoice
import PetaProof.CertifiedPropagationExamples

namespace PetaProof.SafetyClassification.Examples

open PropagationExamples (loopGame)
open CertifiedPropagationExamples (loopIndexed)
open CounterQueueExamples (ParentEdge parentOutgoing parentSource parentGame parentIndexed)

def vertices : List Bool := [false, true]
theorem vertices_unique : vertices.Nodup := by decide
theorem vertices_cover (vertex : Bool) : vertex ∈ vertices := by cases vertex <;> simp [vertices]

def loopInput : Input loopGame Bool := {
  indexed := loopIndexed
  won := fun _ => false
  core := fun _ => true
  checked := fun vertex _ => vertex
  check_correct := by intros; rfl
}

def loopGraph := graph loopInput vertices vertices_unique vertices_cover
def loopStart := SafetyExecution.initial loopGraph vertices

theorem generated_loop_survives : SafetyExecution.Stopped loopStart ∧
    SafetyExecution.alive loopStart false ∧ SafetyExecution.alive loopStart true := by
  constructor
  · constructor <;> decide
  · constructor <;> rfl

theorem generated_loop_choice : returnedChoice loopInput loopStart false = some false := by decide
theorem generated_opponent_none : returnedIndex loopInput loopStart true = none := by decide

def generatedLoopBatch : loopGame.SafeBatch (fun vertex => loopInput.won vertex = true)
    (SafetyExecution.alive loopStart) :=
  returnedBatch loopInput vertices vertices_unique vertices_cover (SafetyExecution.Run.done loopStart)
    generated_loop_survives.1

theorem generated_batch_uses_returned_move : generatedLoopBatch.choice false = .node true := rfl

def parallelIndexed : loopGame.IndexedMoves ParentEdge := {
  outgoing := parentOutgoing
  source := parentSource
  move := fun edge => match edge with
    | .first | .second => .node false
    | .exit => .node true
  unique := by intro vertex; cases vertex <;> decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [parentOutgoing, parentSource]
  legal := by
    intro vertex edge member
    cases vertex <;> cases edge <;> simp_all [parentOutgoing, loopGame]
  covers := by
    intro vertex move legal
    cases vertex with
    | false => exact ⟨.exit, by decide, legal.symm⟩
    | true => exact ⟨.first, by decide, legal.symm⟩
}

def parallelInput : Input loopGame ParentEdge := { loopInput with indexed := parallelIndexed }

theorem parallel_incoming_edges : incoming parallelInput vertices false = [.first, .second] := by decide
theorem parallel_parent_duplicates :
    buildBuckets (target parallelInput) parallelInput.indexed.source (allInternal parallelInput vertices)
      (fun _ => []) false = [true, true] := by decide

theorem parallel_build_matches_spec :
    buildBuckets (target parallelInput) parallelInput.indexed.source (allInternal parallelInput vertices)
      (fun _ => []) false = (incoming parallelInput vertices false).map parallelInput.indexed.source :=
  built_incoming_parents parallelInput vertices false

def wonInput : Input loopGame Bool := { loopInput with won := fun vertex => !vertex }
def wonGraph := graph wonInput vertices vertices_unique vertices_cover
def wonStart := SafetyExecution.initial wonGraph vertices

theorem good_precedes_internal : goodEdges wonInput true = [true] ∧ internalEdges wonInput true = [] := by
  constructor <;> decide
theorem won_source_ignored : internalEdges wonInput false = [] ∧ allInternal wonInput vertices = [] := by
  constructor <;> decide
theorem initial_won_excluded : ¬ SafetyExecution.alive wonStart false ∧ SafetyExecution.alive wonStart true := by
  constructor
  · intro h; cases h
  · rfl

def outsideInput : Input loopGame Bool := { loopInput with core := fun vertex => vertex }
def outsideGraph := graph outsideInput vertices vertices_unique vertices_cover
def outsideStart := SafetyExecution.initial outsideGraph vertices
def outsideFinish := SafetyExecution.tick outsideGraph outsideStart

theorem outside_core_is_bad : badEdges outsideInput true = [true] ∧ internalEdges outsideInput true = [] := by
  constructor <;> decide
theorem outside_core_removed : SafetyExecution.Stopped outsideFinish ∧ outsideFinish.deleted true = true := by
  constructor
  · constructor <;> decide
  · decide

def leafInput : Input parentGame ParentEdge := {
  indexed := parentIndexed
  won := fun _ => false
  core := fun _ => true
  checked := fun _ _ => false
  check_correct := by simp [parentGame]
}

def leafGraph := graph leafInput vertices vertices_unique vertices_cover
def leafStart := SafetyExecution.initial leafGraph vertices
def leafFinish := SafetyExecution.tick leafGraph leafStart

theorem nonchecking_and_is_bad : badEdges leafInput true = [.first, .second] ∧
    internalEdges leafInput true = [] := by constructor <;> decide
theorem good_leaf_choice : returnedChoice leafInput leafFinish false = some .exit := by decide
theorem good_leaf_safe : parentGame.legal false (leafInput.indexed.move .exit) ∧
    parentGame.SafeMove (fun vertex => leafInput.won vertex = true) (SafetyExecution.alive leafFinish)
      false (leafInput.indexed.move .exit) := returned_choice_safe leafInput leafFinish false .exit good_leaf_choice

end PetaProof.SafetyClassification.Examples
