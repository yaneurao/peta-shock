import PetaProof.SafetyExecutionGame
import PetaProof.CertifiedPropagationExamples

namespace PetaProof.SafetyExecution.GameExamples

open PropagationExamples (loopGame)
open CertifiedPropagationExamples (loopIndexed)

def view (vertex : Bool) : SafetyCounter.View Bool := {
  good := []
  internal := [vertex]
  bad := []
  internal_unique := by simp
  internal_not_good := by simp
  bad_disjoint := by simp
}

/-- 相手の王手継続を含む二局面循環。片方ずつではなく一括で保証領域へ追加する。 -/
def graph : Graph Bool Bool := {
  view := view
  own := fun vertex => !vertex
  eligible := fun _ => true
  source := id
  target := fun vertex => !vertex
  source_of_mem := by intro vertex edge member; simpa [view] using member
  source_eligible := by simp
  target_eligible := by simp
  incoming := fun vertex => [!vertex]
  incoming_unique := by simp
  incoming_spec := by intro vertex edge; cases vertex <;> cases edge <;> simp [view]
}

def model : GameModel graph loopIndexed (fun _ => False) := {
  own := by intro vertex; cases vertex <;> rfl
  outgoing := by intro vertex _ edge; rfl
  good := by
    intro vertex _ edge _
    simp [graph, view, loopIndexed, ThresholdGame.GoodExit]
  internal := by
    intro vertex _ edge member
    cases vertex <;> cases edge <;>
      simp_all [graph, view, SafetyCounter.View.outgoing, loopIndexed, loopGame]
  target := by intro vertex edge _; rfl
}

def start := initial graph [false, true]

theorem already_stopped : Stopped start := by constructor <;> decide
theorem both_survive : alive start false ∧ alive start true := by constructor <;> rfl

noncomputable def cyclicBatch : loopGame.SafeBatch (fun _ => False) (alive start) :=
  batch_at_halt graph loopIndexed (fun _ => False) model [false, true]
    (by intro vertex; cases vertex <;> simp) (Run.done start) already_stopped (by simp)

theorem certified_cyclic_batch : Nonempty (loopGame.SafeBatch (fun _ => False) (alive start)) := ⟨cyclicBatch⟩

end PetaProof.SafetyExecution.GameExamples
