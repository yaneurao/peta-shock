import PetaProof.QueueScanAccounting
import PetaProof.QueueThresholdScanExamples
import PetaProof.QueueThresholdControlExamples

/-! 閾値の空進行、分岐・再合流、循環から祖先への伝播を含む通常イベントの実数。 -/
namespace PetaProof.QueueScanAccountingExamples

open ThresholdGame

theorem and_across_four_levels : QueueThresholdScanExamples.context.positiveQueueWork
    QueueThresholdScanExamples.levels QueueThresholdScanExamples.valid = 3 := by decide

inductive Vertex where
  | root | left | right | child
  deriving DecidableEq

inductive Edge where
  | rootLeft | rootRight | leftChild | rightChild | exit
  deriving DecidableEq

def own (vertex : Vertex) : Bool := match vertex with
  | .root | .child => false
  | .left | .right => true

def legal (vertex : Vertex) (move : Move Vertex) : Prop := match vertex with
  | .root => move = .node .left ∨ move = .node .right
  | .left | .right => move = .node .child
  | .child => move = .leaf 20

def game : ThresholdGame Vertex where
  legal := legal
  owner := own
  check := fun _ _ => False
  player := false
  threshold := 40
  mate := 40
  positive := by decide
  bounded := by decide
  alternating := by intro vertex target edge; cases vertex <;> cases target <;> simp_all [legal, own]
  nonempty_moves := by
    intro vertex
    cases vertex with
    | root => exact ⟨.node .left, Or.inl rfl⟩
    | left => exact ⟨.node .child, rfl⟩
    | right => exact ⟨.node .child, rfl⟩
    | child => exact ⟨.leaf 20, rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def outgoing : Vertex → List Edge
  | .root => [.rootLeft, .rootRight]
  | .left => [.leftChild]
  | .right => [.rightChild]
  | .child => [.exit]

def source : Edge → Vertex
  | .rootLeft | .rootRight => .root
  | .leftChild => .left
  | .rightChild => .right
  | .exit => .child

def move : Edge → Move Vertex
  | .rootLeft => .node .left
  | .rootRight => .node .right
  | .leftChild | .rightChild => .node .child
  | .exit => .leaf 20

def indexed : game.IndexedMoves Edge where
  outgoing := outgoing
  source := source
  move := move
  unique := by intro vertex; cases vertex <;> decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [outgoing, source]
  legal := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [outgoing, game, legal, move]
  covers := by
    intro vertex candidate edge
    cases vertex with
    | root =>
      rcases edge with left | right
      · exact ⟨.rootLeft, by decide, left.symm⟩
      · exact ⟨.rootRight, by decide, right.symm⟩
    | left => exact ⟨.leftChild, by decide, edge.symm⟩
    | right => exact ⟨.rightChild, by decide, edge.symm⟩
    | child => exact ⟨.exit, by decide, edge.symm⟩

def parents : ParentLists indexed where
  incoming := fun target => match target with
    | .root => []
    | .left => [.rootLeft]
    | .right => [.rootRight]
    | .child => [.leftChild, .rightChild]
  unique := by intro target; cases target <;> decide
  exact := by intro target edge; cases target <;> cases edge <;> simp [indexed, move]

def context : game.QueueContext Edge where
  vertices := [.root, .left, .right, .child]
  unique := by decide
  covered := by intro vertex; cases vertex <;> decide
  indexed := indexed
  parents := parents
  core := fun _ => false
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [game]

def levels : List Int := [40, 20]
theorem valid : ∀ t ∈ levels, 0 < t ∧ t ≤ game.mate := by
  intro t member
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> subst t <;> decide

theorem root_popped_once : (context.ordinaryLog levels valid).pops = [.child, .left, .right, .root] := by decide
theorem callbacks_not_paths : (context.ordinaryLog levels valid).callbacks =
    [.leftChild, .rightChild, .rootLeft, .rootRight] := by decide
theorem single_leaf_notification : context.leafLog levels valid = [.exit] := by decide
theorem diamond_work_is_nine : context.ordinaryWork levels valid = 9 := by decide
theorem diamond_reaches_bound : context.ordinaryWork levels valid = context.vertices.length + context.allEdges.length := by decide

theorem diamond_work_bounded : context.positiveQueueWork levels valid ≤ 9 :=
  context.positiveQueueWork_bound levels valid (by decide)

def cycleContext := QueueThresholdControlExamples.context
def cycleLevels : List Int := [10]
theorem cycle_valid : ∀ t ∈ cycleLevels, 0 < t ∧ t ≤ QueueThresholdControlExamples.game.mate := by
  intro t member
  have same : t = 10 := by simpa [cycleLevels] using member
  subst t
  decide

theorem cycle_and_ancestor_work : cycleContext.ordinaryWork cycleLevels cycle_valid = 6 := by decide
theorem cycle_pops_once : (cycleContext.ordinaryLog cycleLevels cycle_valid).pops =
    [.other, .own, .root] := by decide

end PetaProof.QueueScanAccountingExamples
