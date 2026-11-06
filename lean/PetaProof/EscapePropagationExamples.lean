import PetaProof.EscapePropagationRun
import PetaProof.EscapeCheckExamples

/-! 距離表を事前に与えず、全親カウンターと全逆辺通知から最終表を生成する例。 -/
namespace PetaProof.EscapePropagationExamples

open EscapeFifoExamples EscapeCheckExamples

def source : Edge → Node
  | .goalGoal => .goal
  | .leftGoal => .left
  | .branchGoal => .branch
  | .rightBranch => .right
  | .rootLeft | .rootLeftAgain | .rootRight => .root

def outgoing : Node → List Edge
  | .goal => [.goalGoal]
  | .left => [.leftGoal]
  | .branch => [.branchGoal]
  | .right => [.rightBranch]
  | .root => [.rootLeft, .rootLeftAgain, .rootRight]

def indexed : EscapePropagation.Input Node Edge where
  toInput := reverseInput
  source := source
  outgoing := outgoing
  outgoing_correct := by intro vertex edge; cases vertex <;> cases edge <;> decide
  outgoing_unique := by intro vertex; cases vertex <;> decide
  outgoing_nonempty := by intro vertex; cases vertex <;> decide
  own := fun vertex => decide (vertex ≠ .root)

def startFrame : EscapeFifo.Frame Node := ⟨.goal, 0, EscapeFifo.pop seed⟩
theorem start_valid : startFrame.Invariant :=
  EscapeFifo.Frame.begin_preserves seed (EscapeFifo.seeded_invariant [Node.goal]) (.goal, 0) [] rfl

def started := EscapePropagation.State.initialGoals indexed (fun vertex => decide (vertex = .goal)) startFrame
def first := EscapePropagation.State.notifyIncoming indexed started
def finished := EscapePropagation.State.run indexed 5 first

theorem started_invariant : EscapePropagation.State.Invariant indexed started :=
  EscapePropagation.State.initialGoals_invariant indexed _ startFrame start_valid

theorem first_invariant : EscapePropagation.State.Invariant indexed first :=
  EscapePropagation.State.notifyIncoming_preserves indexed started started_invariant (by intro edge _; rfl)

theorem first_complete : EscapePropagation.State.Complete indexed first := by
  intro edge
  change (EscapePropagation.State.notifyIncoming indexed started).notified edge = true ↔ _
  rw [EscapePropagation.State.notifyIncoming_complete]
  have logged := EscapePropagation.State.notifyMany_popped indexed started (indexed.incoming started.frame.child)
  change first.frame.queue.popped = _ at logged
  rw [logged]
  change edgeChild edge = Node.goal ∨ false = true ↔ edgeChild edge ∈ [Node.goal]
  simp

theorem finished_invariant : EscapePropagation.State.Invariant indexed finished :=
  EscapePropagation.State.run_preserves indexed 5 first first_invariant

theorem finished_complete : EscapePropagation.State.Complete indexed finished :=
  EscapePropagation.State.run_complete indexed 5 first first_complete

theorem finished_drained : finished.frame.queue.pending = [] :=
  EscapePropagation.State.run_drained indexed vertices covered 5 first first_invariant (by decide)

theorem counters_are_exact (vertex : Node) :
    (finished.counters vertex).result = input.computedDistance vertices.length vertex := by cases vertex <;> decide

theorem final_check_passes : input.tableCheck (fun vertex => (finished.counters vertex).result) vertices = true := by decide

theorem target_self_edge_keeps_zero : (first.counters .goal).result = some 0 := rfl

/-- 同じ子への別二辺で残数を2減らすが、右の子の通知まで相手番は未確定。 -/
theorem parallel_edges_wait_for_right :
    ((EscapePropagation.State.advance indexed first).counters .root).left = 1 ∧
      ((EscapePropagation.State.advance indexed first).counters .root).result = none := by decide

theorem real_received_distances : finished.received .rootLeft = 1 ∧
    finished.received .rootLeftAgain = 1 ∧ finished.received .rootRight = 2 := by decide

theorem all_edges_completed (edge : Edge) : finished.notified edge = true := by cases edge <;> decide

namespace Trap

abbrev Vertex := EscapeExamples.Node
abbrev Move := Fin 13

def sources : List Vertex := [.a, .a, .a, .b, .b, .c, .f, .e, .e, .t, .t, .u, .exit]
def children : List Vertex := [.b, .c, .f, .exit, .a, .e, .e, .exit, .a, .u, .exit, .t, .exit]
def source (edge : Move) : Vertex := sources.get edge
def child (edge : Move) : Vertex := children.get edge
def incoming (vertex : Vertex) := (List.finRange 13).filter (fun edge => decide (child edge = vertex))
def outgoing (vertex : Vertex) := (List.finRange 13).filter (fun edge => decide (source edge = vertex))

def indexed : EscapePropagation.Input Vertex Move where
  child := child
  incoming := incoming
  incoming_correct := by intro vertex; cases vertex <;> decide
  incoming_unique := by intro vertex; cases vertex <;> decide
  source := source
  outgoing := outgoing
  outgoing_correct := by intro vertex; cases vertex <;> decide
  outgoing_unique := by intro vertex; cases vertex <;> decide
  outgoing_nonempty := by intro vertex; cases vertex <;> decide
  own := fun vertex => decide (EscapeExamples.arena.owner vertex = EscapeExamples.arena.player)

def seed := EscapeFifo.seeded [EscapeExamples.Node.exit]
def startFrame : EscapeFifo.Frame Vertex := ⟨.exit, 0, EscapeFifo.pop seed⟩
theorem start_valid : startFrame.Invariant :=
  EscapeFifo.Frame.begin_preserves seed (EscapeFifo.seeded_invariant [EscapeExamples.Node.exit]) (.exit, 0) [] rfl

def started := EscapePropagation.State.initialGoals indexed (fun vertex => decide (vertex = .exit)) startFrame
def first := EscapePropagation.State.notifyIncoming indexed started
def finished := EscapePropagation.State.run indexed 8 first

theorem first_invariant : EscapePropagation.State.Invariant indexed first :=
  EscapePropagation.State.notifyIncoming_preserves indexed started
    (EscapePropagation.State.initialGoals_invariant indexed _ startFrame start_valid) (by intro edge _; rfl)

theorem first_complete : EscapePropagation.State.Complete indexed first := by
  intro edge
  change (EscapePropagation.State.notifyIncoming indexed started).notified edge = true ↔ _
  rw [EscapePropagation.State.notifyIncoming_complete]
  have logged := EscapePropagation.State.notifyMany_popped indexed started (indexed.incoming started.frame.child)
  change first.frame.queue.popped = _ at logged
  rw [logged]
  change child edge = EscapeExamples.Node.exit ∨ false = true ↔ child edge ∈ [EscapeExamples.Node.exit]
  simp

theorem finished_invariant : EscapePropagation.State.Invariant indexed finished :=
  EscapePropagation.State.run_preserves indexed 8 first first_invariant

theorem finished_complete : EscapePropagation.State.Complete indexed finished :=
  EscapePropagation.State.run_complete indexed 8 first first_complete

theorem finished_drained : finished.frame.queue.pending = [] :=
  EscapePropagation.State.run_drained indexed EscapeExamples.vertices EscapeExamples.covered 8 first first_invariant (by decide)

theorem final_check_passes :
    EscapeExamples.exitInput.tableCheck (fun vertex => (finished.counters vertex).result) EscapeExamples.vertices = true := by decide

theorem counters_are_exact (vertex : Vertex) : (finished.counters vertex).result =
    EscapeExamples.exitInput.computedDistance EscapeExamples.vertices.length vertex :=
  EscapeExamples.exitInput.checked_exact _ EscapeExamples.vertices EscapeExamples.covered final_check_passes vertex

/-- Tに出口があっても、相手がUへ留まれるので両方とも無限距離のまま。 -/
theorem trap_stays_unresolved : (finished.counters .t).result = none ∧ (finished.counters .u).result = none := by decide

end Trap

end PetaProof.EscapePropagationExamples
