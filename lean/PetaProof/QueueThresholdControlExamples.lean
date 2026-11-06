import PetaProof.QueueThresholdControl
import PetaProof.OrdinaryQueueClosureExamples

/-! 局所循環の確定が通常FIFOを通じて循環外の祖先へ伝播する、全入力を明示した例。 -/
namespace PetaProof.QueueThresholdControlExamples

open ThresholdGame

inductive Node where
  | root | other | own
  deriving DecidableEq

def next : Node → Node
  | .root => .other
  | .other => .own
  | .own => .other

def game : ThresholdGame Node where
  legal := fun vertex move => move = .node (next vertex)
  owner := fun vertex => decide (vertex = .other)
  check := fun vertex _ => vertex = .other
  player := false
  threshold := 10
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by intro vertex child legal; cases vertex <;> cases child <;> simp_all [next]
  nonempty_moves := fun vertex => ⟨.node (next vertex), rfl⟩
  no_mutual_cycle := by
    intro a b edge back
    have a_other : a = .other := edge.2
    subst a
    have b_own : b = .own := Move.node.inj edge.1
    subst b
    cases back with
    | cons first _ => cases first.2

def indexed : game.IndexedMoves Node where
  outgoing := fun vertex => [vertex]
  source := id
  move := fun vertex => .node (next vertex)
  unique := fun _ => by simp
  at_source := fun _ => by simp
  source_of_mem := by intro vertex edge member; simpa using member
  legal := by
    intro vertex edge member
    have same : edge = vertex := by simpa using member
    subst edge
    rfl
  covers := by intro vertex move legal; exact ⟨vertex, by simp, legal.symm⟩

def parents : ParentLists indexed where
  incoming := fun child => match child with
    | .root => []
    | .other => [.root, .own]
    | .own => [.other]
  unique := by intro child; cases child <;> decide
  exact := by intro child edge; cases child <;> cases edge <;> simp [indexed, next]

def context : game.QueueContext Node where
  vertices := [.root, .other, .own]
  unique := by decide
  covered := by intro vertex; cases vertex <;> decide
  indexed := indexed
  parents := parents
  core := fun vertex => decide (vertex ≠ .root)
  checked := fun vertex _ => decide (vertex = .other)
  check_correct := by intro vertex child; simp [game]

def start : PropagationState Node Node := PropagationState.initial indexed

def boundary : context.Boundary start where
  leaves := by intro edge score impossible _; cases impossible
  nodes := by intro _ impossible; cases impossible

theorem ordinary_queue_initially_empty : start.queue.pending = [] := rfl

/-- rootはcoreに入れない。局所削除の返却は循環内の二頂点だけである。 -/
theorem local_cycle_only : context.localMembers start = [.other, .own] := by decide

def added := start.addMany (context.localMembers start)

theorem root_not_added_by_local_batch : (added.counters .root).admitted = false ∧
    added.queue.pending = [.other, .own] := by decide

theorem root_confirmed_by_ordinary_queue : ((context.drain added).counters .root).admitted = true ∧
    (context.drain added).queue.popped = [.other, .own, .root] := by decide

def finish := context.settleQueue 3 start

theorem all_vertices_confirmed (vertex : Node) : (finish.counters vertex).admitted = true := by
  cases vertex <;> decide

theorem both_queues_stopped : finish.queue.pending = [] ∧ context.localMembers finish = [] := by decide

theorem actual_control_matches_sets : finish.won =
    game.settle context.vertices (fun vertex => context.core vertex = true) 3 start.won :=
  context.settleQueue_refines 3 start (StateCertificate.initial indexed) boundary

theorem root_guaranteed : game.FourfoldWinning .root := by
  obtain ⟨certificate⟩ := context.settleQueue_certified 3 start (StateCertificate.initial indexed)
  exact certificate.region.fourfold_winning .root (all_vertices_confirmed .root)

theorem boundary_preserved : context.Boundary finish := context.settleQueue_boundary 3 start boundary

theorem halted_without_external_stop : finish.queue.pending = [] ∧ context.localMembers finish = [] :=
  context.settleQueue_halted start (StateCertificate.initial indexed) boundary

theorem running_out_of_fuel_is_not_claimed_complete :
    context.localMembers (context.settleQueue 0 start) = [.other, .own] := by decide

/-- 同じ辺を持つが王手がないゲームでは、相手循環を勝ちと誤認してはならない。 -/
def quietGame : ThresholdGame Node := {
  game with
  check := fun _ _ => False
  no_mutual_cycle := by intro _ _ edge _; exact edge.2
}

def quietIndexed : quietGame.IndexedMoves Node where
  outgoing := indexed.outgoing
  source := indexed.source
  move := indexed.move
  unique := indexed.unique
  at_source := indexed.at_source
  source_of_mem := indexed.source_of_mem
  legal := indexed.legal
  covers := indexed.covers

def quietContext : quietGame.QueueContext Node where
  vertices := context.vertices
  unique := context.unique
  covered := context.covered
  indexed := quietIndexed
  parents := { incoming := parents.incoming, unique := parents.unique, exact := parents.exact }
  core := context.core
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [quietGame]

def quietStart : PropagationState Node Node := PropagationState.initial quietIndexed

theorem nonchecking_cycle_deleted :
    (quietContext.localState quietStart).deleted .other = true ∧
    (quietContext.localState quietStart).deleted .own = true ∧
    (quietContext.localState quietStart).pending = [] ∧
    (quietContext.localState quietStart).work = [] := by decide

theorem nonchecking_local_result_empty : quietContext.localMembers quietStart = [] := by decide

theorem nonchecking_control_does_not_confirm (vertex : Node) :
    ((quietContext.settleQueue 3 quietStart).counters vertex).admitted = false := by
  cases vertex <;> decide

end PetaProof.QueueThresholdControlExamples
