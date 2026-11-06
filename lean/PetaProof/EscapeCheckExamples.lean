import PetaProof.EscapeTableCheck
import PetaProof.EscapeReverseEdges
import PetaProof.EscapeFifoExamples
import PetaProof.EscapeExamples

/-! 実FIFO出力の受理、誤距離・未確定漏れ・循環の偽有限距離の棄却。 -/
namespace PetaProof.EscapeCheckExamples

open EscapeFifoExamples

def fifoLabels (vertex : Node) : Option Nat :=
  (finished.popped.find? (fun item => decide (item.1 = vertex))).map Prod.snd

theorem fifo_accepted : input.tableCheck fifoLabels vertices = true := by decide

theorem fifo_exact (vertex : Node) : fifoLabels vertex = input.computedDistance vertices.length vertex :=
  input.checked_exact fifoLabels vertices covered fifo_accepted vertex

theorem wrong_maximum_rejected :
    input.tableCheck (fun vertex => if vertex = .root then some 2 else fifoLabels vertex) vertices = false := by decide

theorem missing_parent_rejected :
    input.tableCheck (fun vertex => if vertex = .left then none else fifoLabels vertex) vertices = false := by decide

inductive Edge where
  | goalGoal | leftGoal | branchGoal | rightBranch | rootLeft | rootLeftAgain | rootRight
  deriving DecidableEq

def edgeChild : Edge → Node
  | .goalGoal | .leftGoal | .branchGoal => .goal
  | .rightBranch => .branch
  | .rootLeft | .rootLeftAgain => .left
  | .rootRight => .right

def incoming : Node → List Edge
  | .goal => [.goalGoal, .leftGoal, .branchGoal]
  | .branch => [.rightBranch]
  | .left => [.rootLeft, .rootLeftAgain]
  | .right => [.rootRight]
  | .root => []

def reverseInput : EscapeReverseEdges.Input Node Edge where
  child := edgeChild
  incoming := incoming
  incoming_correct := by intro vertex edge; cases vertex <;> cases edge <;> decide
  incoming_unique := by intro vertex; cases vertex <;> decide

def edges : List Edge := [.goalGoal, .leftGoal, .branchGoal, .rightBranch, .rootLeft, .rootLeftAgain, .rootRight]
theorem edges_covered (edge : Edge) : edge ∈ edges := by cases edge <;> decide

theorem all_edges_notified_once :
    (reverseInput.notifications (finished.popped.map Prod.fst)).Nodup ∧
      (reverseInput.notifications (finished.popped.map Prod.fst)).length = 7 := by decide

theorem partial_scan_keeps_parallel_edges :
    reverseInput.notifications [.goal, .left] =
      [.goalGoal, .leftGoal, .branchGoal, .rootLeft, .rootLeftAgain] := rfl

theorem actual_fifo_notification_bound :
    (reverseInput.notifications (finished.popped.map Prod.fst)).length ≤ edges.length := by
  have inv := EscapeFifo.advance_preserves last.2.queue last_invariants.2.1.queue []
  exact reverseInput.fifo_notification_count_bound finished inv edges edges_covered

namespace Trap
open EscapeExamples

def labels : EscapeExamples.Node → Option Nat
  | .a => some 3
  | .b => some 4
  | .c | .f => some 2
  | .e => some 1
  | .t | .u => none
  | .exit => some 0

theorem infinite_cycle_accepted : exitInput.tableCheck labels EscapeExamples.vertices = true := by decide

/-- 出口のある循環でも相手が居残れる。未確定を恣意的な有限値に変えると棄却する。 -/
theorem false_finite_cycle_rejected :
    exitInput.tableCheck (fun vertex => match vertex with
      | .t => some 1
      | .u => some 2
      | _ => labels vertex) EscapeExamples.vertices = false := by decide

theorem accepted_trap_exact (vertex : EscapeExamples.Node) :
    labels vertex = exitInput.computedDistance EscapeExamples.vertices.length vertex :=
  exitInput.checked_exact labels EscapeExamples.vertices EscapeExamples.covered infinite_cycle_accepted vertex

end Trap
end PetaProof.EscapeCheckExamples
