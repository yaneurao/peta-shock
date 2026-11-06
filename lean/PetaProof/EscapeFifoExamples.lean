import PetaProof.EscapeFifoNotify
import PetaProof.EscapeComputation

/-! ダイヤモンド再合流、異なる距離のAND子、同じ子への別辺IDを実際に通知する。 -/
namespace PetaProof.EscapeFifoExamples

open EscapeFifo

inductive Node where
  | goal | left | branch | right | root
  deriving DecidableEq

def row : List Bool := [false, true]
def child (edge : Bool) : Node := if edge then .right else .left
def cost (edge : Bool) : Nat := if edge then 2 else 1
def emptyCounter : EscapeCounter.State Bool := EscapeCounter.initial row

def seed : State Node := seeded [.goal]
def afterGoal : State Node := advance seed [.left, .branch]
def leftFrame : Frame Node := ⟨.left, 1, pop afterGoal⟩
def first := Frame.notifyParent false leftFrame .root emptyCounter false
def afterBranch := advance first.2.queue [.right]
def rightFrame : Frame Node := ⟨.right, 2, pop afterBranch⟩
def last := Frame.notifyParent false rightFrame .root first.1 true
def finished := advance last.2.queue []

theorem first_waits : first.1.left = 1 ∧ first.1.peak = 1 ∧ first.1.result = none ∧
    first.2.queue.pending = [(.branch, 1)] := by decide

theorem last_is_maximum : last.1.left = 0 ∧ last.1.peak = 2 ∧ last.1.result = some 3 ∧
    last.2.queue.pending = [(.root, 3)] := by decide

theorem actual_pop_order : finished.popped = [(.goal, 0), (.left, 1), (.branch, 1), (.right, 2), (.root, 3)] ∧
    finished.pending = [] := by decide

theorem left_frame_invariant : Frame.Invariant leftFrame := by
  have initial := seeded_invariant ([Node.goal])
  have next := advance_preserves seed initial [.left, .branch]
  exact Frame.begin_preserves afterGoal next (.left, 1) [(.branch, 1)] rfl

theorem first_invariants : EscapeCounter.Invariant row cost first.1 ∧ Frame.Invariant first.2 ∧
    first.2.Reported row child cost first.1 := by
  exact Frame.notifyParent_preserves false leftFrame left_frame_invariant .root row (by decide) child cost
    emptyCounter (EscapeCounter.initial_invariant row cost (by decide))
    (by intro edge _ impossible; cases impossible) false (by decide) rfl rfl rfl rfl

theorem right_frame_invariant : Frame.Invariant rightFrame := by
  have branchInv := advance_preserves first.2.queue first_invariants.2.1.queue [.right]
  exact Frame.begin_preserves afterBranch branchInv (.right, 2) [] rfl

theorem last_invariants : EscapeCounter.Invariant row cost last.1 ∧ Frame.Invariant last.2 ∧
    last.2.Reported row child cost last.1 := by
  apply Frame.notifyParent_preserves false rightFrame right_frame_invariant .root row (by decide) child cost
    first.1 first_invariants.1 ?_ true (by decide) rfl rfl rfl rfl
  intro edge _ seen
  cases edge with
  | false => decide
  | true => cases seen

/-- 同じ子への二つの元辺は別々に数えるが、最大距離は同じ1のままである。 -/
def duplicateFirst := Frame.notifyParent false leftFrame .root emptyCounter false
def duplicateLast := Frame.notifyParent false duplicateFirst.2 .root duplicateFirst.1 true

theorem distinct_edges_same_child : duplicateFirst.1.result = none ∧ duplicateLast.1.left = 0 ∧
    duplicateLast.1.result = some 2 ∧ duplicateLast.2.queue.pending = [(.branch, 1), (.root, 2)] := by decide

/-- 別辺IDを同じpop中に通知する場合も、一般の保存定理の仮定を満たす。 -/
theorem duplicate_invariants :
    EscapeCounter.Invariant row (fun _ => 1) duplicateLast.1 ∧ Frame.Invariant duplicateLast.2 ∧
      duplicateLast.2.Reported row (fun _ => .left) (fun _ => 1) duplicateLast.1 := by
  have firstInv := Frame.notifyParent_preserves false leftFrame left_frame_invariant .root row
    (by decide) (fun _ => Node.left) (fun _ => 1) emptyCounter
    (EscapeCounter.initial_invariant row (fun _ => 1) (by decide))
    (by intro edge _ impossible; cases impossible) false (by decide) rfl rfl rfl rfl
  exact Frame.notifyParent_preserves false duplicateFirst.2 firstInv.2.1 .root row
    (by decide) (fun _ => Node.left) (fun _ => 1) duplicateFirst.1 firstInv.1 firstInv.2.2
    true (by decide) rfl rfl rfl rfl

theorem frozen_does_not_requeue :
    (Frame.notifyParent false last.2 .root last.1 true).2.queue.pending = last.2.queue.pending := by rfl

def successors : Node → List Node
  | .goal => [.goal]
  | .left | .branch => [.goal]
  | .right => [.branch]
  | .root => [.left, .right]

def arena : HistoryArena Node where
  edge := fun vertex next => next ∈ successors vertex
  owner := fun vertex => decide (vertex = .root)
  player := false
  bad := fun _ _ => False
  moves_exist := by
    intro vertex
    cases vertex with
    | goal => exact ⟨.goal, by decide⟩
    | left => exact ⟨.goal, by decide⟩
    | branch => exact ⟨.goal, by decide⟩
    | right => exact ⟨.branch, by decide⟩
    | root => exact ⟨.left, by decide⟩

def input : HistoryArena.EscapeInput arena (fun vertex => vertex = .goal) where
  successors := successors
  edges := fun _ _ => Iff.rfl
  goal := fun vertex => decide (vertex = .goal)
  goal_correct := by intro vertex; simp

def vertices : List Node := [.goal, .left, .branch, .right, .root]
theorem covered (vertex : Node) : vertex ∈ vertices := by cases vertex <;> decide

/-- この具体的な実行では、全出力距離が機械検査済みの最短距離参照計算と一致する。 -/
theorem agrees_with_reference (vertex : Node) :
    ((finished.popped.find? (fun item => decide (item.1 = vertex))).map Prod.snd) =
      input.computedDistance vertices.length vertex := by cases vertex <;> decide

theorem empty_queue_stays_empty :
    (run (fun _ _ _ => []) 5 (seeded ([] : List Node))).pending = [] := rfl

theorem repeated_seed_is_not_duplicated : (seeded ([Node.goal, .goal])).pending = [(.goal, 0)] := rfl

end PetaProof.EscapeFifoExamples
