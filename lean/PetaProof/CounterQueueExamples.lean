import PetaProof.IndexedPropagation
import PetaProof.NotificationBatches
import PetaProof.IntegerValueExamples

/-! 辺の多重性、OR/AND、重複通知の危険性、FIFOと通知完了条件の検査例。 -/
namespace PetaProof.CounterQueueExamples

open ThresholdGame IntegerValueExamples

def twoEdges : List Nat := [0, 1]
def initialTwo : HitCounter Nat := HitCounter.initial twoEdges
def afterFirst : HitCounter Nat := HitCounter.hit false initialTwo 0
def afterBoth : HitCounter Nat := HitCounter.hit false afterFirst 1

theorem and_waits_for_second : afterFirst.left = 1 ∧ afterFirst.admitted = false := by decide
theorem and_finishes_on_second : afterBoth.left = 0 ∧ afterBoth.admitted = true := by decide

theorem after_first_invariant : HitCounter.Invariant false twoEdges afterFirst :=
  HitCounter.hit_preserves false initialTwo 0 twoEdges
    (HitCounter.initial_invariant false twoEdges (by decide)) (by decide) (by decide) (by decide)

theorem after_both_invariant : HitCounter.Invariant false twoEdges afterBoth :=
  HitCounter.hit_preserves false afterFirst 1 twoEdges after_first_invariant (by decide) (by decide) (by decide)

theorem or_finishes_on_first : (HitCounter.hit true initialTwo 0).admitted = true ∧
    (HitCounter.hit true initialTwo 0).left = 2 := by decide

/-- hitには重複ガードがない。無効な通知列を仮に与えると、2本目なしでANDが確定してしまう。 -/
theorem duplicate_hit_is_unsafe : (HitCounter.hit false afterFirst 0).admitted = true ∧
    (HitCounter.hit false afterFirst 0).seen 1 = false := by decide

def queueThree : AdmissionQueue Bool :=
  ((AdmissionQueue.initial.admit false).admit true).admit false

theorem queue_three_reachable : AdmissionQueue.Reachable queueThree :=
  .admit (.admit (.admit .initial false) true) false

theorem duplicate_admit_does_not_duplicate : queueThree.pending = [false, true] := by decide

theorem popped_cannot_be_requeued : queueThree.pop.admit false = queueThree.pop :=
  AdmissionQueue.cannot_readmit_popped queueThree.pop
    (AdmissionQueue.pop_preserves queueThree queue_three_reachable.invariant) false (by decide)

theorem fifo_order_preserved : queueThree.pop.pop.popped = [false, true] ∧
    queueThree.pop.pop.pending = [] := by decide

def parallelKey (edge : Nat) : Sum Int Bool :=
  if edge = 2 then .inl 20 else .inr false

/-- 0と1は同じ子局面へ進むが、二つの辺IDとして両方を通知する。 -/
theorem parallel_edges_are_both_notified :
    notificationTrace [0, 1, 2] parallelKey [.inl 20, .inr false] = [2, 0, 1] := by decide

theorem parallel_notifications_unique :
    (notificationTrace [0, 1, 2] parallelKey [.inl 20, .inr false]).Nodup :=
  notificationTrace_unique _ _ _ (by decide) (by decide)

theorem same_node_key_twice_duplicates_edges :
    ¬ (notificationTrace [0, 1, 2] parallelKey [.inr false, .inr false]).Nodup := by decide

/-- 降順leaf列と取り出し履歴があれば、交互の通知列全体の一意性を証明できる。 -/
theorem notifications_from_actual_queue_unique :
    (notificationTrace [0, 1, 2] parallelKey [.inl 20, .inr false, .inr true]).Nodup :=
  notifications_unique_from_queue_levels _ (by decide) parallelKey _ [20] (by decide)
    queueThree.pop.pop
    (AdmissionQueue.pop_preserves queueThree.pop (AdmissionQueue.pop_preserves queueThree queue_three_reachable.invariant))
    (by decide) (by decide)

/-- 自分のleafから相手の親へ伝播する、2局面の例。相手側は同じ子への別辺を2本持つ想定。 -/
def parentGame : ThresholdGame Bool where
  legal := fun v m => if v then m = .node false else m = .leaf 20
  owner := id
  check := fun _ _ => False
  player := false
  threshold := 10
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by intro v w edge; cases v <;> cases w <;> simp_all
  nonempty_moves := by intro v; cases v <;> exact ⟨_, rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

inductive ParentEdge where
  | first | second | exit
  deriving DecidableEq

def parentOutgoing (v : Bool) : List ParentEdge :=
  if v then [.first, .second] else [.exit]

def parentSource : ParentEdge → Bool
  | .first | .second => true
  | .exit => false

def parentMove : ParentEdge → Move Bool
  | .first | .second => .node false
  | .exit => .leaf 20

def parentIndexed : parentGame.IndexedMoves ParentEdge where
  outgoing := parentOutgoing
  source := parentSource
  move := parentMove
  unique := by intro v; cases v <;> decide
  at_source := by intro e; cases e <;> decide
  source_of_mem := by intro v e member; cases v <;> cases e <;> simp_all [parentOutgoing, parentSource]
  legal := by intro v e member; cases v <;> cases e <;> simp_all [parentOutgoing, parentMove, parentGame]
  covers := by
    intro v m legal
    cases v with
    | false =>
      have same : m = .leaf 20 := legal
      exact ⟨.exit, by decide, same.symm⟩
    | true =>
      have same : m = .node false := legal
      exact ⟨.first, by decide, same.symm⟩

def parentFirst : HitCounter ParentEdge :=
  HitCounter.hit false (HitCounter.initial [.first, .second]) .first

/-- 同じ子への2本目の通知から、安全な通常伝播バッチを実際に構成する。 -/
def parent_second_hit_batch : parentGame.SafeBatch (fun v => v = false) (fun v => v = true) := by
  apply parentIndexed.hit_batch (fun v => v = false) true parentFirst .second
  · exact HitCounter.hit_preserves false (HitCounter.initial [ParentEdge.first, .second]) .first _
      (HitCounter.initial_invariant false _ (by decide)) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · decide
  · intro e member _
    cases e with
    | first => rfl
    | second => rfl
    | exit => simp [parentIndexed, parentOutgoing] at member
  · rfl
  · decide

def childPopped : AdmissionQueue Bool := (AdmissionQueue.initial.admit false).pop

/-- parents走査途中では、queueが空でもまだ通常伝播が閉じていない場合がある。 -/
theorem empty_queue_before_all_callbacks_is_not_closed :
    childPopped.pending = [] ∧ afterFirst.seen 1 = false ∧
      ¬ parentGame.OrdinaryClosed (fun v => v = false) := by
  refine ⟨by decide, by decide, ?_⟩
  intro closed
  have impossible := closed true (Or.inr ⟨by decide, ?_⟩)
  · cases impossible
  · intro m legal
    have same : m = .node false := legal
    subst m
    rfl

/-- 良いleafがない場合は、未確定カウンターを残したまま通常伝播が閉じる。 -/
def badLeafIndexed : (fixedLeafGame (-20)).IndexedMoves Unit where
  outgoing := fun _ => [()]
  source := fun _ => ()
  move := fun _ => .leaf (-20)
  unique := fun _ => by decide
  at_source := fun _ => by simp
  source_of_mem := by intro v _ _; cases v; rfl
  legal := fun _ _ _ => rfl
  covers := by
    intro _ m legal
    exact ⟨(), by simp, legal.symm⟩

theorem bad_leaf_closed_from_counter_and_queue : (fixedLeafGame (-20)).OrdinaryClosed (fun _ => False) := by
  apply badLeafIndexed.ordinary_closed_when_drained (fun _ => False)
    (fun _ => HitCounter.initial [()]) (AdmissionQueue.initial : AdmissionQueue Unit)
  · intro v
    simp [HitCounter.initial]
  · intro v
    simp [AdmissionQueue.initial]
  · intro v
    exact badLeafIndexed.initial_counter_invariant v
  · exact AdmissionQueue.initial_invariant
  · rfl
  · intro v _ e _ score same good
    have equal : (-20 : Int) = score := Move.leaf.inj same
    change (1 : Int) ≤ score at good
    omega
  · intro _ impossible
    cases impossible

end PetaProof.CounterQueueExamples
