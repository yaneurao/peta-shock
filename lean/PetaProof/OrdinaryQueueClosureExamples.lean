import PetaProof.OrdinaryQueueClosure
import PetaProof.CertifiedPropagationExamples

/-! 実際の排出順、同じ子への別辺、重複通知ガード、通知途中の境界、循環バッチ。 -/
namespace PetaProof.OrdinaryQueueClosureExamples

open ThresholdGame CounterQueueExamples PropagationStateExamples CertifiedPropagationExamples PropagationExamples
open PropagationState

def parentLists : ParentLists parentIndexed where
  incoming := fun child => if child then [] else [.first, .second]
  unique := by intro child; cases child <;> decide
  exact := by intro child edge; cases child <;> cases edge <;> simp [parentIndexed, parentMove]

def parentDone := drainQueue parentIndexed parentLists 2 leafReady

theorem first_visit_finishes_both_callbacks :
    (leafReady.queueVisit parentIndexed parentLists).notified .first = true ∧
    (leafReady.queueVisit parentIndexed parentLists).notified .second = true ∧
    (leafReady.queueVisit parentIndexed parentLists).queue.pending = [true] := by decide

theorem fifo_drained_once : parentDone.queue.popped = [false, true] ∧ parentDone.queue.pending = [] := by decide

theorem and_parent_confirmed : (parentDone.counters true).admitted = true ∧
    (parentDone.counters true).left = 0 := by decide

/-- 生のhitへ同じ辺を二度渡した例とは異なり、第二の辺なしではAND親は確定しない。 -/
theorem repeated_callback_cannot_finish_and :
    ((childTaken.notifyFreshMany parentIndexed [.first, .first]).counters true).admitted = false ∧
    ((childTaken.notifyFreshMany parentIndexed [.first, .first]).counters true).left = 1 := by decide

theorem old_callback_is_skipped : firstNotified.notifyFresh parentIndexed .first = firstNotified := by
  rfl

theorem empty_queue_with_unfinished_callbacks : firstNotified.queue.pending = [] ∧
    ¬ NodesComplete parentIndexed firstNotified := by
  refine ⟨by decide, ?_⟩
  intro complete
  have impossible := complete false (by decide) .second rfl
  change false = true at impossible
  cases impossible

/-- この不正な境界からは、空キューを回すだけで失われた通知は回復しない。 -/
theorem half_callback_is_not_a_valid_start :
    ((drainQueue parentIndexed parentLists 2 firstNotified).counters true).admitted = false := by decide

theorem computed_parent_closure : parentDone.won =
    parentGame.ordinaryClosure [false, true] leafReady.won := by
  obtain ⟨certificate⟩ := leaf_ready_sound.certified parentIndexed
  apply drainQueue_closure parentIndexed parentLists [false, true]
    (by intro vertex; cases vertex <;> decide) leafReady certificate
  · intro edge score same _
    cases edge <;> simp_all [parentIndexed, parentMove]
    decide
  · intro child impossible
    cases impossible

theorem parent_notifications_generated : NodesComplete parentIndexed parentDone :=
  drainQueue_nodes_complete parentIndexed parentLists 2 leafReady (by intro _ impossible; cases impossible)

theorem parent_winning (root : Bool) : parentGame.FourfoldWinning root := by
  obtain ⟨certificate⟩ := leaf_ready_sound.certified parentIndexed
  obtain ⟨final⟩ := drainQueue_certified parentIndexed parentLists 2 leafReady certificate
  apply final.region.fourfold_winning root
  change ((drainQueue parentIndexed parentLists 2 leafReady).counters root).admitted = true
  cases root <;> decide

def loopParents : ParentLists loopIndexed where
  incoming := fun child => [!child]
  unique := by intro child; simp
  exact := by intro child edge; cases child <;> cases edge <;> simp [loopIndexed]

def cycleDone := drainQueue loopIndexed loopParents 2 loopAdded

theorem cyclic_batch_is_not_requeued : cycleDone.queue.popped = [false, true] ∧
    cycleDone.queue.pending = [] ∧ cycleDone.notified false = true ∧ cycleDone.notified true = true := by decide

theorem cyclic_batch_closure : cycleDone.won =
    loopGame.ordinaryClosure [false, true] loopAdded.won := by
  apply drainQueue_closure loopIndexed loopParents [false, true]
    (by intro vertex; cases vertex <;> decide) loopAdded cyclicCertificate
  · intro edge score impossible _
    cases edge <;> cases impossible
  · intro child impossible
    cases impossible

def noParents : ParentLists badLeafIndexed where
  incoming := fun _ => []
  unique := fun _ => by simp
  exact := by intro _ _; simp [badLeafIndexed]

theorem bad_leaf_remains_unconfirmed :
    ¬ (drainQueue badLeafIndexed noParents 1 (initial badLeafIndexed)).won () := by
  change ¬ ((drainQueue badLeafIndexed noParents 1 (initial badLeafIndexed)).counters ()).admitted = true
  decide

theorem already_empty_stays_empty :
    drainQueue badLeafIndexed noParents 5 (initial badLeafIndexed) = initial badLeafIndexed :=
  drainQueue_empty_fixed badLeafIndexed noParents 5 (initial badLeafIndexed) rfl

end PetaProof.OrdinaryQueueClosureExamples
