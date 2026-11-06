import PetaProof.QueueThresholdScan

/-!
既存のキュー制御と同じ分岐をたどる証明用の通常作業ログ。
元の手続きや本番にログ配列を追加せず、空の予算ステップは作業として数えない。
-/
namespace PetaProof

universe u v
variable {V : Type u} {E : Type v}

structure OrdinaryLog (V : Type u) (E : Type v) where
  pops : List V
  callbacks : List E

namespace OrdinaryLog

def empty : OrdinaryLog V E := ⟨[], []⟩
def append (first second : OrdinaryLog V E) : OrdinaryLog V E :=
  ⟨first.pops ++ second.pops, first.callbacks ++ second.callbacks⟩

/-- pop履歴との一致に加え、各popの全逆辺をちょうど一度ずつ記録する。 -/
def Sound (incoming : V → List E) (before after : List V) (log : OrdinaryLog V E) : Prop :=
  before ++ log.pops = after ∧ log.callbacks = log.pops.flatMap incoming

theorem sound_empty (incoming : V → List E) (before : List V) : Sound incoming before before empty := by
  simp [Sound, empty]

theorem Sound.trans {incoming : V → List E} {before middle after : List V} {first second : OrdinaryLog V E}
    (left : Sound incoming before middle first) (right : Sound incoming middle after second) :
    Sound incoming before after (first.append second) := by
  constructor
  · simpa only [append, ← List.append_assoc, left.1] using right.1
  · simp only [append, left.2, right.2, List.flatMap_append]

end OrdinaryLog
end PetaProof

namespace PetaProof.ThresholdGame.PropagationState

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]

def visitLog (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (state : PropagationState V E) : OrdinaryLog V E :=
  match state.queue.pending with
  | [] => OrdinaryLog.empty
  | child :: _ => ⟨[child], parents.incoming child⟩

def drainLog (indexed : G.IndexedMoves E) (parents : ParentLists indexed) : Nat → PropagationState V E → OrdinaryLog V E
  | 0, _ => OrdinaryLog.empty
  | fuel + 1, state => (visitLog indexed parents state).append
      (drainLog indexed parents fuel (state.queueVisit indexed parents))

theorem visitLog_sound (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (state : PropagationState V E) :
    OrdinaryLog.Sound parents.incoming state.queue.popped (state.queueVisit indexed parents).queue.popped
      (visitLog indexed parents state) := by
  cases pending : state.queue.pending with
  | nil => simpa only [queueVisit, visitLog, pending] using OrdinaryLog.sound_empty parents.incoming state.queue.popped
  | cons child rest =>
    constructor
    · simp only [visitLog, queueVisit, pending, notifyFreshMany_popped, pop, AdmissionQueue.pop]
    · simp [visitLog, pending]

theorem drainLog_sound (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (fuel : Nat)
    (state : PropagationState V E) :
    OrdinaryLog.Sound parents.incoming state.queue.popped (drainQueue indexed parents fuel state).queue.popped
      (drainLog indexed parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact OrdinaryLog.sound_empty _ _
  | succ fuel ih => exact (visitLog_sound indexed parents state).trans (ih _)

end PetaProof.ThresholdGame.PropagationState

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

def settleLog : Nat → PropagationState V E → OrdinaryLog V E
  | 0, state => PropagationState.drainLog ctx.indexed ctx.parents ctx.vertices.length state
  | fuel + 1, state =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    let first := PropagationState.drainLog ctx.indexed ctx.parents ctx.vertices.length state
    if members = [] then first else first.append (settleLog fuel (closed.addMany members))

theorem settleLog_sound (fuel : Nat) (state : PropagationState V E) :
    OrdinaryLog.Sound ctx.parents.incoming state.queue.popped (ctx.settleQueue fuel state).queue.popped
      (ctx.settleLog fuel state) := by
  induction fuel generalizing state with
  | zero => exact PropagationState.drainLog_sound ctx.indexed ctx.parents ctx.vertices.length state
  | succ fuel ih =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    have first := PropagationState.drainLog_sound ctx.indexed ctx.parents ctx.vertices.length state
    by_cases empty : members = []
    · change ctx.localMembers (ctx.drain state) = [] at empty
      simpa only [settleLog, settleQueue, if_pos empty] using first
    · have rest := ih (closed.addMany members)
      rw [addMany_popped] at rest
      change ¬ ctx.localMembers (ctx.drain state) = [] at empty
      simpa only [settleLog, settleQueue, if_neg empty] using first.trans rest

def phaseLog (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) (state : PropagationState V E) : OrdinaryLog V E :=
  (ctx.atLevel t positive bounded).settleLog ctx.vertices.length (ctx.prepare t positive bounded state)

theorem phaseLog_sound (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) (state : PropagationState V E) :
    OrdinaryLog.Sound ctx.parents.incoming state.queue.popped (ctx.phase t positive bounded state).queue.popped
      (ctx.phaseLog t positive bounded state) := by
  have result := (ctx.atLevel t positive bounded).settleLog_sound ctx.vertices.length (ctx.prepare t positive bounded state)
  unfold prepare at result
  rw [PropagationState.notifyMany_popped] at result
  exact result

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanQueueLog : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → PropagationState V E → OrdinaryLog V E
  | _, _, [], _, _ => OrdinaryLog.empty
  | G, ctx, t :: rest, valid, state =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    (ctx.phaseLog t positive bounded state).append
      (scanQueueLog (G.retune t positive bounded) (ctx.atLevel t positive bounded) rest
        (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state))

theorem scanQueueLog_sound (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) (values : V → Int) :
    OrdinaryLog.Sound ctx.parents.incoming state.queue.popped (scanQueues G ctx levels valid state values).1.queue.popped
      (scanQueueLog G ctx levels valid state) := by
  induction levels generalizing G state values with
  | nil => exact OrdinaryLog.sound_empty _ _
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let next := ctx.phase t positive bounded state
    exact (ctx.phaseLog_sound t positive bounded state).trans
      (ih (G.retune t positive bounded) (ctx.atLevel t positive bounded) _ next
        (latchValues values t (fun vertex => (next.counters vertex).admitted)))

theorem scanQueue_final_invariant (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state) (values : V → Int) :
    (scanQueues G ctx levels valid state values).1.queue.Invariant := by
  induction levels generalizing G state values with
  | nil => exact certificate.invariant.queue
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    obtain ⟨next⟩ := ctx.phase_certified state certificate t positive (below t (by simp))
    exact ih (G.retune t positive bounded) (ctx.atLevel t positive bounded) _ descending.of_cons
      (fun s member => Int.le_of_lt (List.rel_of_pairwise_cons descending member)) _ next _

end PetaProof.ThresholdGame
