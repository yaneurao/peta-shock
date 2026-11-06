import PetaProof.DenseLeafBuckets

/-! 通常FIFOのpop時だけ値を書く。全頂点のlatch走査もpopログの実行時保存も不要。 -/
namespace PetaProof

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

theorem writeAdmissions_append (values : V → Int) (level : Int) (first second : List V) :
    writeAdmissions values level (first ++ second) = writeAdmissions (writeAdmissions values level first) level second := by
  induction first generalizing values with
  | nil => rfl
  | cons vertex rest ih => exact ih (writeAdmission values level vertex)

/-- 値の非零要素を、取り出し済み頂点と対応させる。待機中は確定済みでも未記録でよい。 -/
def RecordsPopped (values : V → Int) (popped : List V) : Prop :=
  ∀ vertex, values vertex ≠ 0 ↔ vertex ∈ popped

theorem records_append (values : V → Int) (level : Int) (nonzero : level ≠ 0)
    (before added : List V) (represented : RecordsPopped values before) :
    RecordsPopped (writeAdmissions values level added) (before ++ added) := by
  intro vertex
  rw [writeAdmissions_get, List.mem_append, ← represented vertex]
  by_cases zero : values vertex = 0 <;> by_cases member : vertex ∈ added <;>
    simp [zero, member, nonzero]

structure RecordingState (V : Type u) (E : Type v) where
  state : ThresholdGame.PropagationState V E
  values : V → Int
  attempts : Nat

end PetaProof

namespace PetaProof.ThresholdGame.PropagationState

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
/-- 待機項目は過去のpop履歴と交わらないため、初回記録のガードは必ず未記録側を通る。 -/
theorem pending_value_zero (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (invariant : Invariant indexed state) (values : V → Int)
    (represented : RecordsPopped values state.queue.popped) (vertex : V) (member : vertex ∈ state.queue.pending) :
    values vertex = 0 := by
  by_cases zero : values vertex = 0
  · exact zero
  · have old := (represented vertex).mp zero
    have cross := (List.pairwise_append.mp invariant.queue.unique).2.2
    exact False.elim (cross vertex old vertex member rfl)

def recordedVisit (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (level : Int)
    (recorded : RecordingState V E) : RecordingState V E :=
  match recorded.state.queue.pending with
  | [] => recorded
  | vertex :: _ =>
    ⟨recorded.state.queueVisit indexed parents, writeAdmission recorded.values level vertex, recorded.attempts + 1⟩

def recordedDrain (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (level : Int) :
    Nat → RecordingState V E → RecordingState V E
  | 0, recorded => recorded
  | fuel + 1, recorded => recordedDrain indexed parents level fuel (recordedVisit indexed parents level recorded)

theorem recordedVisit_writes (indexed : G.IndexedMoves E) (parents : ParentLists indexed) (level : Int)
    (recorded : RecordingState V E) (invariant : Invariant indexed recorded.state)
    (represented : RecordsPopped recorded.values recorded.state.queue.popped)
    (vertex : V) (rest : List V) (pending : recorded.state.queue.pending = vertex :: rest) :
    (recordedVisit indexed parents level recorded).values vertex = level ∧
      (recordedVisit indexed parents level recorded).attempts = recorded.attempts + 1 := by
  have zero := pending_value_zero indexed recorded.state invariant recorded.values represented vertex (by simp [pending])
  simp [recordedVisit, pending, writeAdmission, zero]

theorem recordedDrain_eq (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (level : Int) (fuel : Nat) (recorded : RecordingState V E) :
    recordedDrain indexed parents level fuel recorded =
      ⟨drainQueue indexed parents fuel recorded.state,
        writeAdmissions recorded.values level (drainLog indexed parents fuel recorded.state).pops,
        recorded.attempts + (drainLog indexed parents fuel recorded.state).pops.length⟩ := by
  induction fuel generalizing recorded with
  | zero => cases recorded; rfl
  | succ fuel ih =>
    rw [recordedDrain, ih]
    cases pending : recorded.state.queue.pending with
    | nil =>
      simp only [recordedVisit, pending, drainQueue, queueVisit, drainLog, visitLog,
        OrdinaryLog.empty, OrdinaryLog.append, List.nil_append, writeAdmissions]
    | cons vertex rest =>
      simp only [recordedVisit, pending, drainQueue, drainLog, visitLog, OrdinaryLog.append,
        List.singleton_append, writeAdmissions, List.length_cons, Nat.add_assoc]
      rw [Nat.add_comm 1]

end PetaProof.ThresholdGame.PropagationState

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

def recordedSettle (level : Int) : Nat → RecordingState V E → RecordingState V E
  | 0, recorded => PropagationState.recordedDrain ctx.indexed ctx.parents level ctx.vertices.length recorded
  | fuel + 1, recorded =>
    let closed := PropagationState.recordedDrain ctx.indexed ctx.parents level ctx.vertices.length recorded
    let members := ctx.localMembers closed.state
    if members = [] then closed else recordedSettle level fuel { closed with state := closed.state.addMany members }

theorem recordedSettle_eq (level : Int) (fuel : Nat) (recorded : RecordingState V E) :
    ctx.recordedSettle level fuel recorded =
      ⟨ctx.settleQueue fuel recorded.state,
        writeAdmissions recorded.values level (ctx.settleLog fuel recorded.state).pops,
        recorded.attempts + (ctx.settleLog fuel recorded.state).pops.length⟩ := by
  induction fuel generalizing recorded with
  | zero => exact PropagationState.recordedDrain_eq _ _ _ _ _
  | succ fuel ih =>
    simp only [recordedSettle, PropagationState.recordedDrain_eq]
    by_cases empty : ctx.localMembers (ctx.drain recorded.state) = []
    · have expanded : ctx.localMembers (PropagationState.drainQueue ctx.indexed ctx.parents ctx.vertices.length recorded.state) = [] := empty
      simp only [settleQueue, settleLog, if_pos empty, if_pos expanded]
      rfl
    · have expanded : ¬ ctx.localMembers (PropagationState.drainQueue ctx.indexed ctx.parents ctx.vertices.length recorded.state) = [] := empty
      simp only [if_neg expanded]
      rw [ih]
      simp only [settleQueue, settleLog, if_neg empty, OrdinaryLog.append, List.length_append,
        writeAdmissions_append, Nat.add_assoc]
      rfl

def recordedPhase (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (recorded : RecordingState V E) : RecordingState V E :=
  (ctx.atLevel t positive bounded).recordedSettle t ctx.vertices.length
    { recorded with state := ctx.prepare t positive bounded recorded.state }

theorem recordedPhase_eq (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (recorded : RecordingState V E) :
    ctx.recordedPhase t positive bounded recorded =
      ⟨ctx.phase t positive bounded recorded.state,
        writeAdmissions recorded.values t (ctx.phaseLog t positive bounded recorded.state).pops,
        recorded.attempts + (ctx.phaseLog t positive bounded recorded.state).pops.length⟩ :=
  (ctx.atLevel t positive bounded).recordedSettle_eq _ _ _

/-- phase終了時は通常FIFOが空なので、全確定頂点がpop済みである。 -/
theorem phase_drained (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (ctx.phase t positive (Int.le_trans lower G.bounded) state).queue.pending = [] := by
  exact (ctx.atLevel t positive (Int.le_trans lower G.bounded)).settleQueue_queue_empty ctx.vertices.length
    (ctx.prepare t positive (Int.le_trans lower G.bounded) state)
    (ctx.prepare_certificate state certificate t positive lower)

theorem recordedPhase_latch (recorded : RecordingState V E)
    (certificate : StateCertificate ctx.indexed recorded.state)
    (represented : RecordsPopped recorded.values recorded.state.queue.popped)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (ctx.recordedPhase t positive (Int.le_trans lower G.bounded) recorded).values =
      latchValues recorded.values t (fun vertex => ((ctx.phase t positive (Int.le_trans lower G.bounded) recorded.state).counters vertex).admitted) := by
  rw [ctx.recordedPhase_eq]
  let next := ctx.phase t positive (Int.le_trans lower G.bounded) recorded.state
  obtain ⟨next_certificate⟩ := ctx.phase_certified recorded.state certificate t positive lower
  have drained := ctx.phase_drained recorded.state certificate t positive lower
  have logged := (ctx.phaseLog_sound t positive (Int.le_trans lower G.bounded) recorded.state).1
  apply writeAdmissions_eq_latch
  intro vertex
  rw [next_certificate.invariant.agrees vertex,
    AdmissionQueue.drained_iff_popped next.queue next_certificate.invariant.queue drained vertex, ← logged,
    List.mem_append, ← represented vertex]

theorem recordedPhase_represents (recorded : RecordingState V E)
    (represented : RecordsPopped recorded.values recorded.state.queue.popped)
    (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) :
    RecordsPopped (ctx.recordedPhase t positive bounded recorded).values
      (ctx.recordedPhase t positive bounded recorded).state.queue.popped := by
  rw [ctx.recordedPhase_eq]
  have logged := (ctx.phaseLog_sound t positive bounded recorded.state).1
  rw [← logged]
  exact records_append recorded.values t (by omega) _ _ represented

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- 値は各popに対する一要素更新だけで記録する。latchValuesを実行しない。 -/
def scanRecorded : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → RecordingState V E → RecordingState V E
  | _, _, [], _, recorded => recorded
  | G, ctx, t :: rest, valid, recorded =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    scanRecorded (G.retune t positive bounded) (ctx.atLevel t positive bounded) rest
      (fun s member => valid s (by simp [member])) (ctx.recordedPhase t positive bounded recorded)

theorem scanRecorded_attempts (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (recorded : RecordingState V E) :
    (scanRecorded G ctx levels valid recorded).attempts =
      recorded.attempts + (scanQueueLog G ctx levels valid recorded.state).pops.length := by
  induction levels generalizing G recorded with
  | nil => simp [scanRecorded, scanQueueLog, OrdinaryLog.empty]
  | cons t rest ih =>
    rw [scanRecorded, ih]
    simp only [QueueContext.recordedPhase_eq, scanQueueLog, OrdinaryLog.append, List.length_append, Nat.add_assoc]

theorem scanRecorded_eq (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (recorded : RecordingState V E) (certificate : StateCertificate ctx.indexed recorded.state)
    (represented : RecordsPopped recorded.values recorded.state.queue.popped) :
    ((scanRecorded G ctx levels valid recorded).state, (scanRecorded G ctx levels valid recorded).values) =
      scanQueues G ctx levels valid recorded.state recorded.values := by
  induction levels generalizing G recorded with
  | nil => rfl
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    let next := ctx.recordedPhase t positive bounded recorded
    have nextState : next.state = ctx.phase t positive bounded recorded.state := by
      simp only [next, ctx.recordedPhase_eq]
    have nextValues : next.values = latchValues recorded.values t
        (fun vertex => ((ctx.phase t positive bounded recorded.state).counters vertex).admitted) :=
      ctx.recordedPhase_latch recorded certificate represented t positive (below t (by simp))
    obtain ⟨next_certificate⟩ := ctx.phase_certified recorded.state certificate t positive (below t (by simp))
    have nextCertified : StateCertificate low.indexed next.state := by
      rw [nextState]
      exact next_certificate
    have nextRepresented := ctx.recordedPhase_represents recorded represented t positive bounded
    have tailResult := ih (G.retune t positive bounded) low
      (fun s member => valid s (by simp [member])) descending.of_cons
      (fun s member => Int.le_of_lt (List.rel_of_pairwise_cons descending member)) next nextCertified nextRepresented
    change ((scanRecorded (G.retune t positive bounded) low rest _ next).state,
      (scanRecorded (G.retune t positive bounded) low rest _ next).values) = _
    rw [tailResult, nextState, nextValues]
    rfl

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

def streamingResult (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : RecordingState V E :=
  scanRecorded G ctx levels valid ⟨ctx.seeded, fun _ => 0, 0⟩

theorem streamingResult_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ((ctx.streamingResult levels valid).state, (ctx.streamingResult levels valid).values) =
      scanQueues G ctx levels valid ctx.seeded (fun _ => 0) := by
  apply scanRecorded_eq G ctx levels valid descending below _ ctx.seeded_certificate
  intro vertex
  simp only [ctx.seeded_popped, List.not_mem_nil]
  decide

theorem streamingResult_attempts (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    (ctx.streamingResult levels valid).attempts = (ctx.ordinaryLog levels valid).pops.length := by
  simpa only [streamingResult, Nat.zero_add] using scanRecorded_attempts G ctx levels valid ⟨ctx.seeded, fun _ => 0, 0⟩

theorem streamingResult_attempts_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.streamingResult levels valid).attempts ≤ ctx.vertices.length := by
  rw [ctx.streamingResult_attempts]
  exact ctx.ordinaryPops_bound levels valid descending below

theorem streaming_two_sides_bound (otherCore : V → Bool)
    (ownLevels : List Int) (ownValid : ∀ t ∈ ownLevels, 0 < t ∧ t ≤ G.mate)
    (ownDescending : ownLevels.Pairwise (fun a b => b < a)) (ownBelow : ∀ t ∈ ownLevels, t ≤ G.threshold)
    (otherLevels : List Int) (otherValid : ∀ t ∈ otherLevels, 0 < t ∧ t ≤ G.mate)
    (otherDescending : otherLevels.Pairwise (fun a b => b < a)) (otherBelow : ∀ t ∈ otherLevels, t ≤ G.threshold) :
    (ctx.streamingResult ownLevels ownValid).attempts +
      ((ctx.opposite otherCore).streamingResult otherLevels otherValid).attempts ≤ 2 * ctx.vertices.length := by
  have own := ctx.streamingResult_attempts_bound ownLevels ownValid ownDescending ownBelow
  have other := (ctx.opposite otherCore).streamingResult_attempts_bound otherLevels otherValid otherDescending otherBelow
  change ((ctx.opposite otherCore).streamingResult otherLevels otherValid).attempts ≤ ctx.vertices.length at other
  omega

end QueueContext
end PetaProof.ThresholdGame

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- 構築済みleaf行の消費と、通常pop時の記録を同じ走査で実行する。 -/
def scanRecordedBatches : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → List (List E) →
    RecordingState V E → RecordingState V E
  | _, _, [], _, _, recorded => recorded
  | G, ctx, t :: rest, valid, batches, recorded =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    let next := low.recordedSettle t ctx.vertices.length
      { recorded with state := recorded.state.notifyMany low.indexed (batches.headD []) }
    scanRecordedBatches (G.retune t positive bounded) low rest
      (fun s member => valid s (by simp [member])) batches.tail next

theorem scanRecordedBatches_eq (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (recorded : RecordingState V E) :
    scanRecordedBatches G ctx levels valid (ctx.bandBatches G.threshold levels) recorded =
      scanRecorded G ctx levels valid recorded := by
  induction levels generalizing G recorded with
  | nil => rfl
  | cons t rest ih =>
    simp only [QueueContext.bandBatches, scanRecordedBatches, List.headD_cons, List.tail_cons, scanRecorded]
    simpa only [QueueContext.recordedPhase, QueueContext.prepare, QueueContext.bandBatches_retune] using
      ih (G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
        (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2)
        (fun s member => valid s (by simp [member])) (ctx.recordedPhase t (valid t (by simp)).1 (valid t (by simp)).2 recorded)

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

def denseStreamingResult (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : RecordingState V E :=
  let batches := ctx.denseLeafBatches levels
  scanRecordedBatches G ctx levels valid batches.tail
    ⟨(PropagationState.initial ctx.indexed).notifyMany ctx.indexed (batches.headD []), fun _ => 0, 0⟩

theorem denseStreamingResult_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.denseStreamingResult levels valid = ctx.streamingResult levels valid := by
  simp only [denseStreamingResult, ctx.denseLeafBatches_eq levels valid, ctx.leafBatches_eq levels descending below,
    List.headD_cons, List.tail_cons, scanRecordedBatches_eq]
  rfl

theorem denseStreamingResult_values (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ((ctx.denseStreamingResult levels valid).state, (ctx.denseStreamingResult levels valid).values) =
      scanQueues G ctx levels valid ctx.seeded (fun _ => 0) := by
  rw [ctx.denseStreamingResult_eq levels valid descending below]
  exact ctx.streamingResult_eq levels valid descending below

theorem denseStreamingResult_attempts_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.denseStreamingResult levels valid).attempts ≤ ctx.vertices.length := by
  rw [ctx.denseStreamingResult_eq levels valid descending below]
  exact ctx.streamingResult_attempts_bound levels valid descending below

def positiveStreamingResult (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : RecordingState V E :=
  let top := ctx.atLevel G.mate G.mate_positive (Int.le_refl _)
  top.denseStreamingResult levels valid

def positiveStreamingValues (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : V → Int :=
  (ctx.positiveStreamingResult levels valid).values

theorem positiveStreamingValues_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) :
    ctx.positiveStreamingValues levels valid = ctx.positiveQueueValues levels valid := by
  let top := ctx.atLevel G.mate G.mate_positive (Int.le_refl _)
  exact congrArg Prod.snd (top.denseStreamingResult_values levels valid descending (fun t member => (valid t member).2))

theorem positiveStreamingResult_attempts_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) :
    (ctx.positiveStreamingResult levels valid).attempts ≤ ctx.vertices.length :=
  (ctx.atLevel G.mate G.mate_positive (Int.le_refl _)).denseStreamingResult_attempts_bound levels valid descending
    (fun t member => (valid t member).2)

noncomputable def computedPositiveStreamingValues : V → Int :=
  ctx.positiveStreamingValues G.setLevels (fun t member =>
    ⟨((G.setLevels_critical_iff t).mp member).1, ((G.setLevels_critical_iff t).mp member).2.1⟩)

theorem computedPositiveStreamingValues_eq : ctx.computedPositiveStreamingValues = ctx.computedPositiveQueueValues :=
  ctx.positiveStreamingValues_eq _ _ (processedLevels_ordered _ _)

noncomputable def computedStreamingValue (otherCore : V → Bool) : V → Int :=
  fun vertex => ctx.computedPositiveStreamingValues vertex -
    (ctx.opposite otherCore).computedPositiveStreamingValues vertex

theorem computedStreamingValue_eq (otherCore : V → Bool) :
    ctx.computedStreamingValue otherCore = ctx.computedQueueValue otherCore := by
  unfold computedStreamingValue
  rw [ctx.computedPositiveStreamingValues_eq, (ctx.opposite otherCore).computedPositiveStreamingValues_eq]
  rfl

/-- 高速leaf表とpop時の記録を使う両側の実行からも、同じ厳密な整数値を得る。 -/
theorem computedStreamingValue_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) (root : V) :
    G.ExactValue root (ctx.computedStreamingValue otherCore root) := by
  rw [ctx.computedStreamingValue_eq]
  exact ctx.computedQueueValue_exact otherCore leaves own_covers other_covers root

end QueueContext
end PetaProof.ThresholdGame
