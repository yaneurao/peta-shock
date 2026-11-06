import PetaProof.CertifiedPropagation
import PetaProof.PropagationStateExamples

/-! 通常伝播と循環集合の一括追加を含む、値保証付きの実行列の回帰例。 -/
namespace PetaProof.CertifiedPropagationExamples

open ThresholdGame CounterQueueExamples PropagationStateExamples PropagationExamples
open StateCertificate

theorem leaf_ready_sound : SoundRun parentIndexed leafReady := by
  apply SoundRun.leaf_notification parentIndexed SoundRun.initial .exit 20 rfl
  · decide
  · decide

theorem first_notified_sound : SoundRun parentIndexed firstNotified := by
  apply SoundRun.node_notification parentIndexed (SoundRun.pop leaf_ready_sound) .first false rfl
  · decide
  · decide

theorem both_notified_sound : SoundRun parentIndexed bothNotified := by
  apply SoundRun.node_notification parentIndexed first_notified_sound .second false rfl
  · decide
  · decide

theorem finished_sound : SoundRun parentIndexed finished := SoundRun.pop both_notified_sound

theorem finished_guarantees (root : Bool) : parentGame.LowerGuarantee root 10 := by
  apply finished_sound.lower_guarantee parentIndexed root
  change (finished.counters root).admitted = true
  cases root <;> decide

def loopIndexed : loopGame.IndexedMoves Bool where
  outgoing := fun vertex => [vertex]
  source := id
  move := fun vertex => .node (!vertex)
  unique := fun _ => by simp
  at_source := fun _ => by simp
  source_of_mem := by intro vertex edge member; simpa using member
  legal := by
    intro vertex edge member
    have same : edge = vertex := by simpa using member
    subst edge
    rfl
  covers := by intro vertex move legal; exact ⟨vertex, by simp, legal.symm⟩

def loopStart : PropagationState Bool Bool := PropagationState.initial loopIndexed
def loopAdded := loopStart.addMany [false, true]

/-- 相手の内部継続が王手の2局面循環を、空集合からまとめて追加する。 -/
def cyclicBatch : loopGame.SafeBatch loopStart.won (fun vertex => vertex ∈ [false, true]) where
  fresh := by intro vertex _ impossible; cases impossible
  choice := fun vertex => .node (!vertex)
  chosen_legal := by intro _ _ _; rfl
  safe := by
    intro vertex _ move follows
    have same : move = .node (!vertex) := follows.1
    subst move
    right
    constructor
    · cases vertex <;> decide
    · cases vertex <;> simp [loopGame]

noncomputable def cyclicCertificate : StateCertificate loopIndexed loopAdded :=
  StateCertificate.addBatch loopIndexed loopStart (StateCertificate.initial loopIndexed) [false, true] cyclicBatch

theorem cyclic_batch_sound : SoundRun loopIndexed loopAdded :=
  SoundRun.batch SoundRun.initial [false, true] ⟨cyclicBatch⟩

theorem cyclic_batch_guarantees (root : Bool) : loopGame.LowerGuarantee root 10 := by
  apply cyclic_batch_sound.lower_guarantee loopIndexed root
  change (loopAdded.counters root).admitted = true
  cases root <;> decide

theorem cyclic_batch_same_rank (vertex : Bool) : cyclicCertificate.region.rank vertex = 1 := by
  classical
  cases vertex <;> simp [cyclicCertificate, StateCertificate.addBatch, RankedRegion.reindex,
    RankedRegion.extend, RankedRegion.extendedRank, StateCertificate.initial, RankedRegion.empty]

def loopDone := ((loopAdded.pop.pop).notify loopIndexed false).notify loopIndexed true

/-- 循環集合の投入後に両頂点をpopし、確定済み親への逆辺通知も最後まで処理する。 -/
theorem cyclic_done_sound : SoundRun loopIndexed loopDone := by
  apply SoundRun.node_notification loopIndexed (edge := true) (child := false)
  · apply SoundRun.node_notification loopIndexed
      (SoundRun.pop (SoundRun.pop cyclic_batch_sound)) false true rfl
    · decide
    · decide
  · rfl
  · decide
  · decide

theorem cyclic_done_exact (root : Bool) : loopDone.won root ↔ loopGame.FourfoldWinning root := by
  apply cyclic_done_sound.stopped_exact loopIndexed (by decide)
    (vertices := [false, true]) (core := fun _ => True) (rounds := 0)
  · intro edge score impossible _
    cases impossible
  · intro child _ edge _
    cases edge <;> decide
  · intro vertex
    cases vertex <;> decide
  · intro _ _
    trivial
  · intro vertex survives
    have outside : ¬ loopDone.won vertex := survives.2
    apply outside
    change (loopDone.counters vertex).admitted = true
    cases vertex <;> decide

/-- 循環を形成する2頂点を、空集合から独立な単一追加として扱うことはできない。 -/
theorem cyclic_singleton_not_safe :
    ¬ Nonempty (loopGame.SafeBatch loopStart.won (fun vertex => vertex = false)) := by
  rintro ⟨batch⟩
  have chosen : batch.choice false = .node true := batch.chosen_legal false rfl rfl
  have safe := batch.safe false rfl (.node true) ⟨rfl, fun _ => chosen⟩
  rcases safe with old | ⟨inside, _⟩
  · cases old
  · cases inside

/-- 機械的不変条件だけを満たす強制追加は、悪いleafの値保証を持てない。 -/
theorem unsafe_forced_add_excluded :
    ¬ Nonempty (StateCertificate badLeafIndexed
      ((PropagationState.initial badLeafIndexed).add ())) := by
  rintro ⟨certificate⟩
  have inside : ((PropagationState.initial badLeafIndexed).add ()).won () := rfl
  obtain ⟨move, follows⟩ := certificate.region.has_following_move () inside
  have same : move = .leaf (-20) := follows.1
  subst move
  have good := certificate.region.closed () inside (.leaf (-20)) follows
  change (1 : Int) ≤ -20 at good
  omega

end PetaProof.CertifiedPropagationExamples
