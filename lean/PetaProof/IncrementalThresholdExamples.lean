import PetaProof.IncrementalThreshold

/-! AND親が高いleafの通知を保持したまま、低いleafの通知で確定する増分処理例。 -/
namespace PetaProof.IncrementalThresholdExamples

open ThresholdGame

def andGame : ThresholdGame Unit where
  legal := fun _ move => move = .leaf 30 ∨ move = .leaf 20
  owner := fun _ => true
  check := fun _ _ => False
  player := false
  threshold := 25
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by intro _ _ legal; cases legal with | inl impossible => cases impossible | inr impossible => cases impossible
  nonempty_moves := fun _ => ⟨.leaf 30, Or.inl rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def andIndexed : andGame.IndexedMoves Bool where
  outgoing := fun _ => [false, true]
  source := fun _ => ()
  move := fun edge => if edge then .leaf 20 else .leaf 30
  unique := fun _ => by decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex _ _; cases vertex; rfl
  legal := by intro _ edge _; cases edge <;> simp [andGame]
  covers := by
    intro _ move legal
    rcases legal with high | low
    · exact ⟨false, by decide, high.symm⟩
    · exact ⟨true, by decide, low.symm⟩

def start : PropagationState Unit Bool := PropagationState.initial andIndexed
def highState := start.notify andIndexed false
def lowIndexed := andIndexed.lowerThreshold 10 (by decide) (by decide)
def lowState := highState.notifyMany lowIndexed [true]

theorem high_run : StateCertificate.SoundRun andIndexed highState := by
  apply StateCertificate.SoundRun.leaf_notification andIndexed StateCertificate.SoundRun.initial false 30 rfl
  · rfl
  · decide

noncomputable def highCertificate : StateCertificate andIndexed highState :=
  StateCertificate.notify andIndexed start (StateCertificate.initial andIndexed) false rfl (by change (25 : Int) ≤ 30; decide)

noncomputable def lowCertificate : StateCertificate lowIndexed lowState := by
  apply StateCertificate.advanceLeaves andIndexed highState highCertificate 10 (by decide) (by decide) [true] (by decide)
  intro edge member
  have same : edge = true := by simpa using member
  subst edge
  exact ⟨20, rfl, by decide, by decide⟩

/-- 閾値を変えただけなら、全操作履歴も同じ状態のまま低い閾値で有効である。 -/
theorem retained_run : StateCertificate.SoundRun lowIndexed highState :=
  high_run.lowerThreshold andIndexed 10 (by decide) (by decide)

theorem high_counter_retained : (highState.counters ()).left = 1 ∧
    (highState.counters ()).admitted = false ∧ highState.queue.pending = [] := by decide

theorem low_leaf_is_fresh : highState.notified true = false :=
  StateCertificate.lower_leaf_fresh andIndexed highState highCertificate true 20 rfl (by decide)

theorem low_run : StateCertificate.SoundRun lowIndexed lowState := by
  apply StateCertificate.SoundRun.leaf_notification lowIndexed retained_run true 20 rfl
  · decide
  · decide

/-- カウンターを初期化し直さず、新leafの1回の通知で残数1から0へ進む。 -/
theorem low_counter_finishes : (lowState.counters ()).left = 0 ∧
    (lowState.counters ()).admitted = true ∧ lowState.queue.pending = [()] ∧
    lowState.notified false = true ∧ lowState.notified true = true := by decide

theorem high_state_closed : andGame.OrdinaryClosed highState.won := by
  apply PropagationState.ordinary_closed andIndexed highState highCertificate.invariant (by decide)
  · intro edge score same good
    cases edge with
    | false => decide
    | true =>
      have value : (20 : Int) = score := Move.leaf.inj same
      change (25 : Int) ≤ score at good
      omega
  · intro child impossible
    cases impossible

/-- 空キューは維持されても、新しいleaf通知前に旧停止判定を使い回すことはできない。 -/
theorem lowered_state_not_closed : ¬ (andGame.lowerThreshold 10 (by decide) (by decide)).OrdinaryClosed highState.won := by
  intro closed
  have inside := closed () (Or.inr ⟨by decide, ?_⟩)
  · change (highState.counters ()).admitted = true at inside
    have outside : (highState.counters ()).admitted = false := by decide
    rw [outside] at inside
    cases inside
  · intro move legal
    rcases legal with high | low
    · subst move
      change (10 : Int) ≤ 30
      decide
    · subst move
      change (10 : Int) ≤ 20
      decide

theorem lower_guarantee_after_notification :
    (andGame.lowerThreshold 10 (by decide) (by decide)).LowerGuarantee () 10 :=
  lowCertificate.region.fourfold_winning () rfl

theorem low_leaf_notifications_complete : ∀ edge score, andIndexed.move edge = .leaf score → (10 : Int) ≤ score →
    lowState.notified edge = true := by
  apply StateCertificate.advanceLeaves_complete andIndexed highState 10 (by decide) (by decide) [true]
  · intro edge score same good
    cases edge with
    | false => decide
    | true =>
      have value : (20 : Int) = score := Move.leaf.inj same
      change (25 : Int) ≤ score at good
      omega
  · intro edge score same _ below
    cases edge with
    | false =>
      have value : (30 : Int) = score := Move.leaf.inj same
      change score < (25 : Int) at below
      omega
    | true => decide

def lowDone := lowState.pop

/-- 既存の疎な降順走査の定理へ渡せる、増分処理後の停止証拠。 -/
noncomputable def lowStopped : andGame.StoppedThreshold 10 (by decide) (by decide) := by
  apply StoppedThreshold.ofState 10 (by decide) (by decide) lowIndexed lowDone
    (StateCertificate.pop lowIndexed lowState lowCertificate) (by decide)
    (core := fun _ => True) (rounds := 0)
  · exact low_leaf_notifications_complete
  · intro child _ edge impossible
    cases edge <;> cases impossible
  · intro _ _
    trivial
  · intro vertex survives
    exact survives.2 rfl

theorem low_stopped_exact : lowDone.won () ↔ andGame.LowerGuarantee () 10 :=
  lowStopped.correct [()] (by intro vertex; cases vertex; simp) ()

end PetaProof.IncrementalThresholdExamples
