import PetaProof.RecordedPhase
import PetaProof.PropagationStateExamples
import PetaProof.IntegerValueExamples

/-! 初回値の保持、単一書込み列、実行状態の停止証拠から最大正値までの検査。 -/
namespace PetaProof.RecordedValueExamples

open ThresholdGame PropagationStateExamples CounterQueueExamples IntegerValueExamples

def levels : List Int := [32000, 30, 20]
def confirmed (level : Int) (vertex : Nat) : Bool :=
  if vertex = 0 then decide (level ≤ 30) else if vertex = 1 then decide (level ≤ 20) else false
def recorded := scanValues levels confirmed (fun _ => 0)

theorem first_value_is_kept : recorded 0 = 30 ∧ recorded 1 = 20 ∧ recorded 2 = 0 := by decide

theorem repeated_admission_keeps_value :
    writeAdmissions (fun _ : Nat => 0) 30 [0, 1, 0] 0 = 30 ∧
    writeAdmissions (fun _ : Nat => 0) 30 [0, 1, 0] 1 = 30 := by decide

theorem old_value_is_not_overwritten :
    writeAdmissions (fun vertex : Nat => if vertex = 0 then 100 else 0) 20 [0, 1] 0 = 100 ∧
    writeAdmissions (fun vertex : Nat => if vertex = 0 then 100 else 0) 20 [0, 1] 1 = 20 := by decide

def parentValues : Bool → Int := writeAdmission (writeAdmission (fun _ => 0) 10 false) 10 true

theorem parent_recorded_phase : RecordedPhase parentIndexed 10 start (fun _ => 0) finished parentValues := by
  apply RecordedPhase.pop
  apply RecordedPhase.notify (edge := ParentEdge.second)
  apply RecordedPhase.notify (edge := ParentEdge.first)
  apply RecordedPhase.pop
  apply RecordedPhase.notify (edge := ParentEdge.exit)
  exact RecordedPhase.initial

theorem parent_recorded_phase_correct :
    (∀ vertex, finished.won vertex ↔ parentValues vertex ≠ 0) ∧
      parentValues = latchValues (fun _ => 0) 10 (fun vertex => (finished.counters vertex).admitted) :=
  parent_recorded_phase.invariants parentIndexed 10 (by decide) start (fun _ => 0)
    (by intro vertex; simp [PropagationState.won, start, PropagationState.initial, HitCounter.initial])

def leafGame := fixedLeafGame 20

def leafIndexedAt (level : Int) (positive : 0 < level) (bounded : level ≤ leafGame.mate) :
    (leafGame.retune level positive bounded).IndexedMoves Unit where
  outgoing := fun _ => [()]
  source := fun _ => ()
  move := fun _ => .leaf 20
  unique := fun _ => by decide
  at_source := fun _ => by simp
  source_of_mem := by intro vertex _ _; cases vertex; rfl
  legal := fun _ _ _ => rfl
  covers := by intro _ move legal; exact ⟨(), by simp, legal.symm⟩

def leafStart : PropagationState Unit Unit := PropagationState.initial (leafIndexedAt 1 (by decide) (by decide))
def leafDone := (leafStart.notify (leafIndexedAt 1 (by decide) (by decide)) ()).pop
def leafStates (level : Int) := if level ≤ 20 then leafDone else leafStart

noncomputable def leafCertificateAt (level : Int) (positive : 0 < level) (bounded : level ≤ leafGame.mate) :
    StateCertificate (leafIndexedAt level positive bounded) (leafStates level) := by
  by_cases good : level ≤ 20
  · have certificate : StateCertificate (leafIndexedAt level positive bounded) leafDone := by
      apply StateCertificate.pop
      apply StateCertificate.notify (edge := ())
      · exact StateCertificate.initial (leafIndexedAt level positive bounded)
      · rfl
      · exact good
    simpa only [leafStates, if_pos good] using certificate
  · simpa only [leafStates, if_neg good] using StateCertificate.initial (leafIndexedAt level positive bounded)

noncomputable def leafStopAt (level : Int) (positive : 0 < level) (bounded : level ≤ leafGame.mate) :
    leafGame.StoppedThreshold level positive bounded := by
  apply StoppedThreshold.ofState level positive bounded (leafIndexedAt level positive bounded) (leafStates level)
    (leafCertificateAt level positive bounded) (core := fun _ => False) (rounds := 0)
  · by_cases good : level ≤ 20
    · simp only [leafStates, if_pos good]
      rfl
    · simp only [leafStates, if_neg good]
      rfl
  · intro edge score same good
    have value : (20 : Int) = score := Move.leaf.inj same
    have eligible : level ≤ 20 := by omega
    simp only [leafStates, if_pos eligible]
    rfl
  · intro _ _ edge impossible
    cases impossible
  · intro vertex cycle
    obtain ⟨child, edge, _⟩ := cycle
    cases edge.1
  · intro _ impossible
    exact impossible.1

def leafLevels : List Int := [32000, 20]

theorem leaf_levels_valid (level : Int) (member : level ∈ leafLevels) : leafGame.CriticalLevel level := by
  have choices : level = 32000 ∨ level = 20 := by simpa [leafLevels] using member
  rcases choices with high | low
  · subst level
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · subst level
    exact ⟨by decide, by decide, Or.inr ⟨(), rfl⟩⟩

theorem leaf_levels_cover (level : Int) (critical : leafGame.CriticalLevel level) : level ∈ leafLevels := by
  rcases critical.2.2 with top | ⟨vertex, legal⟩
  · have same : level = 32000 := top
    simp [leafLevels, same]
  · have same : level = 20 := Move.leaf.inj legal
    simp [leafLevels, same]

/-- 値の正しさを仮定せず、実際に構成した状態の停止証拠から、記録値20の最大性を導く。 -/
theorem recorded_leaf_maximum : leafGame.PositiveMaximum () 20 := by
  have maximum := leafGame.recorded_from_stops (fixed_leaves_bounded 20 (by decide)) [()] (by intro vertex; cases vertex; simp)
    leafLevels leaf_levels_valid leaf_levels_cover (by decide) leafStates
    (fun level member => leafStopAt level (leaf_levels_valid level member).1 (leaf_levels_valid level member).2.1)
    (by intro _ _ _; rfl) ()
  have value : scanValues leafLevels (fun level vertex => ((leafStates level).counters vertex).admitted) (fun _ => 0) () = 20 := by decide
  simpa only [value] using maximum

end PetaProof.RecordedValueExamples
