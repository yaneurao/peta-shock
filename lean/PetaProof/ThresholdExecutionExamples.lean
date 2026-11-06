import PetaProof.ThresholdExecution
import PetaProof.IncrementalThresholdExamples

/-! Mate→30→20の単一実行。AND親の残数1を保持し、最後のleaf通知で確定する。 -/
namespace PetaProof.ThresholdExecutionExamples

open ThresholdGame IncrementalThresholdExamples

def snapshots (level : Int) : PropagationState Unit Bool :=
  if level ≤ 20 then lowDone else if level ≤ 30 then highState else start

def values : Unit → Int := writeAdmission (fun _ => 0) 20 ()

def haltAt (level : Int) (positive : 0 < level) (bounded : level ≤ andGame.mate) :
    HaltConditions (andIndexed.retune level positive bounded) (snapshots level) where
  queue_empty := by
    by_cases low : level ≤ 20
    · simp only [snapshots, if_pos low]
      rfl
    · by_cases high : level ≤ 30
      · simp only [snapshots, if_neg low, if_pos high]
        rfl
      · simp only [snapshots, if_neg low, if_neg high]
        rfl
  leaves_done := by
    intro edge score same good
    change level ≤ score at good
    cases edge with
    | false =>
      have equal : (30 : Int) = score := Move.leaf.inj same
      have high : level ≤ 30 := by omega
      by_cases low : level ≤ 20
      · simp only [snapshots, if_pos low]
        rfl
      · simp only [snapshots, if_neg low, if_pos high]
        rfl
    | true =>
      have equal : (20 : Int) = score := Move.leaf.inj same
      have low : level ≤ 20 := by omega
      simp only [snapshots, if_pos low]
      rfl
  nodes_done := by intro _ _ edge impossible; cases edge <;> cases impossible
  core := fun _ => False
  covers_core := by
    intro vertex cycle
    obtain ⟨child, edge, _⟩ := cycle
    rcases edge.1 with impossible | impossible <;> cases impossible
  rounds := 0
  local_empty := by intro _ impossible; exact impossible.1

/-- 停止点ごとの状態を独立に与えるのではなく、同じ入力・出力で次の段階を接続する。 -/
theorem three_level_execution :
    ThresholdExecution andIndexed snapshots andGame.mate andGame.mate_positive (Int.le_refl _)
      start (fun _ => 0) [32000, 30, 20] lowDone values := by
  apply ThresholdExecution.step (level_positive := by decide) (lower := by decide) (nextValues := fun _ => 0)
  · exact CertifiedPhase.initial
  · exact ⟨haltAt 32000 (by decide) (by decide)⟩
  · apply ThresholdExecution.step (level_positive := by decide) (lower := by decide) (nextValues := fun _ => 0)
    · apply CertifiedPhase.notify (edge := false)
      · exact CertifiedPhase.initial
      · rfl
      · change (30 : Int) ≤ 30
        decide
    · exact ⟨haltAt 30 (by decide) (by decide)⟩
    · apply ThresholdExecution.step (level_positive := by decide) (lower := by decide) (nextValues := values)
      · apply CertifiedPhase.pop
        apply CertifiedPhase.notify (edge := true)
        · exact CertifiedPhase.initial
        · rfl
        · change (20 : Int) ≤ 20
          decide
      · exact ⟨haltAt 20 (by decide) (by decide)⟩
      · exact ThresholdExecution.done

theorem partial_counter_carried : ((snapshots 30).counters ()).left = 1 := by decide
theorem final_counter_zero : ((snapshots 20).counters ()).left = 0 := by decide

theorem leaves_bounded : andGame.BoundedLeaves := by
  intro _ score legal
  change -32000 ≤ score ∧ score ≤ 32000
  rcases legal with high | low
  · have same : score = 30 := Move.leaf.inj high
    omega
  · have same : score = 20 := Move.leaf.inj low
    omega

theorem levels_valid (level : Int) (member : level ∈ [32000, 30, 20]) : andGame.CriticalLevel level := by
  have choices : level = 32000 ∨ level = 30 ∨ level = 20 := by simpa using member
  rcases choices with top | high | low
  · subst level
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · subst level
    exact ⟨by decide, by decide, Or.inr ⟨(), Or.inl rfl⟩⟩
  · subst level
    exact ⟨by decide, by decide, Or.inr ⟨(), Or.inr rfl⟩⟩

theorem levels_cover (level : Int) (critical : andGame.CriticalLevel level) : level ∈ [32000, 30, 20] := by
  rcases critical.2.2 with top | ⟨_, legal⟩
  · have same : level = 32000 := top
    simp [same]
  · rcases legal with high | low
    · have same : level = 30 := Move.leaf.inj high
      simp [same]
    · have same : level = 20 := Move.leaf.inj low
      simp [same]

/-- 同じ実行の操作・記録・全停止条件から、最終記録値20の最大性を導く。 -/
theorem whole_execution_maximum : andGame.PositiveMaximum () 20 := by
  have maximum := three_level_execution.positive_maximum andIndexed snapshots leaves_bounded [()]
    (by intro vertex; cases vertex; simp) levels_valid levels_cover (by decide) ()
  simpa [values, writeAdmission] using maximum

end PetaProof.ThresholdExecutionExamples
