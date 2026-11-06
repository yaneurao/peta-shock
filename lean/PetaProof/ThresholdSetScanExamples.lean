import PetaProof.ThresholdSetScan
import PetaProof.IntegerValueExamples
import PetaProof.ThresholdSetSolverExamples

/-! 集合算法を通した初回記録、正負のleaf、通常千日手と王手千日手の値。 -/
namespace PetaProof.ThresholdSetScanExamples

open ThresholdGame PropagationExamples FinitePayoffExamples IntegerValueExamples SignedBoundsExamples

theorem fixed_computed_value (score : Int) (bounds : -32000 ≤ score ∧ score ≤ 32000) :
    (fixedLeafGame score).computedSetValue [()] (fun _ => False) (fun _ => False) () = score := by
  apply ExactValue.unique (fixedLeafGame score) [()] (by simp) ()
    _ (fixed_exact score)
  apply (fixedLeafGame score).computedSetValue_exact (fixed_leaves_bounded score bounds) [()] (by simp)
  · intro _ ⟨_, edge, _⟩
    cases edge.1
  · intro _ ⟨_, edge, _⟩
    cases edge.1

theorem positive_twenty :
    (fixedLeafGame 20).computedSetValue [()] (fun _ => False) (fun _ => False) () = 20 :=
  fixed_computed_value 20 (by decide)

theorem negative_twenty :
    (fixedLeafGame (-20)).computedSetValue [()] (fun _ => False) (fun _ => False) () = -20 :=
  fixed_computed_value (-20) (by decide)

theorem zero_leaf :
    (fixedLeafGame 0).computedSetValue [()] (fun _ => False) (fun _ => False) () = 0 :=
  fixed_computed_value 0 (by decide)

theorem positive_mate :
    (fixedLeafGame 32000).computedSetValue [()] (fun _ => False) (fun _ => False) () = 32000 :=
  fixed_computed_value 32000 (by decide)

theorem negative_mate :
    (fixedLeafGame (-32000)).computedSetValue [()] (fun _ => False) (fun _ => False) () = -32000 :=
  fixed_computed_value (-32000) (by decide)

def vertices : List Bool := [false, true]
theorem covered (v : Bool) : v ∈ vertices := by cases v <;> simp [vertices]

theorem opponent_checks (v : Bool) :
    loopGame.computedSetValue vertices (fun _ => True) (fun _ => True) v = 32000 := by
  apply ExactValue.unique loopGame vertices covered v _ (opponent_checks_value v)
  exact loopGame.computedSetValue_exact (by intro _ _ impossible; cases impossible) vertices covered
    (fun _ => True) (fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial) v

theorem own_checks (v : Bool) :
    ownCheckingGame.computedSetValue vertices (fun _ => True) (fun _ => True) v = -32000 := by
  apply ExactValue.unique ownCheckingGame vertices covered v _ (own_checks_value v)
  exact ownCheckingGame.computedSetValue_exact (by intro _ _ impossible; cases impossible) vertices covered
    (fun _ => True) (fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial) v

theorem ordinary_draw (v : Bool) :
    drawUnit.computedSetValue vertices (fun _ => True) (fun _ => True) v = 0 := by
  apply ExactValue.unique drawUnit vertices covered v _ (draw_exact_zero v)
  exact drawUnit.computedSetValue_exact (by intro _ _ impossible; cases impossible) vertices covered
    (fun _ => True) (fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial) v

/-- 同じ局面が後の閾値でも確定済みであっても、20を10へ下げない。 -/
theorem inherited_value_unchanged :
    ((fixedLeafGame 20).scanSets [()] (fun _ => False) [10]
      (by
        intro t member
        have same : t = 10 := by simpa using member
        subst t
        decide)
      (fun _ => True) (fun _ => 20)).2 () = 20 := by
  apply (fixedLeafGame 20).scanSets_keeps_nonzero
  decide

theorem fixed_flags (score t : Int) : (fixedLeafGame score).guaranteeFlags t () = decide (t ≤ score) := by
  classical
  unfold guaranteeFlags
  simp only [ExactValue.lower_iff (fixedLeafGame score) [()] (by simp) () (fixed_exact score) t]

def threeLevels : List Int := [32000, 20, 10]
theorem three_valid : ∀ t ∈ threeLevels, 0 < t ∧ t ≤ (fixedLeafGame 20).mate := by
  intro t member
  simp only [threeLevels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> subst t <;> decide

/-- 上限では未確定、20で初回確定、10でも残る、という一続きの実行で20を記録する。 -/
theorem first_record_is_twenty :
    (fixedLeafGame 20).positiveSetValues [()] (fun _ => False) threeLevels three_valid () = 20 := by
  have run := (fixedLeafGame 20).scanSets_values [()] (by simp) (fun _ => False)
    (by intro _ ⟨_, edge, _⟩; cases edge.1) threeLevels three_valid (by decide)
    32000 (by decide) (by decide) (fun t member => (three_valid t member).2)
    (RankedRegion.empty (G := (fixedLeafGame 20).retune 32000 (by decide) (by decide))) (fun _ => 0)
  unfold positiveSetValues
  rw [run, scanValues_initial threeLevels _ (fun t member => (three_valid t member).1)]
  simp [threeLevels, firstWinning, fixed_flags]

end PetaProof.ThresholdSetScanExamples
