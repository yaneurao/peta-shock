import PetaProof.ThresholdSchedule
import PetaProof.IntegerValueExamples

/-! 大きな閾値の空白、leafのない王手循環、通常千日手と0の境界を検査する。 -/
namespace PetaProof.SparseThresholdExamples

open ThresholdGame PropagationExamples IntegerValueExamples SignedBoundsExamples

def leaf20Levels : List Int := [32000, 20]
def leaf20Oracle (level : Int) : Bool := decide (level ≤ 20)

theorem leaf20_critical_iff (level : Int) :
    (fixedLeafGame 20).CriticalLevel level ↔ level = 32000 ∨ level = 20 := by
  constructor
  · rintro ⟨_, _, top | ⟨v, leaf⟩⟩
    · exact Or.inl top
    · exact Or.inr (Move.leaf.inj leaf)
  · rintro (top | leaf)
    · subst level
      exact ⟨by decide, by decide, Or.inl rfl⟩
    · subst level
      exact ⟨by decide, by decide, Or.inr ⟨(), rfl⟩⟩

theorem leaf20_valid : ∀ level ∈ leaf20Levels, (fixedLeafGame 20).CriticalLevel level := by
  intro level member
  exact (leaf20_critical_iff level).mpr (by simpa [leaf20Levels] using member)

theorem leaf20_covers : ∀ level, (fixedLeafGame 20).CriticalLevel level → level ∈ leaf20Levels := by
  intro level critical
  simpa [leaf20Levels] using (leaf20_critical_iff level).mp critical

theorem leaf20_oracle_correct (level : Int) :
    leaf20Oracle level = true ↔ (fixedLeafGame 20).LowerGuarantee () level := by
  change decide (level ≤ 20) = true ↔ _
  simp only [decide_eq_true_eq]
  exact (ExactValue.lower_iff (fixedLeafGame 20) [()] (by simp) () (fixed_exact 20) level).symm

theorem leaf20_sparse_maximum :
    (fixedLeafGame 20).PositiveMaximum () (firstWinning leaf20Oracle leaf20Levels) :=
  (fixedLeafGame 20).firstWinning_complete (fixed_leaves_bounded 20 (by decide)) [()] (by simp)
    leaf20Levels leaf20_valid leaf20_covers (by decide) leaf20Oracle ()
    (fun level _ => leaf20_oracle_correct level)

theorem leaf20_scan_returns_twenty : firstWinning leaf20Oracle leaf20Levels = 20 := by decide

/-- 実際の降順ループと同じ列を作り、空バケットを省略する小さな計算例。 -/
theorem schedule_skips_empty_buckets :
    processedLevels 5 (fun level => decide (level = 2)) = [5, 2] := by decide

theorem schedule_keeps_mate_without_leaf : processedLevels 5 (fun _ => false) = [5] := by decide

theorem schedule_does_not_duplicate_mate :
    processedLevels 5 (fun level => decide (level = 5 ∨ level = 2)) = [5, 2] := by decide

theorem leaf20_buckets_correct (level : Int) :
    decide (level = 20) = true ↔ ∃ v, (fixedLeafGame 20).legal v (.leaf level) := by
  simp only [decide_eq_true_eq]
  constructor
  · intro same
    subst level
    exact ⟨(), rfl⟩
  · rintro ⟨_, legal⟩
    exact Move.leaf.inj legal

/-- 32000から1までの整数走査を省略した列でも、最大正閾値の仕様を満たす。 -/
theorem leaf20_canonical_schedule : (fixedLeafGame 20).PositiveMaximum ()
    (firstWinning leaf20Oracle (processedLevels 32000 (fun level => decide (level = 20)))) :=
  (fixedLeafGame 20).processed_scan_complete (fixed_leaves_bounded 20 (by decide)) [()] (by simp)
    (fun level => decide (level = 20)) (fun level _ _ => leaf20_buckets_correct level) leaf20Oracle ()
    (fun level _ => leaf20_oracle_correct level)

theorem leaf20_canonical_returns_twenty :
    firstWinning leaf20Oracle (processedLevels 32000 (fun level => decide (level = 20))) = 20 := by
  let game := fixedLeafGame 20
  let value := firstWinning leaf20Oracle (processedLevels 32000 (fun level => decide (level = 20)))
  have leaves := fixed_leaves_bounded 20 (by decide)
  have lower : (20 : Int) ≤ value := PositiveMaximum.is_largest game leaves [()] (by simp) ()
    leaf20_canonical_schedule 20 (by decide) (fixed_exact 20).1
  have exact := PositiveMaximum.exact_of_positive game leaves [()] (by simp) () leaf20_canonical_schedule (by omega)
  exact ExactValue.unique game [()] (by simp) () exact (fixed_exact 20)

/-- 唯一のleafを持つ例で、勝敗の正しさを仮定せず抽象停止証拠を直接構成する。 -/
def fixedLeafStopped (score level : Int) (positive : 0 < level) (bounded : level ≤ 32000) :
    (fixedLeafGame score).StoppedThreshold level positive bounded where
  won := fun _ => level ≤ score
  sound := {
    choice := fun _ => .leaf score
    rank := fun _ => 0
    stage := 0
    rank_bound := fun _ _ => Nat.le_refl _
    chosen_legal := fun _ _ _ => rfl
    closed := by
      intro _ inside m follows
      have same : m = .leaf score := follows.1
      subst m
      exact inside
    decreasing := by intro _ _ _ follows; cases follows.1
    opponent_strict := by intro _ _ _ follows _ _; cases follows.1
  }
  ordinary := by
    intro _ ordinary
    rcases ordinary with ⟨_, m, legal, good⟩ | ⟨other, _⟩
    · have same : m = .leaf score := legal
      subst m
      exact good
    · exact False.elim (other rfl)
  core := fun _ => False
  covers_core := by intro _ ⟨_, edge, _⟩; cases edge.1
  rounds := 0
  empty := by intro _ candidate; exact candidate.1

/-- 既存の通常伝播・局所削除の停止条件から、疎な走査の最大値までを一つの定理で接続する。 -/
theorem leaf20_sparse_from_stops :
    (fixedLeafGame 20).PositiveMaximum () (firstWinning leaf20Oracle leaf20Levels) := by
  apply (fixedLeafGame 20).firstWinning_from_stops (fixed_leaves_bounded 20 (by decide)) [()] (by simp)
    leaf20Levels leaf20_valid leaf20_covers (by decide)
    (fun level member => fixedLeafStopped 20 level (leaf20_valid level member).1 (leaf20_valid level member).2.1)
    leaf20Oracle ()
  intro level _
  change decide (level ≤ 20) = true ↔ level ≤ 20
  simp only [decide_eq_true_eq]

/-- 1から20までを個別に解かず、20だけ調べても全ての勝敗が分かる。 -/
theorem leaf20_whole_gap :
    (fixedLeafGame 20).LowerGuarantee () 1 ↔ (fixedLeafGame 20).LowerGuarantee () 20 := by
  apply (fixedLeafGame 20).lower_same_cut (by decide) (by decide) (by decide) (by decide)
  apply (fixedLeafGame 20).same_leaf_cut_of_gap (by decide)
  intro _ score legal between
  have same : score = 20 := Move.leaf.inj legal
  omega

theorem leaf20_empty_bucket :
    (fixedLeafGame 20).LowerGuarantee () 19 ↔ (fixedLeafGame 20).LowerGuarantee () 20 := by
  apply (fixedLeafGame 20).lower_step_no_leaf 19 (by decide) (by decide)
  intro _ legal
  have impossible : (19 : Int) = 20 := Move.leaf.inj legal
  omega

theorem loop_only_mate_critical (level : Int) : loopGame.CriticalLevel level ↔ level = 32000 := by
  constructor
  · rintro ⟨_, _, top | ⟨v, impossible⟩⟩
    · exact top
    · cases impossible
  · intro same
    subst level
    exact loopGame.mate_critical

/-- leafが一つもない王手循環でも、Mateを最初に調べるため正しい値を拾える。 -/
theorem checking_loop_sparse_maximum (root : Bool) : loopGame.PositiveMaximum root 32000 := by
  have valid : ∀ level ∈ ([32000] : List Int), loopGame.CriticalLevel level := by
    intro level member
    exact (loop_only_mate_critical level).mpr (by simpa using member)
  have covers : ∀ level, loopGame.CriticalLevel level → level ∈ ([32000] : List Int) := by
    intro level critical
    simpa using (loop_only_mate_critical level).mp critical
  have correct : ∀ level ∈ ([32000] : List Int), (true : Bool) = true ↔ loopGame.LowerGuarantee root level := by
    intro level member
    have same : level = 32000 := by simpa using member
    subst level
    exact ⟨fun _ => (opponent_checks_value root).1, fun _ => rfl⟩
  have result := loopGame.firstWinning_complete (by intro _ _ impossible; cases impossible)
    [false, true] (by intro v; cases v <;> simp) [32000] valid covers (by decide)
    (fun _ => true) root correct
  simpa [firstWinning] using result

theorem draw_only_mate_critical (level : Int) : drawUnit.CriticalLevel level ↔ level = 32000 := by
  constructor
  · rintro ⟨_, _, top | ⟨v, impossible⟩⟩
    · exact top
    · cases impossible
  · intro same
    subst level
    exact drawUnit.mate_critical

theorem ordinary_draw_sparse_maximum (root : Bool) : drawUnit.PositiveMaximum root 0 := by
  have valid : ∀ level ∈ ([32000] : List Int), drawUnit.CriticalLevel level := by
    intro level member
    exact (draw_only_mate_critical level).mpr (by simpa using member)
  have covers : ∀ level, drawUnit.CriticalLevel level → level ∈ ([32000] : List Int) := by
    intro level critical
    simpa using (draw_only_mate_critical level).mp critical
  have correct : ∀ level ∈ ([32000] : List Int), (false : Bool) = true ↔ drawUnit.LowerGuarantee root level := by
    intro level member
    have same : level = 32000 := by simpa using member
    subst level
    constructor
    · intro impossible
      cases impossible
    · intro winning
      have impossible := (ExactValue.lower_iff drawUnit [false, true] (by intro v; cases v <;> simp)
        root (draw_exact_zero root) 32000).mp winning
      omega
  have result := drawUnit.firstWinning_complete (by intro _ _ impossible; cases impossible)
    [false, true] (by intro v; cases v <;> simp) [32000] valid covers (by decide)
    (fun _ => false) root correct
  simpa [firstWinning] using result

/-- 0と1を同じ区間として省略してはいけない。leafがなくても通常千日手の合否が変わる。 -/
theorem zero_boundary_is_different (root : Bool) :
    drawUnit.SameLeafCut 0 1 ∧ drawUnit.LowerGuarantee root 0 ∧ ¬ drawUnit.LowerGuarantee root 1 := by
  refine ⟨?_, (draw_exact_zero root).1, ?_⟩
  · intro _ _ impossible
    cases impossible
  · intro winning
    have impossible := (ExactValue.lower_iff drawUnit [false, true] (by intro v; cases v <;> simp)
      root (draw_exact_zero root) 1).mp winning
    omega

end PetaProof.SparseThresholdExamples
