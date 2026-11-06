import PetaProof.ThresholdEvents

/-!
Mateと正のleaf値だけを高い順に調べる閾値走査。
各処理閾値の勝敗判定が正しいという明示的な前提のもとで、全整数の最大正閾値と一致する。
-/

namespace PetaProof

/-- 高い順の閾値列から、最初に勝てる閾値を返す。勝てる閾値がなければ0。 -/
def firstWinning (wins : Int → Bool) : List Int → Int
  | [] => 0
  | level :: rest => if wins level then level else firstWinning wins rest

/-- 降順走査の結果は、処理した閾値内の最大の勝利値である。 -/
theorem firstWinning_spec (wins : Int → Bool) (levels : List Int)
    (positive : ∀ level ∈ levels, 0 < level)
    (descending : levels.Pairwise (fun a b => b < a)) :
    0 ≤ firstWinning wins levels ∧
      (firstWinning wins levels = 0 ∨ firstWinning wins levels ∈ levels) ∧
      (0 < firstWinning wins levels → wins (firstWinning wins levels) = true) ∧
      ∀ level ∈ levels, firstWinning wins levels < level → ¬ wins level = true := by
  induction levels with
  | nil => simp [firstWinning]
  | cons head rest ih =>
    by_cases chosen : wins head = true
    · have head_positive := positive head (by simp)
      simp only [firstWinning, if_pos chosen]
      refine ⟨by omega, Or.inr (by simp), fun _ => chosen, ?_⟩
      intro level member above
      rcases List.mem_cons.mp member with same | tail
      · omega
      · have less := List.rel_of_pairwise_cons descending tail
        omega
    · have tail_positive : ∀ level ∈ rest, 0 < level := fun level member => positive level (by simp [member])
      obtain ⟨nonneg, found, winner, maximal⟩ := ih tail_positive descending.of_cons
      simp only [firstWinning, if_neg chosen]
      refine ⟨nonneg, ?_, winner, ?_⟩
      · rcases found with zero | member
        · exact Or.inl zero
        · exact Or.inr (by simp [member])
      · intro level member above
        rcases List.mem_cons.mp member with same | tail
        · subst level
          exact chosen
        · exact maximal level tail above

namespace ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V) [DecidableEq V]

/-- 処理した閾値上だけで最大性を検査する、疎な走査の結果の仕様。 -/
structure SparseMaximum (root : V) (value : Int) : Prop where
  nonnegative : 0 ≤ value
  bounded : value ≤ G.mate
  critical : 0 < value → G.CriticalLevel value
  wins : 0 < value → G.LowerGuarantee root value
  maximal : ∀ level, G.CriticalLevel level → value < level → ¬ G.LowerGuarantee root level

/-- 疎な閾値集合での最大値が、全正整数閾値での最大値に一致する。 -/
theorem SparseMaximum.complete (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {value : Int}
    (sparse : G.SparseMaximum root value) : G.PositiveMaximum root value := by
  obtain ⟨actual, maximum⟩ := G.positive_maximum_exists leaves vertices covered root
  have lower : value ≤ actual := by
    by_cases positive : 0 < value
    · exact PositiveMaximum.is_largest G leaves vertices covered root maximum value positive (sparse.wins positive)
    · have := sparse.nonnegative
      have := maximum.nonnegative
      omega
  have upper : actual ≤ value := by
    by_cases positive : 0 < actual
    · apply Classical.byContradiction
      intro above
      exact sparse.maximal actual (PositiveMaximum.critical G root maximum positive)
        (by omega) (maximum.wins positive)
    · have := sparse.nonnegative
      have := maximum.nonnegative
      omega
  have same : value = actual := Int.le_antisymm lower upper
  simpa only [same] using maximum

/-- 降順に並んだ処理閾値と、その各閾値における正しい勝敗判定を疎な最大値仕様へ接続する。 -/
theorem firstWinning_sparse (levels : List Int)
    (valid : ∀ level ∈ levels, G.CriticalLevel level)
    (covered : ∀ level, G.CriticalLevel level → level ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a))
    (wins : Int → Bool) (root : V)
    (correct : ∀ level ∈ levels, wins level = true ↔ G.LowerGuarantee root level) :
    G.SparseMaximum root (firstWinning wins levels) := by
  obtain ⟨nonneg, found, winner, maximal⟩ := firstWinning_spec wins levels
    (fun level member => (valid level member).1) descending
  have member (positive : 0 < firstWinning wins levels) : firstWinning wins levels ∈ levels := by
    rcases found with zero | present
    · omega
    · exact present
  exact {
    nonnegative := nonneg
    bounded := by
      rcases found with zero | present
      · rw [zero]
        have := G.mate_positive
        omega
      · exact (valid _ present).2.1
    critical := fun positive => valid _ (member positive)
    wins := fun positive => (correct _ (member positive)).mp (winner positive)
    maximal := by
      intro level critical above winning
      have present := covered level critical
      exact maximal level present above ((correct level present).mpr winning)
  }

/-- C++型の閾値省略の抽象仕様。処理対象の全閾値を網羅し正しく解けば、省略で値を失わない。 -/
theorem firstWinning_complete (leaves : G.BoundedLeaves)
    (vertices : List V) (vertices_cover : ∀ v, v ∈ vertices)
    (levels : List Int) (valid : ∀ level ∈ levels, G.CriticalLevel level)
    (levels_cover : ∀ level, G.CriticalLevel level → level ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a))
    (wins : Int → Bool) (root : V)
    (correct : ∀ level ∈ levels, wins level = true ↔ G.LowerGuarantee root level) :
    G.PositiveMaximum root (firstWinning wins levels) :=
  SparseMaximum.complete G leaves vertices vertices_cover root
    (G.firstWinning_sparse levels valid levels_cover descending wins root correct)

/-- 両側で疎な走査をしても、その差は全整数閾値から得る最適値と一致する。 -/
theorem merge_sparse_maxima (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {a b : Int}
    (own : G.SparseMaximum root a) (other : G.opposite.SparseMaximum root b) :
    G.ExactValue root (a - b) :=
  G.merge_positive_maxima leaves vertices covered root
    (SparseMaximum.complete G leaves vertices covered root own)
    (SparseMaximum.complete G.opposite (G.opposite_bounded_leaves leaves) vertices covered root other)

end ThresholdGame
end PetaProof
