import PetaProof.IntegerValue

/-!
両側の正の勝利閾値の最大値a,bを組み合わせ、固定プレイヤー視点の値a-bを保証する。
本番の閾値の省略や配列処理ではなく、それらが満たすべき集合・数値仕様を表す。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V) [DecidableEq V]

/-- 正の勝利閾値がなければ0、それ以外は最大の勝利閾値。
上端Mateでは次の閾値を要求しない。 -/
structure PositiveMaximum (root : V) (value : Int) : Prop where
  nonnegative : 0 ≤ value
  bounded : value ≤ G.mate
  zero : value = 0 → ¬ G.LowerGuarantee root 1
  wins : 0 < value → G.LowerGuarantee root value
  next : 0 < value → value < G.mate → ¬ G.LowerGuarantee root (value + 1)

/-- 下限と上限の両戦略がある値より、1だけ大きい下限は保証できない。 -/
theorem ExactValue.not_above (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    {value : Int} (exact : G.ExactValue root value) : ¬ G.LowerGuarantee root (value + 1) := by
  rintro ⟨self, lower⟩
  obtain ⟨opponent, upper⟩ := exact.2
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
  have lo := lower opponent payoff result
  have hi := upper self payoff result
  omega

theorem PositiveMaximum.exact_of_positive (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {value : Int}
    (maximum : G.PositiveMaximum root value) (positive : 0 < value) : G.ExactValue root value := by
  apply G.exact_at_positive_boundary leaves vertices covered root value positive maximum.bounded (maximum.wins positive)
  by_cases top : value = G.mate
  · exact Or.inl top
  · exact Or.inr (maximum.next positive (by have := maximum.bounded; omega))

/-- 直後の整数閾値に勝てないという境界条件だけで、より高い勝利閾値も全て排除できる。 -/
theorem PositiveMaximum.is_largest (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {value : Int}
    (maximum : G.PositiveMaximum root value) (level : Int) (positive : 0 < level)
    (winning : G.LowerGuarantee root level) : level ≤ value := by
  by_cases pos : 0 < value
  · have exact := PositiveMaximum.exact_of_positive G leaves vertices covered root maximum pos
    obtain ⟨self, lower⟩ := winning
    obtain ⟨opponent, upper⟩ := exact.2
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    exact Int.le_trans (lower opponent payoff result) (upper self payoff result)
  · have zero : value = 0 := by have := maximum.nonnegative; omega
    apply False.elim
    apply maximum.zero zero
    obtain ⟨self, lower⟩ := winning
    refine ⟨self, ?_⟩
    intro opponent payoff result
    have lo := lower opponent payoff result
    omega

/-- 2本の正閾値の最大値が同時に正になることはない。 -/
theorem positive_maxima_exclusive (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {a b : Int}
    (own : G.PositiveMaximum root a) (other : G.opposite.PositiveMaximum root b) : a = 0 ∨ b = 0 := by
  by_cases apos : 0 < a
  · right
    by_cases bpos : 0 < b
    · have exact_a := PositiveMaximum.exact_of_positive G leaves vertices covered root own apos
      have exact_b := PositiveMaximum.exact_of_positive G.opposite
        (G.opposite_bounded_leaves leaves) vertices covered root other bpos
      have same := ExactValue.unique G vertices covered root exact_a (ExactValue.of_opposite G root b exact_b)
      omega
    · have := other.nonnegative
      omega
  · left
    have := own.nonnegative
    omega

/-- 有限個の正の閾値を考えれば、この仕様を満たす最大値が存在する。 -/
theorem positive_maximum_exists (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    ∃ value, G.PositiveMaximum root value := by
  classical
  by_cases positive : G.LowerGuarantee root 1
  · obtain ⟨value, pos, bound, exact⟩ := G.positive_exact_exists leaves vertices covered root positive
    refine ⟨value, ⟨by omega, bound, ?_, fun _ => exact.1, ?_⟩⟩
    · intro zero
      omega
    · intro _ _
      exact ExactValue.not_above G vertices covered root exact
  · exact ⟨0, ⟨by decide, by have := G.mate_positive; omega, fun _ => positive,
      fun impossible => False.elim (by omega), fun impossible => False.elim (by omega)⟩⟩

theorem exact_zero_of_no_lower (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (own : ¬ G.LowerGuarantee root 1) (other : ¬ G.opposite.LowerGuarantee root 1) : G.ExactValue root 0 := by
  have positive := G.mate_positive
  have upper := G.upper_of_not_lower vertices covered root 1 (by decide) (by omega) own
  have other_upper := G.opposite.upper_of_not_lower vertices covered root 1 (by decide)
    (by change 1 ≤ G.mate; omega) other
  have lower := G.lower_of_opposite_upper root 0 (by simpa using other_upper)
  exact ⟨by simpa using lower, by simpa using upper⟩

/-- 両者の最大正閾値を持つとき、a-bが元の有限ゲームの整数最適値となる。 -/
theorem merge_positive_maxima (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) {a b : Int}
    (own : G.PositiveMaximum root a) (other : G.opposite.PositiveMaximum root b) :
    G.ExactValue root (a - b) := by
  by_cases apos : 0 < a
  · have exact_a := PositiveMaximum.exact_of_positive G leaves vertices covered root own apos
    have bzero : b = 0 := by
      rcases G.positive_maxima_exclusive leaves vertices covered root own other with zero | zero
      · omega
      · exact zero
    simpa only [bzero, Int.sub_zero] using exact_a
  · have azero : a = 0 := by have := own.nonnegative; omega
    by_cases bpos : 0 < b
    · have exact_b := PositiveMaximum.exact_of_positive G.opposite
        (G.opposite_bounded_leaves leaves) vertices covered root other bpos
      simpa only [azero, Int.zero_sub] using ExactValue.of_opposite G root b exact_b
    · have bzero : b = 0 := by have := other.nonnegative; omega
      simpa only [azero, bzero, Int.sub_self] using
        G.exact_zero_of_no_lower vertices covered root (own.zero azero) (other.zero bzero)

/-- 両側の正閾値からの値の構成は、全局面で可能である。 -/
theorem value_assembly_exists (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    ∃ a b, G.PositiveMaximum root a ∧ G.opposite.PositiveMaximum root b ∧
      G.ExactValue root (a - b) := by
  obtain ⟨a, own⟩ := G.positive_maximum_exists leaves vertices covered root
  obtain ⟨b, other⟩ := G.opposite.positive_maximum_exists
    (G.opposite_bounded_leaves leaves) vertices covered root
  exact ⟨a, b, own, other, G.merge_positive_maxima leaves vertices covered root own other⟩

end PetaProof.ThresholdGame
