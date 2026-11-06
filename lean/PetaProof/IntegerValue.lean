import PetaProof.ThresholdChange

/-!
leafの値域を明示し、正の勝利閾値の最大値から整数最適値を構成する。
これは抽象解法の存在・完全性の証明であり、本番で全戦略を列挙する実装ではない。
-/

namespace PetaProof

/-- 有限個の自然数の候補が一つでもあれば、その中に最大候補がある。 -/
theorem largest_bounded_nat (P : Nat → Prop) (cap : Nat) (exists_candidate : ∃ n, n ≤ cap ∧ P n) :
    ∃ n, n ≤ cap ∧ P n ∧ ∀ k, k ≤ cap → P k → k ≤ n := by
  classical
  induction cap with
  | zero =>
    obtain ⟨n, bound, good⟩ := exists_candidate
    have same : n = 0 := by omega
    subst n
    exact ⟨0, Nat.le_refl _, good, fun _ h _ => h⟩
  | succ cap ih =>
    by_cases top : P (cap + 1)
    · exact ⟨cap + 1, Nat.le_refl _, top, fun _ h _ => h⟩
    · have smaller : ∃ n, n ≤ cap ∧ P n := by
        obtain ⟨n, bound, good⟩ := exists_candidate
        exact ⟨n, by
          have ne : n ≠ cap + 1 := fun same => top (same ▸ good)
          omega, good⟩
      obtain ⟨n, bound, good, largest⟩ := ih smaller
      refine ⟨n, by omega, good, ?_⟩
      intro k kbound kgood
      have ne : k ≠ cap + 1 := fun same => top (same ▸ kgood)
      exact largest k (by omega) kgood

namespace ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V) [DecidableEq V]

/-- 反則負けの値だけでなく、入力leafの値も同じ区間内にあることを要求する。 -/
def BoundedLeaves : Prop := ∀ v score, G.legal v (.leaf score) → -G.mate ≤ score ∧ score ≤ G.mate

omit [DecidableEq V] in
theorem mate_positive : 0 < G.mate := Int.lt_of_lt_of_le G.positive G.bounded

theorem TerminalResult.payoff_bounded (leaves : G.BoundedLeaves)
    {plan : G.MovePlan} {root : V} {payoff : Int} (result : G.TerminalResult plan root payoff) :
    -G.mate ≤ payoff ∧ payoff ≤ G.mate := by
  classical
  apply TerminalResult.property G result (fun _ => True) (fun _ _ => True)
    (fun score => -G.mate ≤ score ∧ score ≤ G.mate) trivial
  · intro _ v m _ legal _
    cases m with
    | node _ => exact ⟨trivial, trivial⟩
    | leaf score => exact leaves v score legal
  · intro a b edge back _
    have positive := G.mate_positive
    unfold repetitionValue
    dsimp only
    split
    · constructor <;> omega
    · split <;> constructor <;> omega

theorem lower_mate_bound (leaves : G.BoundedLeaves) (root : V) : G.LowerGuarantee root (-G.mate) := by
  refine ⟨G.defaultPlan, ?_⟩
  intro opponent payoff result
  exact (TerminalResult.payoff_bounded G leaves result).1

theorem upper_mate_bound (leaves : G.BoundedLeaves) (root : V) : G.UpperGuarantee root G.mate := by
  refine ⟨G.defaultPlan, ?_⟩
  intro self payoff result
  exact (TerminalResult.payoff_bounded G leaves result).2

omit [DecidableEq V] in
theorem opposite_bounded_leaves (leaves : G.BoundedLeaves) : G.opposite.BoundedLeaves := by
  intro v score legal
  have bound := leaves v (-score) legal
  change -G.mate ≤ score ∧ score ≤ G.mate
  constructor <;> omega

/-- 相手視点の下限は、元のゲームの上限を与える。 -/
theorem upper_of_opposite_lower (root : V) (value : Int)
    (lower : G.opposite.LowerGuarantee root value) : G.UpperGuarantee root (-value) := by
  obtain ⟨opponent, bound⟩ := lower
  refine ⟨opponent.unopposite, ?_⟩
  intro self payoff result
  have moved := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at moved
  have h := bound self.opposite (-payoff) moved
  omega

/-- 相手視点の上限は、元のゲームの下限を与える。 -/
theorem lower_of_opposite_upper (root : V) (value : Int)
    (upper : G.opposite.UpperGuarantee root value) : G.LowerGuarantee root (-value) := by
  obtain ⟨self, bound⟩ := upper
  refine ⟨self.unopposite, ?_⟩
  intro opponent payoff result
  have moved := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at moved
  have h := bound opponent.opposite (-payoff) moved
  omega

theorem ExactValue.of_opposite (root : V) (value : Int) (exact : G.opposite.ExactValue root value) :
    G.ExactValue root (-value) :=
  ⟨G.lower_of_opposite_upper root value exact.2, G.upper_of_opposite_lower root value exact.1⟩

/-- 勝てる正の値tの一つ上で勝てなければ、整数最適値はt。
t=Mateでは次の閾値を使えないため、入力leafを含む大域上限を使う。 -/
theorem exact_at_positive_boundary (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) (t : Int)
    (positive : 0 < t) (bounded : t ≤ G.mate) (winning : G.LowerGuarantee root t)
    (boundary : t = G.mate ∨ ¬ G.LowerGuarantee root (t + 1)) : G.ExactValue root t := by
  refine ⟨winning, ?_⟩
  rcases boundary with top | next
  · simpa only [top] using G.upper_mate_bound leaves root
  · by_cases top : t = G.mate
    · simpa only [top] using G.upper_mate_bound leaves root
    · have upper := G.upper_of_not_lower vertices covered root (t + 1) (by omega) (by omega) next
      simpa using upper

/-- 正の値を保証できる局面には、最大の勝利閾値で表される整数最適値がある。 -/
theorem positive_exact_exists (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (winning : G.LowerGuarantee root 1) :
    ∃ value, 0 < value ∧ value ≤ G.mate ∧ G.ExactValue root value := by
  have positive := G.mate_positive
  let P := fun n : Nat => 0 < n ∧ G.LowerGuarantee root (n : Int)
  have cast_mate : (G.mate.toNat : Int) = G.mate := Int.toNat_of_nonneg (by omega)
  obtain ⟨n, bound, good, largest⟩ := largest_bounded_nat P G.mate.toNat
    ⟨1, by omega, by exact ⟨by decide, winning⟩⟩
  have npos : 0 < (n : Int) := by have := good.1; omega
  have nbound : (n : Int) ≤ G.mate := by omega
  refine ⟨(n : Int), npos, nbound, G.exact_at_positive_boundary leaves vertices covered root
    (n : Int) npos nbound good.2 (Or.inr ?_)⟩
  intro next
  by_cases cap : n + 1 ≤ G.mate.toNat
  · have next_good : P (n + 1) := ⟨by omega, by simpa only [Int.natCast_add, Int.natCast_one] using next⟩
    have impossible := largest (n + 1) cap next_good
    omega
  · obtain ⟨self, lower⟩ := next
    obtain ⟨opponent, upper⟩ := G.upper_mate_bound leaves root
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    have lo := lower opponent payoff result
    have hi := upper self payoff result
    omega

/-- 正・負・0の全場合で、両側の全履歴依存戦略を対象とする整数最適値を構成する。 -/
theorem integer_value_exists (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    ∃ value, -G.mate ≤ value ∧ value ≤ G.mate ∧ G.ExactValue root value := by
  classical
  have positive := G.mate_positive
  by_cases own : G.LowerGuarantee root 1
  · obtain ⟨value, pos, upper, exact⟩ := G.positive_exact_exists leaves vertices covered root own
    exact ⟨value, by omega, upper, exact⟩
  · by_cases other : G.opposite.LowerGuarantee root 1
    · obtain ⟨value, pos, upper, exact⟩ := G.opposite.positive_exact_exists
        (G.opposite_bounded_leaves leaves) vertices covered root other
      have upper' : value ≤ G.mate := upper
      exact ⟨-value, by omega, by omega, ExactValue.of_opposite G root value exact⟩
    · have upper := G.upper_of_not_lower vertices covered root 1 (by decide) (by omega) own
      have other_upper := G.opposite.upper_of_not_lower vertices covered root 1 (by decide)
        (by change 1 ≤ G.mate; omega) other
      have lower := G.lower_of_opposite_upper root 0 (by simpa using other_upper)
      exact ⟨0, by omega, by omega, by simpa using And.intro lower upper⟩

/-- 全局面の整数最適値は存在し、一意である。 -/
theorem integer_value_exists_unique (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    ∃ value, -G.mate ≤ value ∧ value ≤ G.mate ∧ G.ExactValue root value ∧
      ∀ other, G.ExactValue root other → other = value := by
  obtain ⟨value, lower, upper, exact⟩ := G.integer_value_exists leaves vertices covered root
  exact ⟨value, lower, upper, exact, fun _ other => ExactValue.unique G vertices covered root other exact⟩

end ThresholdGame
end PetaProof
