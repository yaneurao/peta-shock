import PetaProof.Perspective

/-!
正の閾値の勝敗から、元の有限ゲームの整数利得の上下界を得る。
値0も「両者とも正の値を保証できない」ことから上下の保証を構成して扱う。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V) [DecidableEq V]

/-- 自分の戦略により、相手の全履歴依存戦略に対して整数利得の下限を保証する。 -/
def LowerGuarantee (root : V) (bound : Int) : Prop :=
  ∃ self : G.MovePlan, ∀ opponent : G.MovePlan, ∀ payoff,
    G.TerminalResult (G.combinePlans self opponent) root payoff → bound ≤ payoff

/-- 相手の戦略により、自分の全履歴依存戦略に対して整数利得の上限を保証する。 -/
def UpperGuarantee (root : V) (bound : Int) : Prop :=
  ∃ opponent : G.MovePlan, ∀ self : G.MovePlan, ∀ payoff,
    G.TerminalResult (G.combinePlans self opponent) root payoff → payoff ≤ bound

/-- 両側に保証戦略がある整数値。単なるminimax方程式の固定点とは区別する。 -/
def ExactValue (root : V) (value : Int) : Prop :=
  G.LowerGuarantee root value ∧ G.UpperGuarantee root value

theorem lower_of_fourfold {root : V} (winning : G.FourfoldWinning root) :
    G.LowerGuarantee root G.threshold := winning

/-- 正の閾値tで勝てなければ、相手は整数値をt-1以下に抑えられる。 -/
theorem upper_of_not_fourfold (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (losing : ¬ G.FourfoldWinning root) : G.UpperGuarantee root (G.threshold - 1) := by
  obtain ⟨lost, ⟨negative⟩, inside⟩ := G.refutation_of_not_absorbed_winning vertices covered root
    (fun winning => losing ((G.fourfold_winning_iff_absorbed_history vertices covered root).mpr winning))
  refine ⟨negative.movePlan, ?_⟩
  intro self payoff result
  have strict := negative.terminal_lt root inside self result
  omega

/-- 相手視点でt以上を保証できるなら、元の視点では-t以下に抑えられる。 -/
theorem upper_of_opposite_fourfold (root : V) (winning : G.opposite.FourfoldWinning root) :
    G.UpperGuarantee root (-G.threshold) := by
  obtain ⟨opponent, wins⟩ := winning
  refine ⟨opponent.unopposite, ?_⟩
  intro self payoff result
  have reflected := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at reflected
  have lower := wins self.opposite (-payoff) reflected
  change G.threshold ≤ -payoff at lower
  omega

/-- 相手視点でt以上を保証できなければ、元の視点では1-t以上を保証できる。 -/
theorem lower_of_not_opposite_fourfold (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (losing : ¬ G.opposite.FourfoldWinning root) : G.LowerGuarantee root (1 - G.threshold) := by
  obtain ⟨self, upper⟩ := G.opposite.upper_of_not_fourfold vertices covered root losing
  refine ⟨self.unopposite, ?_⟩
  intro opponent payoff result
  have reflected := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at reflected
  have bound := upper opponent.opposite (-payoff) reflected
  change -payoff ≤ G.threshold - 1 at bound
  omega

/-- 同じ局面で、両者がそれぞれ正の閾値以上を保証することはできない。 -/
theorem positive_winners_exclusive (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (own : G.FourfoldWinning root) (other : G.opposite.FourfoldWinning root) : False := by
  obtain ⟨self, lower⟩ := own
  obtain ⟨opponent, upper⟩ := G.upper_of_opposite_fourfold root other
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
  have lo := lower opponent payoff result
  have hi := upper self payoff result
  have positive := G.positive
  omega

/-- 閾値1で双方が勝てなければ、両側の保証が一致して整数値は厳密に0となる。 -/
theorem exact_zero_of_no_positive (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (unit_threshold : G.threshold = 1) (own : ¬ G.FourfoldWinning root)
    (other : ¬ G.opposite.FourfoldWinning root) : G.ExactValue root 0 := by
  have lower := G.lower_of_not_opposite_fourfold vertices covered root other
  have upper := G.upper_of_not_fourfold vertices covered root own
  rw [unit_threshold] at lower upper
  exact ⟨by simpa using lower, by simpa using upper⟩

/-- 利得が0に確定しているなら、正の閾値に勝てる側はどちらにも存在しない。 -/
theorem no_positive_of_exact_zero (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (value : G.ExactValue root 0) : ¬ G.FourfoldWinning root ∧ ¬ G.opposite.FourfoldWinning root := by
  constructor
  · rintro ⟨self, wins⟩
    obtain ⟨opponent, upper⟩ := value.2
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    have lo := wins opponent payoff result
    have hi := upper self payoff result
    have positive := G.positive
    omega
  · intro winning
    obtain ⟨self, lower⟩ := value.1
    obtain ⟨opponent, upper⟩ := G.upper_of_opposite_fourfold root winning
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    have lo := lower opponent payoff result
    have hi := upper self payoff result
    have positive := G.positive
    omega

theorem exact_zero_iff_no_positive (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    (unit_threshold : G.threshold = 1) :
    G.ExactValue root 0 ↔ ¬ G.FourfoldWinning root ∧ ¬ G.opposite.FourfoldWinning root :=
  ⟨G.no_positive_of_exact_zero vertices covered root,
    fun h => G.exact_zero_of_no_positive vertices covered root unit_threshold h.1 h.2⟩

/-- 両側の保証を伴う整数値は一意である。戦略を組み合わせて実際に終局させて比較する。 -/
theorem ExactValue.unique (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    {a b : Int} (left : G.ExactValue root a) (right : G.ExactValue root b) : a = b := by
  have compare {x y : Int} (lower : G.LowerGuarantee root x) (upper : G.UpperGuarantee root y) : x ≤ y := by
    obtain ⟨self, lo⟩ := lower
    obtain ⟨opponent, hi⟩ := upper
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    exact Int.le_trans (lo opponent payoff result) (hi self payoff result)
  exact Int.le_antisymm (compare left.1 right.2) (compare right.1 left.2)

/-- 最適な両戦略を同時に使えば、その値で実際に終局する手順が存在する。 -/
theorem ExactValue.realized (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V)
    {value : Int} (exact : G.ExactValue root value) :
    ∃ self opponent : G.MovePlan, Nonempty (G.TerminalResult (G.combinePlans self opponent) root value) := by
  obtain ⟨self, lower⟩ := exact.1
  obtain ⟨opponent, upper⟩ := exact.2
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
  have same := Int.le_antisymm (lower opponent payoff result) (upper self payoff result)
  exact ⟨self, opponent, by simpa only [same] using Nonempty.intro result⟩

end PetaProof.ThresholdGame
