import PetaProof.ValueAssembly
import PetaProof.SignedBoundsExamples

/-!
非零leaf・Mate境界・通常千日手・連続王手で、整数最適値の構成と両側の値の合成を検査する。
-/
namespace PetaProof.IntegerValueExamples

open ThresholdGame PropagationExamples FinitePayoffExamples SignedBoundsExamples

/-- 唯一の手が指定した整数値のleafである、1局面の検査用ゲーム。 -/
def fixedLeafGame (score : Int) : ThresholdGame Unit where
  legal := fun _ m => m = .leaf score
  owner := fun _ => false
  check := fun _ _ => False
  player := false
  threshold := 1
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by intro _ _ impossible; cases impossible
  nonempty_moves := fun _ => ⟨.leaf score, rfl⟩
  no_mutual_cycle := by intro _ _ impossible _; cases impossible.1

theorem fixed_leaves_bounded (score : Int) (bounds : -32000 ≤ score ∧ score ≤ 32000) :
    (fixedLeafGame score).BoundedLeaves := by
  intro _ actual legal
  have same : actual = score := Move.leaf.inj legal
  simpa only [same] using bounds

theorem fixed_payoff (score : Int) {plan : (fixedLeafGame score).MovePlan} {payoff : Int}
    (result : (fixedLeafGame score).TerminalResult plan () payoff) : payoff = score := by
  apply TerminalResult.property (fixedLeafGame score) result (fun _ => True) (fun _ _ => True)
    (fun value => value = score) trivial
  · intro _ _ m _ legal _
    cases m with
    | node _ => cases legal
    | leaf _ => exact Move.leaf.inj legal
  · intro _ _ edge _ _
    cases edge

theorem fixed_exact (score : Int) : (fixedLeafGame score).ExactValue () score := by
  constructor
  · refine ⟨(fixedLeafGame score).defaultPlan, ?_⟩
    intro opponent payoff result
    rw [fixed_payoff score result]
    exact Int.le_refl _
  · refine ⟨(fixedLeafGame score).defaultPlan, ?_⟩
    intro self payoff result
    rw [fixed_payoff score result]
    exact Int.le_refl _

/-- 存在証明で構成した値a-bが、独立に求めた唯一のleaf値と一致する。 -/
theorem fixed_assembly (score : Int) (bounds : -32000 ≤ score ∧ score ≤ 32000) :
    ∃ a b, (fixedLeafGame score).PositiveMaximum () a ∧
      (fixedLeafGame score).opposite.PositiveMaximum () b ∧ a - b = score ∧ (a = 0 ∨ b = 0) := by
  let game := fixedLeafGame score
  have leaves := fixed_leaves_bounded score bounds
  obtain ⟨a, b, own, other, exact⟩ := game.value_assembly_exists leaves [()] (by simp) ()
  exact ⟨a, b, own, other, ExactValue.unique game [()] (by simp) () exact (fixed_exact score),
    game.positive_maxima_exclusive leaves [()] (by simp) () own other⟩

theorem positive_leaf_parts (score : Int) (positive : 0 < score) (bound : score ≤ 32000) :
    (fixedLeafGame score).PositiveMaximum () score ∧
      (fixedLeafGame score).opposite.PositiveMaximum () 0 := by
  obtain ⟨a, b, own, other, same, exclusive⟩ := fixed_assembly score ⟨by omega, bound⟩
  have bzero : b = 0 := by
    have := other.nonnegative
    rcases exclusive with zero | zero <;> omega
  have avalue : a = score := by omega
  simpa only [bzero, avalue] using And.intro own other

theorem negative_leaf_parts (score : Int) (negative : score < 0) (bound : -32000 ≤ score) :
    (fixedLeafGame score).PositiveMaximum () 0 ∧
      (fixedLeafGame score).opposite.PositiveMaximum () (-score) := by
  obtain ⟨a, b, own, other, same, exclusive⟩ := fixed_assembly score ⟨bound, by omega⟩
  have azero : a = 0 := by
    have := own.nonnegative
    rcases exclusive with zero | zero <;> omega
  have bvalue : b = -score := by omega
  simpa only [azero, bvalue] using And.intro own other

theorem positive_twenty : (fixedLeafGame 20).PositiveMaximum () 20 ∧
    (fixedLeafGame 20).opposite.PositiveMaximum () 0 :=
  positive_leaf_parts 20 (by decide) (by decide)

theorem negative_twenty : (fixedLeafGame (-20)).PositiveMaximum () 0 ∧
    (fixedLeafGame (-20)).opposite.PositiveMaximum () 20 :=
  negative_leaf_parts (-20) (by decide) (by decide)

theorem positive_mate_boundary : (fixedLeafGame 32000).PositiveMaximum () 32000 ∧
    (fixedLeafGame 32000).opposite.PositiveMaximum () 0 :=
  positive_leaf_parts 32000 (by decide) (by decide)

theorem negative_mate_boundary : (fixedLeafGame (-32000)).PositiveMaximum () 0 ∧
    (fixedLeafGame (-32000)).opposite.PositiveMaximum () 32000 :=
  negative_leaf_parts (-32000) (by decide) (by decide)

/-- Mate外の入力を、値域前提を満たすものとして扱っていないことも検査する。 -/
theorem out_of_range_leaf_excluded : ¬ (fixedLeafGame 32001).BoundedLeaves := by
  intro leaves
  have impossible := leaves () 32001 rfl
  change -32000 ≤ 32001 ∧ 32001 ≤ 32000 at impossible
  omega

/-- どの反復区間でも相手が王手を続け、leafがない場合の利得はMateとなる。 -/
theorem checking_loop_exact_mate {V : Type} [DecidableEq V] (game : ThresholdGame V)
    (no_leaves : ∀ v score, ¬ game.legal v (.leaf score))
    (checking : ∀ v w, game.LegalNode v w → game.owner v ≠ game.player → game.check v w)
    (root : V) : game.ExactValue root game.mate := by
  have payoff {plan : game.MovePlan} {value : Int} (result : game.TerminalResult plan root value) :
      value = game.mate := by
    apply TerminalResult.property game result (fun _ => True) (fun _ _ => True) (fun v => v = game.mate) trivial
    · intro _ v m _ legal _
      cases m with
      | node _ => exact ⟨trivial, trivial⟩
      | leaf score => exact False.elim (no_leaves v score legal)
    · intro a b edge back _
      classical
      have other : (Walk.cons edge back).Every
          (fun v w => game.owner v ≠ game.player → game.check v w) :=
        (Walk.cons edge back).every_mono (Walk.cons edge back).every_true
          (fun v w legal _ => checking v w legal)
      have own := fun h => game.no_both_checks edge back h other
      simp only [repetitionValue, if_neg own, if_pos other]
  constructor
  · refine ⟨game.defaultPlan, ?_⟩
    intro opponent value result
    rw [payoff result]
    exact Int.le_refl _
  · refine ⟨game.defaultPlan, ?_⟩
    intro self value result
    rw [payoff result]
    exact Int.le_refl _

theorem opponent_checks_value (root : Bool) : loopGame.ExactValue root 32000 := by
  apply checking_loop_exact_mate loopGame (by intro _ _ impossible; cases impossible)
  intro v w _ other
  cases v with
  | false => exact False.elim (other rfl)
  | true => rfl

theorem own_checks_value (root : Bool) : ownCheckingGame.ExactValue root (-32000) := by
  apply ExactValue.of_opposite ownCheckingGame root 32000
  apply checking_loop_exact_mate ownCheckingGame.opposite (by intro _ _ impossible; cases impossible)
  intro v w _ other
  cases v with
  | false => rfl
  | true => exact False.elim (other rfl)

theorem integer_construction_matches_check_loop (root : Bool) :
    ∃ value, -32000 ≤ value ∧ value ≤ 32000 ∧ loopGame.ExactValue root value ∧ value = 32000 := by
  obtain ⟨value, lower, upper, exact⟩ := loopGame.integer_value_exists
    (by intro _ _ impossible; cases impossible) [false, true] (by intro v; cases v <;> simp) root
  exact ⟨value, lower, upper, exact, ExactValue.unique loopGame [false, true]
    (by intro v; cases v <;> simp) root exact (opponent_checks_value root)⟩

theorem integer_construction_matches_draw (root : Bool) :
    ∃ value, drawUnit.ExactValue root value ∧ value = 0 := by
  obtain ⟨value, _, _, exact⟩ := drawUnit.integer_value_exists
    (by intro _ _ impossible; cases impossible) [false, true] (by intro v; cases v <;> simp) root
  exact ⟨value, exact, ExactValue.unique drawUnit [false, true]
    (by intro v; cases v <;> simp) root exact (draw_exact_zero root)⟩

/-- 悪いleafも選択可能だが、自分が良い方を選べるゲームの最適値。 -/
theorem ordinary_exact_twenty : ordinaryGame.ExactValue () 20 := by
  constructor
  · refine ⟨ordinaryPlan true, ?_⟩
    intro opponent payoff result
    apply TerminalResult.property ordinaryGame result (fun _ => True) (fun _ _ => True)
      (fun score => 20 ≤ score) trivial
    · intro history v m _ _ selected
      have chosen : (Move.leaf 20 : Move Unit) = m := by
        simpa [combinePlans, ordinaryPlan, ordinaryGame] using selected
      subst m
      exact Int.le_refl _
    · intro _ _ edge _ _
      rcases edge with impossible | impossible <;> cases impossible
  · refine ⟨ordinaryGame.defaultPlan, ?_⟩
    intro self payoff result
    apply TerminalResult.property ordinaryGame result (fun _ => True) (fun _ _ => True)
      (fun score => score ≤ 20) trivial
    · intro _ _ m _ legal _
      cases m with
      | node _ => rcases legal with impossible | impossible <;> cases impossible
      | leaf score =>
        rcases legal with good | bad
        · have same := Move.leaf.inj good
          omega
        · have same := Move.leaf.inj bad
          omega
    · intro _ _ edge _ _
      rcases edge with impossible | impossible <;> cases impossible

theorem integer_construction_selects_better_leaf :
    ∃ value, ordinaryGame.ExactValue () value ∧ value = 20 := by
  have leaves : ordinaryGame.BoundedLeaves := by
    intro _ score legal
    change -32000 ≤ score ∧ score ≤ 32000
    rcases legal with good | bad
    · have same := Move.leaf.inj good
      constructor <;> omega
    · have same := Move.leaf.inj bad
      constructor <;> omega
  obtain ⟨value, _, _, exact⟩ := ordinaryGame.integer_value_exists leaves [()] (by simp) ()
  exact ⟨value, exact, ExactValue.unique ordinaryGame [()] (by simp) () exact ordinary_exact_twenty⟩

end PetaProof.IntegerValueExamples
