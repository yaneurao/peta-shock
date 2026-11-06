import PetaProof.SignedBounds
import PetaProof.FiniteGameExamples

/-! 視点反転の符号、通常千日手の値0、両側の正の勝利の排他性を検査する。 -/
namespace PetaProof.SignedBoundsExamples

open ThresholdGame PropagationExamples FinitePayoffExamples FiniteGameExamples

theorem opposite_draw_is_zero :
    drawGame.opposite.repetitionValue (show drawGame.LegalNode false true from rfl) drawLegalBack = 0 := by
  rw [drawGame.opposite_repetitionValue, draw_legal_payoff]
  rfl

theorem opposite_opponent_check_is_minus_mate :
    loopGame.opposite.repetitionValue (show loopGame.LegalNode false true from rfl) drawLegalBack = -32000 := by
  rw [loopGame.opposite_repetitionValue]
  simp [repetitionValue, drawLegalBack, Walk.Every, loopGame]

theorem opposite_own_check_is_mate :
    ownCheckingGame.opposite.repetitionValue
      (show ownCheckingGame.LegalNode false true from rfl) drawLegalBack = 32000 := by
  rw [ownCheckingGame.opposite_repetitionValue]
  simp [repetitionValue, drawLegalBack, Walk.Every, ownCheckingGame, drawGame]

/-- 実際の最初の終局手順も反転できる。通常千日手は反転後も0である。 -/
noncomputable def oppositeDrawTerminal : drawGame.opposite.TerminalResult drawPlan.opposite false 0 := by
  simpa using TerminalResult.opposite drawGame drawTerminal

/-- leafの値と選択だけが反転し、履歴で決まる終局地点は変わらない。 -/
noncomputable def oppositeHistoryLeaf :
    escapeGame.opposite.TerminalResult historyPlan.opposite false 0 := by
  simpa using TerminalResult.opposite escapeGame historyLeaf

def ordinaryPlan (positive : Bool) : ordinaryGame.MovePlan where
  choose := fun _ _ => .leaf (if positive then 20 else -20)
  legal := by
    intro _ _
    cases positive
    · exact Or.inr rfl
    · exact Or.inl rfl

def ordinaryTerminal (positive : Bool) :
    ordinaryGame.TerminalResult (ordinaryPlan positive) () (if positive then 20 else -20) :=
  TerminalResult.leaf (G := ordinaryGame) (plan := ordinaryPlan positive)
    (.nil ()) trivial (by intro v; cases v; decide) _ ((ordinaryPlan positive).legal [] ()) rfl

/-- 非零leafの符号も確認する。履歴や候補手だけ反転して値を取り違えることを防ぐ。 -/
noncomputable def oppositePositiveLeaf :
    ordinaryGame.opposite.TerminalResult (ordinaryPlan true).opposite () (-20) := by
  simpa using TerminalResult.opposite ordinaryGame (ordinaryTerminal true)

noncomputable def oppositeNegativeLeaf :
    ordinaryGame.opposite.TerminalResult (ordinaryPlan false).opposite () 20 := by
  simpa using TerminalResult.opposite ordinaryGame (ordinaryTerminal false)

def drawUnit : ThresholdGame Bool := drawGame.lowerThreshold 1 (by decide) (by decide)

def drawUnitNegative : drawUnit.RefutationRegion (fun _ => True) where
  response := drawRegion.response
  chosen_legal := drawRegion.chosen_legal
  closed := by
    intro v _ m reply
    have chosen : m = .node (!v) := reply.1
    subst m
    trivial
  rank := drawRegion.rank
  strict_checking := drawRegion.strict_checking

def drawUnitOppositeNegative : drawUnit.opposite.RefutationRegion (fun _ => True) where
  response := fun v => .node (!v)
  chosen_legal := fun _ _ _ => rfl
  closed := by
    intro v _ m reply
    have chosen : m = .node (!v) := by
      cases m with
      | node w => exact reply.1
      | leaf score => cases reply.1
    subst m
    trivial
  rank := fun v => if v then 1 else 0
  strict_checking := by
    intro v w _ reply checking
    have same : w = !v := Move.node.inj reply.1
    subst w
    cases v with
    | false => exact False.elim (checking (by decide))
    | true => decide

/-- 両側とも閾値1に勝てないため、通常千日手の整数最適値は0となる。 -/
theorem draw_exact_zero (root : Bool) : drawUnit.ExactValue root 0 :=
  drawUnit.exact_zero_of_no_positive [false, true] (by intro v; cases v <;> simp) root rfl
    (drawUnitNegative.not_fourfold_winning [false, true] (by intro v; cases v <;> simp) root trivial)
    (drawUnitOppositeNegative.not_fourfold_winning [false, true] (by intro v; cases v <;> simp) root trivial)

theorem draw_has_no_other_value (root : Bool) (value : Int) (exact : drawUnit.ExactValue root value) :
    value = 0 :=
  ExactValue.unique drawUnit [false, true] (by intro v; cases v <;> simp) root exact (draw_exact_zero root)

theorem draw_zero_is_realized (root : Bool) :
    ∃ self opponent : drawUnit.MovePlan,
      Nonempty (drawUnit.TerminalResult (drawUnit.combinePlans self opponent) root 0) :=
  ExactValue.realized drawUnit [false, true] (by intro v; cases v <;> simp) root (draw_exact_zero root)

/-- 相手が王手し続ける循環は自分の正の勝利であり、相手側も正の勝利とはならない。 -/
theorem no_opposite_positive_in_check_loop (root : Bool) : ¬ loopGame.opposite.FourfoldWinning root :=
  loopGame.positive_winners_exclusive [false, true] (by intro v; cases v <;> simp) root
    (opponent_check_loop_wins_finite_game root)

end PetaProof.SignedBoundsExamples
