import PetaProof.FiniteGame
import PetaProof.FinitePayoffExamples

/-! 最初の終局の生成、履歴で変わる選択、有限ゲームと停止条件の接続の検査例。 -/
namespace PetaProof.FiniteGameExamples

open PropagationExamples FinitePayoffExamples ThresholdGame

/-- 同じ局面でも履歴長が4に達したらleafを選び、それ以前は内部手を選ぶ。 -/
def historyPlan : escapeGame.MovePlan where
  choose := fun history v => if v = true ∧ 4 ≤ history.length then .leaf 0 else .node (!v)
  legal := by
    intro history v
    split
    · rename_i condition
      exact Or.inr ⟨condition.1, rfl⟩
    · exact Or.inl rfl

theorem choice_changes_with_history :
    historyPlan.choose [false, true] true = .node false ∧
      historyPlan.choose [false, true, false, true] true = .leaf 0 := by simp [historyPlan]

def historyTrace : Walk escapeGame.LegalNode false true :=
  .cons (Or.inl rfl) (.cons (Or.inl rfl) (.cons (Or.inl rfl) (.nil true)))

/-- 3手の内部手の後にleafを選び、四回出現前に4手で終わる。 -/
def historyLeaf : escapeGame.TerminalResult historyPlan false 0 :=
  .leaf historyTrace (by simp [Walk.Selected, historyTrace, historyPlan])
    (by intro v; cases v <;> decide) 0 (Or.inr ⟨rfl, rfl⟩)
    (by simp [historyPlan, historyTrace, Walk.visits])

theorem history_leaf_four_plies : historyLeaf.plies = 4 := rfl

theorem all_history_plans_terminate (plan : escapeGame.MovePlan) (root : Bool) :
    ∃ payoff, Nonempty (escapeGame.TerminalResult plan root payoff) :=
  escapeGame.terminal_result_exists [false, true] (by intro v; cases v <;> simp) plan root

theorem all_terminal_results_within_six (plan : escapeGame.MovePlan) (root : Bool) (payoff : Int)
    (result : escapeGame.TerminalResult plan root payoff) : result.plies ≤ 6 :=
  TerminalResult.plies_bound escapeGame [false, true] (by intro v; cases v <;> simp) result

def drawPlan : drawGame.MovePlan where
  choose := fun _ v => .node (!v)
  legal := fun _ _ => rfl

def drawLegalBack : Walk drawGame.LegalNode true false :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil false)))))

def drawLegalTrace : Walk drawGame.LegalNode false false := .cons rfl drawLegalBack

theorem draw_legal_payoff : drawGame.repetitionValue (show drawGame.LegalNode false true from rfl)
    drawLegalBack = 0 := by
  have no_own : ¬ drawLegalTrace.Every
      (fun v w => drawGame.owner v = drawGame.player → drawGame.check v w) := by
    intro all
    exact all.1 rfl
  have no_other : ¬ drawLegalTrace.Every
      (fun v w => drawGame.owner v ≠ drawGame.player → drawGame.check v w) := by
    intro all
    exact all.2.1 (by decide)
  unfold drawLegalTrace at no_own no_other
  simp only [repetitionValue, if_neg no_own, if_neg no_other]

/-- 四回出現で止まる通常千日手を、実際の終局証拠として構成する。 -/
noncomputable def drawTerminal : drawGame.TerminalResult drawPlan false 0 := by
  have result : drawGame.TerminalResult drawPlan false
      (drawGame.repetitionValue (show drawGame.LegalNode false true from rfl) drawLegalBack) :=
    .repetition drawLegalTrace (by simp [Walk.Selected, drawPlan, drawLegalTrace, drawLegalBack])
      (by intro v; cases v <;> decide)
      (.nil false) rfl drawLegalBack (.nil false) rfl (by decide) (by decide)
  rw [draw_legal_payoff] at result
  exact result

theorem ordinary_leaf_wins_finite_game : ordinaryGame.FourfoldWinning () :=
  ordinaryRegion.fourfold_winning () (Or.inr trivial)

theorem opponent_check_loop_wins_finite_game (root : Bool) : loopGame.FourfoldWinning root :=
  loopRegion.fourfold_winning root (Or.inr trivial)

theorem ordinary_draw_cannot_win_positive (root : Bool) : ¬ drawGame.FourfoldWinning root :=
  drawRegion.not_fourfold_winning [false, true] (by intro v; cases v <;> simp) root trivial

theorem own_check_loop_cannot_win_positive (root : Bool) : ¬ ownCheckingGame.FourfoldWinning root :=
  ownCheckingRegion.not_fourfold_winning [false, true] (by intro v; cases v <;> simp) root trivial

/-- 相手が途中でleaf0へ逃げる例でも、元の停止条件と有限ゲームの勝敗が一致する。 -/
theorem original_stop_exact_for_finite_game (root : Bool) : False ↔ escapeGame.FourfoldWinning root :=
  escapeGame.stopped_exact_for_fourfold RankedRegion.empty CompletenessExamples.escape_ordinary_closed
    [false, true] (by intro v; cases v <;> simp) (fun _ => True) (fun _ _ => trivial)
    2 CompletenessExamples.escape_local_empty root

end PetaProof.FiniteGameExamples
