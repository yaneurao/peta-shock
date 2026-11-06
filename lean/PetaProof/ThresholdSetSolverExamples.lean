import PetaProof.ThresholdSetSolver
import PetaProof.FiniteGameExamples

/-! 集合制御の実際の分岐と返却集合。いずれも説明用の抽象グラフである。 -/
namespace PetaProof.ThresholdSetSolverExamples

open ThresholdGame PropagationExamples CompletenessExamples FinitePayoffExamples FiniteGameExamples

def vertices : List Bool := [false, true]
theorem covered (v : Bool) : v ∈ vertices := by cases v <;> simp [vertices]
def fullCore : Bool → Prop := fun _ => True

theorem good_leaf_in_closure : ordinaryGame.ordinaryClosure [()] (fun _ => False) () := by
  change False ∨ ordinaryGame.OrdinaryReady (fun _ => False) ()
  exact Or.inr (Or.inl ⟨rfl, .leaf 20, Or.inl rfl, by change (10 : Int) ≤ 20; decide⟩)

theorem good_leaf_result : ordinaryGame.thresholdResult [()] (fun _ => False) () := by
  classical
  have empty : ¬ (∃ v, ordinaryGame.localResult [()] (fun _ => False)
      (ordinaryGame.ordinaryClosure [()] (fun _ => False)) v) := by
    rintro ⟨v, inside⟩
    exact (ordinaryGame.iterate_subset 1 v inside).1
  unfold thresholdResult
  simp only [List.length_cons, List.length_nil, settle, if_neg empty]
  exact good_leaf_in_closure

theorem loop_closure_empty : loopGame.ordinaryClosure vertices (fun _ => False) = (fun _ => False) :=
  loopGame.ordinaryIter_of_closed loop_ordinary_closed vertices.length

theorem loop_local_survives (v : Bool) : loopGame.localResult vertices fullCore (fun _ => False) v :=
  loopGame.safe_survives loop_is_safe (fun _ _ => ⟨trivial, fun h => h⟩) vertices.length v trivial

theorem loop_nonempty_branch : ∃ v, loopGame.localResult vertices fullCore
    (loopGame.ordinaryClosure vertices (fun _ => False)) v := by
  rw [loop_closure_empty]
  exact ⟨false, loop_local_survives false⟩

theorem loop_one_batch (v : Bool) : loopGame.settle vertices fullCore 1 (fun _ => False) v := by
  classical
  simp only [settle, if_pos loop_nonempty_branch]
  apply loopGame.ordinaryClosure_subset vertices _ v
  exact Or.inr (by rw [loop_closure_empty]; exact loop_local_survives v)

theorem loop_computed_wins (v : Bool) : loopGame.thresholdResult vertices fullCore v := by
  apply (loopGame.thresholdResult_exact vertices covered fullCore (fun _ _ => trivial) v).mpr
  exact opponent_check_loop_wins_finite_game v

theorem escape_closure_empty : escapeGame.ordinaryClosure vertices (fun _ => False) = (fun _ => False) :=
  escapeGame.ordinaryIter_of_closed escape_ordinary_closed vertices.length

theorem escape_empty_branch : ¬ (∃ v, escapeGame.localResult vertices fullCore
    (escapeGame.ordinaryClosure vertices (fun _ => False)) v) := by
  rw [escape_closure_empty]
  rintro ⟨v, inside⟩
  exact escape_local_empty v inside

theorem escape_computed_empty : escapeGame.thresholdResult vertices fullCore = (fun _ => False) := by
  classical
  unfold thresholdResult
  change escapeGame.settle vertices fullCore (1 + 1) (fun _ => False) = _
  simp only [settle, if_neg escape_empty_branch]
  exact escape_closure_empty

theorem ordinary_draw_rejected (v : Bool) : ¬ drawGame.thresholdResult vertices fullCore v := by
  intro inside
  exact ordinary_draw_cannot_win_positive v
    ((drawGame.thresholdResult_exact vertices covered fullCore (fun _ _ => trivial) v).mp inside)

theorem own_checking_rejected (v : Bool) : ¬ ownCheckingGame.thresholdResult vertices fullCore v := by
  intro inside
  exact own_check_loop_cannot_win_positive v
    ((ownCheckingGame.thresholdResult_exact vertices covered fullCore (fun _ _ => trivial) v).mp inside)

theorem computed_stop_is_generated :
    (ordinaryGame.computedThresholdStop [()] (by intro v; cases v; simp) (fun _ => True)
      (fun _ _ => trivial) 10 (by decide) (by decide)).won () := by
  apply (ordinaryGame.computedThresholdStop_correct [()] (by intro v; cases v; simp)
    (fun _ => True) (fun _ _ => trivial) 10 (by decide) (by decide) ()).mpr
  exact ordinaryGame.retune_winning_iff 10 (by decide) (by decide) () |>.mp ordinary_leaf_wins_finite_game

theorem warm_start_already_won (v : Bool) :
    loopGame.settle vertices fullCore 0 (fun _ => True) v :=
  loopGame.ordinaryClosure_subset vertices (fun _ => True) v trivial

theorem stops_without_external_progress :
    loopGame.OrdinaryClosed (loopGame.thresholdResult vertices fullCore) ∧
      ∀ v, ¬ loopGame.localResult vertices fullCore (loopGame.thresholdResult vertices fullCore) v :=
  loopGame.thresholdResult_stops vertices covered fullCore

end PetaProof.ThresholdSetSolverExamples
