import PetaProof.ThresholdDeterminacy
import PetaProof.CompletenessExamples

/-! leafの閾値境界、良いleafと悪いleafの混在、相手の悪いleaf出口を検査する。 -/
namespace PetaProof.AbsorptionExamples

open PropagationExamples

theorem threshold_equal_is_success {V : Type} (game : ThresholdGame V) :
    game.encodeMove (.leaf game.threshold) = .success := by
  simp [ThresholdGame.encodeMove]

theorem below_threshold_is_failure {V : Type} (game : ThresholdGame V) :
    game.encodeMove (.leaf (game.threshold - 1)) = .failure := by
  have bad : ¬ game.threshold ≤ game.threshold - 1 := by omega
  simp [ThresholdGame.encodeMove, bad]

/-- 自分が悪いleafを選べることと、勝利戦略がないことは同じではない。 -/
theorem ordinary_has_bad_leaf : ordinaryGame.absorbedArena.edge (.node ()) .failure := by
  refine ⟨-20, Or.inr rfl, ?_⟩
  change ¬ (10 : Int) ≤ -20
  omega

theorem ordinary_has_good_leaf : ordinaryGame.absorbedArena.edge (.node ()) .success := by
  refine ⟨20, Or.inl rfl, ?_⟩
  change (10 : Int) ≤ 20
  omega

theorem ordinary_history_winning : ordinaryGame.absorbedArena.HistoryWinning (.node ()) :=
  (ordinaryGame.liftRankedRegion ordinaryRegion).history_winning
    (ordinaryGame.absorbedVertices [()]) (ordinaryGame.absorbedVertices_cover [()] (by simp))
    (.node ()) (Or.inr trivial)

/-- 相手が悪いleafへ出られるなら、内部が相手王手循環でも勝利保証できない。 -/
theorem opponent_bad_leaf_prevents_history_win (v : Bool) :
    ¬ escapeGame.absorbedArena.HistoryWinning (.node v) := by
  intro winning
  exact CompletenessExamples.escape_no_positional_win v
    ((escapeGame.absorbed_history_iff_positional [false, true]
      (by intro v; cases v <;> simp) v).mp winning)

theorem original_core_stop_handles_all_histories (v : Bool) :
    False ↔ escapeGame.absorbedArena.HistoryWinning (.node v) :=
  escapeGame.stopped_exact_for_absorbed_history ThresholdGame.RankedRegion.empty
    CompletenessExamples.escape_ordinary_closed [false, true]
    (by intro v; cases v <;> simp) (fun _ => True) (fun _ _ => trivial)
    2 CompletenessExamples.escape_local_empty v

end PetaProof.AbsorptionExamples
