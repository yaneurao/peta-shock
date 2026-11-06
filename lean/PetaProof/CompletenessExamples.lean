import PetaProof.Completeness
import PetaProof.PropagationExamples

/-!
最下流成分による完全性を、小さな抽象ゲームで使う。
相手の悪い出口がある場合は、特定の方策だけでなく全てのPositionalRegionを排除する。
-/

namespace PetaProof.CompletenessExamples

open ThresholdGame PropagationExamples

theorem loop_ordinary_closed : loopGame.OrdinaryClosed (fun _ => False) := by
  intro v ordinary
  rcases ordinary with ⟨_, m, legal, good⟩ | ⟨_, all_good⟩
  · change m = .node (!v) at legal
    subst m
    exact good
  · exact all_good (.node (!v)) rfl

/-- 確定集合が空であれば、相手王手の循環から非空の局所候補を必ず取り出せる。 -/
theorem loop_missing_forces_candidate :
    ∃ candidate, (∃ v, candidate v) ∧ loopGame.SafeSet (fun _ => False) candidate ∧
      ∀ v, candidate v → CyclicVertex loopGame.OpponentChecking v ∧ ¬ False := by
  apply loopRegion.positional.missing_yields_local_safe loop_ordinary_closed [false, true]
  · intro v _
    cases v <;> simp
  · exact ⟨false, Or.inr True.intro, fun h => h⟩

theorem escape_ordinary_closed : escapeGame.OrdinaryClosed (fun _ => False) := by
  intro v ordinary
  rcases ordinary with ⟨own, m, legal, good⟩ | ⟨_, all_good⟩
  · rcases legal with selected | ⟨opponent, _⟩
    · subst m
      exact good
    · have self : v = false := own
      have impossible : (false : Bool) = true := self.symm.trans opponent
      cases impossible
  · exact all_good (.node (!v)) (Or.inl rfl)

theorem escape_local_empty : ∀ v,
    ¬ escapeGame.pruneIter (fun _ => False) (fun _ => True ∧ ¬ False) 2 v := by
  have initial : (fun _ : Bool => True ∧ ¬ False) = (fun _ : Bool => True) := by
    funext _
    exact propext (by simp)
  rw [initial]
  exact escape_all_deleted

/-- 悪い出口のある版では、どの履歴不要の正の保証方策も存在しない。 -/
theorem escape_no_positional_win (v : Bool) : ¬ escapeGame.PositionalWinning v := by
  rintro ⟨possible, ⟨region⟩, hv⟩
  exact region.complete_when_local_empty escape_ordinary_closed [false, true]
    (by intro x _; cases x <;> simp) (fun _ => True) (fun _ _ => True.intro)
    2 escape_local_empty v hv

/-- 良いleafがあるのに通常伝播を閉じていない場合は、完全性の停止前提を満たさない。 -/
theorem ordinary_closure_is_needed : ¬ ordinaryGame.OrdinaryClosed (fun _ => False) := by
  intro closed
  exact closed () (Or.inl ⟨rfl, .leaf 20, Or.inl rfl, by change (10 : Int) ≤ 20; decide⟩)

end PetaProof.CompletenessExamples
