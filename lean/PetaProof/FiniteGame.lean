import PetaProof.TerminalPlay

/-!
leafまたは最初の四回出現で終わる有限ゲームの勝利定義。
終局手順の存在を別に証明し、正側と反証側の保証を全履歴依存戦略へ適用する。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 各手の不変条件と反復区間の保証から、実際の最初の終局の利得を保証する。 -/
theorem TerminalResult.property [DecidableEq V] {plan : G.MovePlan} {root : V} {payoff : Int}
    (result : G.TerminalResult plan root payoff) (domain : V → Prop) (P : V → V → Prop)
    (Q : Int → Prop) (inside : domain root)
    (step : ∀ history v m, domain v → G.legal v m → plan.choose history v = m →
      match m with
      | .node w => domain w ∧ P v w
      | .leaf score => Q score)
    (loop : ∀ {a b : V} (edge : G.LegalNode a b) (back : Walk G.LegalNode b a),
      (Walk.cons edge back).Every P → Q (G.repetitionValue edge back)) : Q payoff := by
  have invariant {v : V} (trace : Walk G.LegalNode root v)
      (selected : trace.Selected plan.choose []) : domain v ∧ trace.Every P :=
    trace.selected_invariant plan.choose domain P
      (fun history a b parent edge chosen => step history a (.node b) parent edge chosen)
      [] inside selected
  cases result with
  | leaf trace selected _ score legal last =>
    exact step trace.visits _ (.leaf payoff) (invariant trace selected).1 legal last
  | repetition trace selected _ stem edge back suffix original _ _ =>
    have all := (invariant trace selected).2
    rw [original] at all
    have left := ((stem.append (.cons edge back)).every_append suffix P).mp all
    have middle := (stem.every_append (.cons edge back) P).mp left.1
    exact loop edge back middle.2

/-- 自分の全履歴依存戦略で、相手の全履歴依存戦略に対して終局利得を閾値以上にできる。 -/
def FourfoldWinning [DecidableEq V] (root : V) : Prop :=
  ∃ self : G.MovePlan, ∀ opponent : G.MovePlan, ∀ payoff,
    G.TerminalResult (G.combinePlans self opponent) root payoff → G.threshold ≤ payoff

namespace RankedRegion

variable {G} {won : V → Prop}

/-- 保証領域内の自分の手だけを固定し、未使用の選択も合法手で埋める。 -/
noncomputable def movePlan (region : G.RankedRegion won) : G.MovePlan := by
  classical
  exact {
    choose := fun history v => if inside : won v ∧ G.owner v = G.player then region.choice v
      else G.defaultPlan.choose history v
    legal := by
      intro history v
      split
      · rename_i inside
        exact region.chosen_legal v inside.1 inside.2
      · exact G.defaultPlan.legal history v
  }

theorem movePlan_follows (region : G.RankedRegion won) (opponent : G.MovePlan)
    (history : List V) (v : V) (inside : won v) (m : Move V) (legal : G.legal v m)
    (selected : (G.combinePlans region.movePlan opponent).choose history v = m) :
    G.Follows region.choice v m := by
  classical
  refine ⟨legal, ?_⟩
  intro own
  have condition : won v ∧ G.owner v = G.player := ⟨inside, own⟩
  simpa only [combinePlans, movePlan, if_pos own, dif_pos condition] using selected

/-- 正側の順位付き方策は、最初の四回出現で止めても、相手の全履歴戦略に勝つ。 -/
theorem fourfold_winning [DecidableEq V] (region : G.RankedRegion won) (root : V)
    (inside : won root) : G.FourfoldWinning root := by
  refine ⟨region.movePlan, ?_⟩
  intro opponent payoff result
  apply TerminalResult.property G result won region.FiniteInternal (fun score => G.threshold ≤ score) inside
  · intro history v m parent legal selected
    have follows := region.movePlan_follows opponent history v parent m legal selected
    cases m with
    | leaf score => exact region.closed v parent (.leaf score) follows
    | node w => exact ⟨region.closed v parent (.node w) follows, parent, follows⟩
  · intro a b edge back all
    let convert : ∀ v w, G.LegalNode v w ∧ region.FiniteInternal v w → region.FiniteInternal v w :=
      fun _ _ h => h.2
    have bound := region.finite_repetition_ge (convert a b ⟨edge, all.1⟩)
      ((back.withEvery region.FiniteInternal all.2).map convert)
    have same := (G.repetitionValue_map ⟨edge, all.1⟩
      (back.withEvery region.FiniteInternal all.2) convert).trans
      (G.repetitionValue_restrict edge back all.1 all.2)
    rw [same] at bound
    exact bound

end RankedRegion

namespace RefutationRegion

variable {G} {lost : V → Prop}

/-- 反証領域内の相手の手だけを固定する。領域外や自分の手番は未使用の合法手で埋める。 -/
noncomputable def movePlan (region : G.RefutationRegion lost) : G.MovePlan := by
  classical
  exact {
    choose := fun history v => if inside : lost v ∧ G.owner v ≠ G.player then region.response v
      else G.defaultPlan.choose history v
    legal := by
      intro history v
      split
      · rename_i inside
        exact region.chosen_legal v inside.1 inside.2
      · exact G.defaultPlan.legal history v
  }

theorem movePlan_replies (region : G.RefutationRegion lost) (self : G.MovePlan)
    (history : List V) (v : V) (inside : lost v) (m : Move V) (legal : G.legal v m)
    (selected : (G.combinePlans self region.movePlan).choose history v = m) :
    G.Replies region.response v m := by
  classical
  refine ⟨legal, ?_⟩
  intro other
  have condition : lost v ∧ G.owner v ≠ G.player := ⟨inside, other⟩
  simpa only [combinePlans, movePlan, if_neg other, dif_pos condition] using selected

/-- 反証側は、任意の自分の履歴戦略に対して最初の終局利得を閾値未満に抑える。 -/
theorem terminal_lt [DecidableEq V] (region : G.RefutationRegion lost) (root : V)
    (inside : lost root) (self : G.MovePlan) {payoff : Int}
    (result : G.TerminalResult (G.combinePlans self region.movePlan) root payoff) :
    payoff < G.threshold := by
  apply TerminalResult.property G result lost region.Internal (fun score => score < G.threshold) inside
  · intro history v m parent legal selected
    have reply := region.movePlan_replies self history v parent m legal selected
    cases m with
    | leaf score => exact region.closed v parent (.leaf score) reply
    | node w => exact ⟨region.closed v parent (.node w) reply, parent, reply⟩
  · intro a b edge back all
    let convert : ∀ v w, G.LegalNode v w ∧ region.Internal v w → region.Internal v w :=
      fun _ _ h => h.2
    have bound := region.repetition_lt (convert a b ⟨edge, all.1⟩)
      ((back.withEvery region.Internal all.2).map convert)
    have same := (G.repetitionValue_map ⟨edge, all.1⟩
      (back.withEvery region.Internal all.2) convert).trans
      (G.repetitionValue_restrict edge back all.1 all.2)
    rw [same] at bound
    exact bound

theorem not_fourfold_winning [DecidableEq V] (region : G.RefutationRegion lost)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) (inside : lost root) :
    ¬ G.FourfoldWinning root := by
  rintro ⟨self, wins⟩
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered
    (G.combinePlans self region.movePlan) root
  have lower := wins region.movePlan payoff result
  have upper := region.terminal_lt root inside self result
  omega

end RefutationRegion

/-- 最初の四回出現で終わる有限ゲームと、吸収co-Buchiモデルの勝利領域が一致する。 -/
theorem fourfold_winning_iff_absorbed_history [DecidableEq V]
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    G.FourfoldWinning root ↔ G.absorbedArena.HistoryWinning (.node root) := by
  classical
  constructor
  · intro finite
    apply Classical.byContradiction
    intro losing
    obtain ⟨lost, ⟨negative⟩, inside⟩ := G.refutation_of_not_absorbed_winning vertices covered root losing
    exact negative.not_fourfold_winning vertices covered root inside finite
  · intro winning
    obtain ⟨won, ⟨policy⟩, inside⟩ := (G.absorbedArena.history_winning_iff_ranked
      (G.absorbedVertices vertices) (G.absorbedVertices_cover vertices covered) (.node root)).mp winning
    exact (G.extractRankedRegion policy).fourfold_winning root inside

/-- 元の正の閾値解法の停止領域は、有限四回出現ゲームの勝利領域と過不足なく一致する。 -/
theorem stopped_exact_for_fourfold [DecidableEq V] {won : V → Prop} (sound : G.RankedRegion won)
    (ordinary : G.OrdinaryClosed won) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v)
    (root : V) : won root ↔ G.FourfoldWinning root := by
  exact (G.stopped_exact_for_absorbed_history sound ordinary vertices covered core covers_core n empty root).trans
    (G.fourfold_winning_iff_absorbed_history vertices covered root).symm

end PetaProof.ThresholdGame
