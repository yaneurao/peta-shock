import PetaProof.SignedBounds

/-! 反証側の共通順位で候補を残す。視点反転により0・負の下限保証を得る。 -/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 反対視点での最初の終局を、履歴と判定区間を変えずに元の視点へ戻す。 -/
noncomputable def TerminalResult.unopposite [DecidableEq V] {plan : G.opposite.MovePlan}
    {root : V} {payoff : Int} (result : G.opposite.TerminalResult plan root payoff) :
    G.TerminalResult plan.unopposite root (-payoff) := by
  cases result with
  | leaf trace selected quiet score legal last =>
    refine TerminalResult.leaf (G := G) (plan := plan.unopposite)
      trace (trace.selected_negate plan.choose [] selected) quiet (-payoff) legal ?_
    change (plan.choose trace.visits _).negate = .leaf (-payoff)
    rw [last]
    rfl
  | repetition trace selected earliest stem edge back suffix original first fourth =>
    have originalResult := TerminalResult.repetition (G := G) (plan := plan.unopposite)
      trace (trace.selected_negate plan.choose [] selected) earliest
      stem edge back suffix original first fourth
    simpa only [G.opposite_repetitionValue, Int.neg_neg] using originalResult

/-- 最小利得-Mでは王手循環を除く必要はない。leafも-M以上なら全合法計画が下限を保つ。 -/
theorem terminal_mate_floor [DecidableEq V]
    (leafBound : ∀ vertex score, G.legal vertex (.leaf score) → -G.mate ≤ score)
    {plan : G.MovePlan} {root : V} {payoff : Int} (result : G.TerminalResult plan root payoff) :
    -G.mate ≤ payoff := by
  apply TerminalResult.property G result (fun _ => True) (fun _ _ => True)
    (fun score => -G.mate ≤ score) trivial
  · intro history vertex move _ legal _
    cases move with
    | node child => exact ⟨trivial, trivial⟩
    | leaf score => exact leafBound vertex score legal
  · intro a b edge back _
    classical
    have positive := G.positive
    have bounded := G.bounded
    unfold repetitionValue
    dsimp only
    split
    · exact Int.le_refl _
    · split <;> omega

namespace RefutationRegion

variable {G} {lost : V → Prop}
variable (region : G.RefutationRegion lost)

/-- 相手の非王手なら順位を戻せる。それ以外の内部手は厳密に減少させる。 -/
def candidateCondition (vertex : V) : Move V → Prop
  | .leaf score => score < G.threshold
  | .node child => lost child ∧
      ((G.owner vertex ≠ G.player → G.check vertex child) → region.rank child < region.rank vertex)

def admissibleMove (vertex : V) (move : Move V) : Prop :=
  G.legal vertex move ∧ region.candidateCondition vertex move

theorem replies_admissible (vertex : V) (inside : lost vertex) (move : Move V)
    (reply : G.Replies region.response vertex move) : region.admissibleMove vertex move := by
  refine ⟨reply.1, ?_⟩
  cases move with
  | leaf score => exact region.closed vertex inside (.leaf score) reply
  | node child => exact ⟨region.closed vertex inside (.node child) reply,
      region.strict_checking vertex child inside reply⟩

theorem reference_candidate (vertex : V) (inside : lost vertex) (other : G.owner vertex ≠ G.player) :
    region.admissibleMove vertex (region.response vertex) :=
  region.replies_admissible vertex inside _ ⟨region.chosen_legal vertex inside other, fun _ => rfl⟩

theorem own_candidate (vertex : V) (inside : lost vertex) (own : G.owner vertex = G.player)
    (move : Move V) (legal : G.legal vertex move) : region.admissibleMove vertex move :=
  region.replies_admissible vertex inside move ⟨legal, fun other => False.elim (other own)⟩

def AdmissiblePlan (opponent : G.MovePlan) : Prop :=
  ∀ history vertex, lost vertex → G.owner vertex ≠ G.player →
    region.admissibleMove vertex (opponent.choose history vertex)

theorem reference_plan_admissible : region.AdmissiblePlan region.movePlan := by
  classical
  intro history vertex inside other
  have same : region.movePlan.choose history vertex = region.response vertex := by
    simp [movePlan, inside, other]
  rw [same]
  exact region.reference_candidate vertex inside other

theorem combined_admissible (self opponent : G.MovePlan) (allowed : region.AdmissiblePlan opponent)
    (history : List V) (vertex : V) (inside : lost vertex) (move : Move V) (legal : G.legal vertex move)
    (selected : (G.combinePlans self opponent).choose history vertex = move) : region.admissibleMove vertex move := by
  by_cases own : G.owner vertex = G.player
  · exact region.own_candidate vertex inside own move legal
  · have same : opponent.choose history vertex = move := by
      simpa only [combinePlans, if_neg own] using selected
    rw [← same]
    exact allowed history vertex inside own

def CandidateInternal (vertex child : V) : Prop :=
  G.LegalNode vertex child ∧ lost vertex ∧ region.candidateCondition vertex (.node child)

theorem candidate_strict {vertex child : V} (edge : region.CandidateInternal vertex child)
    (checking : G.owner vertex ≠ G.player → G.check vertex child) :
    region.rank child < region.rank vertex := edge.2.2.2 checking

/-- 閉歩道の全相手手が王手なら全辺で厳密減少となり、元の順位へ戻れない。 -/
theorem candidate_loop_not_opponent_checks {a b : V} (edge : region.CandidateInternal a b)
    (back : Walk region.CandidateInternal b a) :
    ¬ (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  intro all
  have strict := region.candidate_strict edge all.1
  have lower := (back.withEvery _ all.2).nat_antitone region.rank
    (fun _ _ found => Nat.le_of_lt (region.candidate_strict found.1 found.2))
  omega

theorem candidate_repetition_lt {a b : V} (edge : region.CandidateInternal a b)
    (back : Walk region.CandidateInternal b a) : G.repetitionValue edge back < G.threshold := by
  classical
  have other := region.candidate_loop_not_opponent_checks edge back
  have positive := G.positive
  have bound := G.bounded
  by_cases own : (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w)
  · simp only [repetitionValue, if_pos own]
    omega
  · simp only [repetitionValue, if_neg own, if_neg other]
    exact positive

/-- 候補を履歴ごとに切り替えても、実際の最初の終局の厳密上限を保つ。 -/
theorem admissible_plan_upper [DecidableEq V] (self opponent : G.MovePlan)
    (allowed : region.AdmissiblePlan opponent) (root : V) (inside : lost root) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : payoff < G.threshold := by
  apply TerminalResult.property G result lost region.CandidateInternal (fun score => score < G.threshold) inside
  · intro history vertex move parent legal selected
    have admissible := region.combined_admissible self opponent allowed history vertex parent move legal selected
    cases move with
    | leaf score => exact admissible.2
    | node child => exact ⟨admissible.2.1, legal, parent, admissible.2⟩
  · intro a b edge back all
    let convert : ∀ v w, G.LegalNode v w ∧ region.CandidateInternal v w → region.CandidateInternal v w :=
      fun _ _ found => found.2
    have bound := region.candidate_repetition_lt (convert a b ⟨edge, all.1⟩)
      ((back.withEvery region.CandidateInternal all.2).map convert)
    have same := (G.repetitionValue_map ⟨edge, all.1⟩
      (back.withEvery region.CandidateInternal all.2) convert).trans
      (G.repetitionValue_restrict edge back all.1 all.2)
    rw [same] at bound
    exact bound

/-- 反証候補を視点反転すると、自分の非王手で順位を戻せる下限候補になる。 -/
theorem opposite_condition (vertex : V) (move : Move V) :
    region.candidateCondition vertex move ↔
      match move.negate with
      | .leaf score => 1 - G.threshold ≤ score
      | .node child => lost child ∧
          ((G.owner vertex = !G.player → G.check vertex child) → region.rank child < region.rank vertex) := by
  cases move with
  | leaf score => simp only [candidateCondition, Move.negate]; omega
  | node child => simp only [candidateCondition, Move.negate, Bool.eq_not]

/-- 正の相手閾値tの反証候補から、0以下の1-tを保証する任意切替を得る。 -/
theorem admissible_plan_opposite_lower [DecidableEq V] (self opponent : G.opposite.MovePlan)
    (allowed : region.AdmissiblePlan self.unopposite) (root : V) (inside : lost root) (payoff : Int)
    (result : G.opposite.TerminalResult (G.opposite.combinePlans self opponent) root payoff) :
    1 - G.threshold ≤ payoff := by
  have back := TerminalResult.unopposite G result
  have combined : (G.opposite.combinePlans self opponent).unopposite =
      G.combinePlans opponent.unopposite self.unopposite := by
    apply MovePlan.ext
    funext history vertex
    by_cases own : G.owner vertex = G.player
    · have other : ¬ G.owner vertex = !G.player := by simpa only [Bool.eq_not] using not_not_intro own
      simp only [MovePlan.unopposite, combinePlans, opposite, if_pos own, if_neg other]
    · have other : G.owner vertex = !G.player := Bool.eq_not_of_ne own
      simp only [MovePlan.unopposite, combinePlans, opposite, if_neg own, if_pos other]
  rw [combined] at back
  have upper := region.admissible_plan_upper opponent.unopposite self.unopposite allowed root inside (-payoff) back
  omega

end RefutationRegion
end PetaProof.ThresholdGame
