import PetaProof.FiniteGame

/-! 一つの保証順位を共有する候補手なら、履歴に応じて自由に切り替えても正の閾値保証を保つ。 -/
namespace PetaProof.ThresholdGame.RankedRegion

universe u
variable {V : Type u} {G : ThresholdGame V} {won : V → Prop}
variable (region : G.RankedRegion won)

/-- depthとは独立の条件。相手の非王手辺だけは順位の厳密減少を要求する。 -/
def candidateCondition (vertex : V) : Move V → Prop
  | .leaf score => G.threshold ≤ score
  | .node child => won child ∧ region.rank child ≤ region.rank vertex ∧
      (G.owner vertex ≠ G.player → ¬ G.check vertex child → region.rank child < region.rank vertex)

def admissibleMove (vertex : V) (move : Move V) : Prop :=
  G.legal vertex move ∧ region.candidateCondition vertex move

theorem follows_admissible (vertex : V) (inside : won vertex) (move : Move V)
    (follows : G.Follows region.choice vertex move) : region.admissibleMove vertex move := by
  refine ⟨follows.1, ?_⟩
  cases move with
  | leaf score => exact region.closed vertex inside (.leaf score) follows
  | node child => exact ⟨region.closed vertex inside (.node child) follows,
      region.decreasing vertex child inside follows,
      region.opponent_strict vertex child inside follows⟩

theorem reference_candidate (vertex : V) (inside : won vertex) (own : G.owner vertex = G.player) :
    region.admissibleMove vertex (region.choice vertex) :=
  region.follows_admissible vertex inside _ ⟨region.chosen_legal vertex inside own, fun _ => rfl⟩

theorem opponent_candidate (vertex : V) (inside : won vertex) (other : G.owner vertex ≠ G.player)
    (move : Move V) (legal : G.legal vertex move) : region.admissibleMove vertex move :=
  region.follows_admissible vertex inside move ⟨legal, fun own => False.elim (other own)⟩

/-- 同一局面で履歴ごとに異なる候補を選んでもよい。相手の手は制限しない。 -/
def AdmissiblePlan (self : G.MovePlan) : Prop :=
  ∀ history vertex, won vertex → G.owner vertex = G.player →
    region.admissibleMove vertex (self.choose history vertex)

theorem reference_plan_admissible : region.AdmissiblePlan region.movePlan := by
  classical
  intro history vertex inside own
  have same : region.movePlan.choose history vertex = region.choice vertex := by
    simp [movePlan, inside, own]
  rw [same]
  exact region.reference_candidate vertex inside own

theorem combined_admissible (self opponent : G.MovePlan) (allowed : region.AdmissiblePlan self)
    (history : List V) (vertex : V) (inside : won vertex) (move : Move V) (legal : G.legal vertex move)
    (selected : (G.combinePlans self opponent).choose history vertex = move) : region.admissibleMove vertex move := by
  by_cases own : G.owner vertex = G.player
  · have same : self.choose history vertex = move := by simpa only [combinePlans, if_pos own] using selected
    rw [← same]
    exact allowed history vertex inside own
  · exact region.opponent_candidate vertex inside own move legal

def CandidateInternal (vertex child : V) : Prop :=
  G.LegalNode vertex child ∧ won vertex ∧ region.candidateCondition vertex (.node child)

theorem candidate_rank {vertex child : V} (edge : region.CandidateInternal vertex child) :
    region.rank child ≤ region.rank vertex := edge.2.2.2.1

theorem candidate_strict {vertex child : V} (edge : region.CandidateInternal vertex child)
    (other : G.owner vertex ≠ G.player) (noncheck : ¬ G.check vertex child) :
    region.rank child < region.rank vertex := edge.2.2.2.2 other noncheck

theorem candidate_loop_opponent_checks {a b : V} (edge : region.CandidateInternal a b)
    (back : Walk region.CandidateInternal b a) :
    (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  apply Walk.every_returning _ _ (Walk.cons edge back) (.nil a)
  intro vertex child step returning other
  apply Classical.byContradiction
  intro noncheck
  have strict := region.candidate_strict step other noncheck
  have lower := returning.nat_antitone region.rank (fun _ _ found => region.candidate_rank found)
  omega

theorem candidate_loop_not_own_checks {a b : V} (edge : region.CandidateInternal a b)
    (back : Walk region.CandidateInternal b a) :
    ¬ (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w) := by
  intro own
  let loop := Walk.cons edge back
  have opponent := region.candidate_loop_opponent_checks edge back
  have checks : loop.Every G.check := loop.every_mono (loop.every_and own opponent) (by
    intro vertex child _ both
    by_cases turn : G.owner vertex = G.player
    · exact both.1 turn
    · exact both.2 turn)
  exact G.no_mutual_cycle a b ⟨edge.1, checks.1⟩
    ((back.withEvery _ checks.2).map (fun _ _ found => ⟨found.1.1, found.2⟩))

theorem candidate_repetition_ge {a b : V} (edge : region.CandidateInternal a b)
    (back : Walk region.CandidateInternal b a) : G.threshold ≤ G.repetitionValue edge back := by
  classical
  have own := region.candidate_loop_not_own_checks edge back
  have other := region.candidate_loop_opponent_checks edge back
  simp only [repetitionValue, if_neg own, if_pos other]
  exact G.bounded

/-- 候補内なら、履歴依存の切替と相手の全応手を含む実際の最初の終局でも下限を保つ。 -/
theorem admissible_plan_guarantee [DecidableEq V] (self opponent : G.MovePlan)
    (allowed : region.AdmissiblePlan self) (root : V) (inside : won root) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : G.threshold ≤ payoff := by
  apply TerminalResult.property G result won region.CandidateInternal (fun score => G.threshold ≤ score) inside
  · intro history vertex move parent legal selected
    have admissible := region.combined_admissible self opponent allowed history vertex parent move legal selected
    cases move with
    | leaf score => exact admissible.2
    | node child => exact ⟨admissible.2.1, legal, parent, admissible.2⟩
  · intro a b edge back all
    let convert : ∀ v w, G.LegalNode v w ∧ region.CandidateInternal v w → region.CandidateInternal v w :=
      fun _ _ found => found.2
    have bound := region.candidate_repetition_ge (convert a b ⟨edge, all.1⟩)
      ((back.withEvery region.CandidateInternal all.2).map convert)
    have same := (G.repetitionValue_map ⟨edge, all.1⟩
      (back.withEvery region.CandidateInternal all.2) convert).trans
      (G.repetitionValue_restrict edge back all.1 all.2)
    rw [same] at bound
    exact bound

theorem candidate_subset_guarantee [DecidableEq V] (kept : V → Move V → Prop)
    (safe : ∀ vertex move, won vertex → G.owner vertex = G.player → kept vertex move →
      region.admissibleMove vertex move) (self opponent : G.MovePlan)
    (selected : ∀ history vertex, won vertex → G.owner vertex = G.player → kept vertex (self.choose history vertex))
    (root : V) (inside : won root) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : G.threshold ≤ payoff :=
  region.admissible_plan_guarantee self opponent
    (fun history vertex parent own => safe vertex _ parent own (selected history vertex parent own)) root inside payoff result

end PetaProof.ThresholdGame.RankedRegion
