import PetaProof.SignedRankProgress

/-! 通常循環の延長、非負の短縮、危険な連続王手候補の除外を分けた小例。 -/
namespace PetaProof.SignedRankExamples

inductive Node | a | b | exit deriving DecidableEq, Repr
open Node

def vertices : List Node := [.a, .b, .exit]
theorem covered (v : Node) : v ∈ vertices := by cases v <;> simp [vertices]

def extending : SignedRankGraph.Input Node where
  moves := fun v => match v with | .a => [.exit, .b] | .b => [.exit, .a] | .exit => [.exit]
  nonempty := by intro v; cases v <;> simp
  minimizes := fun v => match v with | .exit => true | _ => false
  goal := fun v => match v with | .exit => true | _ => false

def shortening : SignedRankGraph.Input Node :=
  { extending with minimizes := fun v => match v with | .a => true | .b => false | .exit => true }

def oppositeView : SignedRankGraph.Input Node :=
  { extending with
    moves := fun v => match v with | .a => [.exit, .b] | .b => [.exit] | .exit => [.exit]
    nonempty := by intro v; cases v <;> simp
    minimizes := fun v => match v with | .a => false | _ => true }

theorem extending_a : extending.rank 3 .a = none := by decide
theorem extending_b : extending.rank 3 .b = none := by decide
theorem exit_rank : extending.rank 3 .exit = some 0 := by decide
theorem shortening_a : shortening.rank 3 .a = some 1 := by decide
theorem shortening_b : shortening.rank 3 .b = some 2 := by decide
theorem opposite_a : oppositeView.rank 3 .a = some 2 := by decide
theorem opposite_b : oppositeView.rank 3 .b = some 1 := by decide

theorem negative_prefers_loop : extending.preferred 3 .a .b := by
  refine ⟨by decide, rfl, ?_⟩
  intro other member _
  cases other with
  | a => simp [extending] at member
  | b => decide
  | exit => decide

theorem positive_prefers_exit : shortening.preferred 3 .a .exit := by
  refine ⟨by decide, rfl, ?_⟩
  intro other member _
  cases other with
  | a => simp [shortening, extending] at member
  | b => decide
  | exit => decide

/-- 無限rankであっても相手側のbには出口があり、循環を選ぶ機会と強制は違う。 -/
theorem opponent_can_exit : .exit ∈ extending.moves .b ∧ extending.rank 3 .b = none := by decide

inductive Candidate | loop | exit | ownChecking deriving DecidableEq

def candidateRank : Candidate → PathRank.Rank
  | .loop => none
  | .exit => some 3
  | .ownChecking => none

def safe (e : Candidate) : Prop := e ≠ .ownChecking

theorem safe_loop_preferred : PathRank.Preferred (fun _ : Candidate => (-85 : Int)) candidateRank 3 safe (-85) .loop := by
  refine ⟨by simp [safe], rfl, ?_⟩
  intro other allowed _
  cases other with
  | loop => decide
  | exit => decide
  | ownChecking => exact False.elim (allowed rfl)

theorem unsafe_infinity_rejected :
    ¬ PathRank.Preferred (fun _ : Candidate => (-85 : Int)) candidateRank 3 safe (-85) .ownChecking := by
  intro accepted
  exact accepted.1 rfl

theorem unsafe_saved_lower :
    OutputPreference.encoded (fun _ : Candidate => (-85 : Int))
      (PathRank.Preferred (fun _ : Candidate => (-85 : Int)) candidateRank 3 safe (-85)) (-85) .ownChecking = -86 := by
  simp [OutputPreference.encoded, unsafe_infinity_rejected]

theorem safe_loop_saved_best :
    OutputPreference.encoded (fun _ : Candidate => (-85 : Int))
      (PathRank.Preferred (fun _ : Candidate => (-85 : Int)) candidateRank 3 safe (-85)) (-85) .loop = -85 := by
  simp [OutputPreference.encoded, safe_loop_preferred]

end PetaProof.SignedRankExamples
