import PetaProof.Determinacy

/-!
勝敗が混在し、相手には勝ち領域へ出る手もある例。
補集合内の反証手を選び、自分の合法手を削っていないことを検査する。
-/

namespace PetaProof.DeterminacyExamples

inductive Node where
  | win | ownLose | replyLose
  deriving DecidableEq

open Node

def arena : HistoryArena Node where
  edge := fun v w => match v with
    | .win => w = .win
    | .ownLose => w = .replyLose
    | .replyLose => w = .ownLose ∨ w = .win
  owner := fun v => match v with
    | .replyLose => true
    | _ => false
  player := false
  bad := fun v _ => v = .replyLose
  moves_exist := by
    intro v
    cases v with
    | win => exact ⟨.win, rfl⟩
    | ownLose => exact ⟨.replyLose, rfl⟩
    | replyLose => exact ⟨.ownLose, Or.inl rfl⟩

def vertices : List Node := [.win, .ownLose, .replyLose]

theorem covered (v : Node) : v ∈ vertices := by cases v <;> simp [vertices]

def won (v : Node) : Prop := v = .win

def policy : arena.RankedPolicy won where
  choice := fun v => match v with
    | .ownLose => .replyLose
    | _ => .win
  legal := by intro v own; cases v <;> simp_all [arena]
  rank := fun _ => 0
  ceiling := 0
  bounded := by intro _ _; exact Nat.le_refl _
  closed := by
    intro v w hv follows
    subst v
    exact follows.1
  decreasing := by intro _ _ _ _; exact Nat.le_refl _
  strict_bad := by
    intro v w hv _ hb
    subst v
    simp [arena] at hb

/-- 2頂点の循環に悪い辺があり、どんな順位付き方策でもその領域を保証できない。 -/
theorem own_not_in_policy {possible : Node → Prop} (other : arena.RankedPolicy possible) :
    ¬ possible .ownLose := by
  intro inside
  have selected : other.choice .ownLose = .replyLose := other.legal .ownLose rfl
  have forward : arena.FollowsChoice other.choice .ownLose .replyLose :=
    ⟨rfl, fun _ => selected.symm⟩
  have backward : arena.FollowsChoice other.choice .replyLose .ownLose :=
    ⟨Or.inl rfl, by intro own; simp [arena] at own⟩
  have reply := other.closed .ownLose .replyLose inside forward
  have weak := other.decreasing .ownLose .replyLose inside forward
  have strict := other.strict_bad .replyLose .ownLose reply backward rfl
  omega

theorem maximal : arena.PolicyMaximal won := by
  intro possible other v inside
  cases v with
  | win => rfl
  | ownLose => exact False.elim (own_not_in_policy other inside)
  | replyLose =>
    have backward : arena.FollowsChoice other.choice .replyLose .ownLose :=
      ⟨Or.inl rfl, by intro own; simp [arena] at own⟩
    exact False.elim (own_not_in_policy other (other.closed _ _ inside backward))

theorem exact_history (v : Node) : arena.HistoryWinning v ↔ v = .win :=
  (arena.maximal_policy_exact_history policy maximal vertices covered v).symm

def ordinary : arena.OrdinaryClosed won := arena.maximal_policy_ordinary policy maximal

def residual := arena.complementTrap ordinary

noncomputable def constructedCounter : residual.restricted.Counterstrategy :=
  Classical.choice (arena.residual_counter_exists policy maximal ordinary vertices covered)

/-- 相手には勝ち領域へ出る合法手もあるが、反証方策はそれを選ばない。 -/
theorem opponent_has_winning_exit : arena.edge .replyLose .win := Or.inr rfl

theorem counter_stays_losing : residual.liftResponse constructedCounter .replyLose = .ownLose := by
  have edge := residual.liftResponse_legal constructedCounter .replyLose (by decide)
  have inside := residual.liftResponse_stays constructedCounter .replyLose
    (residual.liftResponse constructedCounter .replyLose) (by simp [won])
    ⟨edge, fun _ => rfl⟩
  change residual.liftResponse constructedCounter .replyLose = .ownLose ∨
    residual.liftResponse constructedCounter .replyLose = .win at edge
  rcases edge with stays | leaves
  · exact stays
  · exact False.elim (inside leaves)

/-- 自分の合法手の行き先を削るような切り出しは、Trapの条件を満たさない。 -/
theorem cannot_remove_own_moves : ¬ arena.Trap (fun v => v = .ownLose) := by
  intro invalid
  have wrong := invalid.own_closed .ownLose .replyLose rfl rfl rfl
  cases wrong

theorem generic_determinacy_applies :
    ∃ region, Nonempty (arena.RankedPolicy region) ∧
      (∀ v, region v ↔ arena.HistoryWinning v) ∧
      ∃ closed : arena.OrdinaryClosed region,
        Nonempty (arena.complementTrap closed).restricted.Counterstrategy :=
  arena.memoryless_determinacy vertices covered

end PetaProof.DeterminacyExamples
