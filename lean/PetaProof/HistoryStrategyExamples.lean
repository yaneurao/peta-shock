import PetaProof.HistoryStrategy

/-! 同じ局面でも履歴により異なる手を選ぶ戦略を、反証方策と実際に対局させる。 -/
namespace PetaProof.HistoryStrategyExamples

inductive Node where
  | own | left | right
  deriving DecidableEq

open Node

def arena : HistoryArena Node where
  edge := fun v w => match v with
    | .own => w ≠ .own
    | _ => w = .own
  owner := fun v => match v with
    | .own => false
    | _ => true
  player := false
  bad := fun v _ => v ≠ .own
  moves_exist := by
    intro v
    cases v with
    | own => exact ⟨.left, by decide⟩
    | left => exact ⟨.own, rfl⟩
    | right => exact ⟨.own, rfl⟩

def counter : arena.Counterstrategy where
  response := fun _ => .own
  legal := by intro v other; cases v <;> simp_all [arena]
  ranking := {
    rank := fun v => match v with
      | .own => 1
      | _ => 0
    strict_good := by
      intro v w edge nonbad
      cases v <;> cases w <;> simp_all [arena, HistoryArena.FollowsResponse]
  }

def memoryStrategy : arena.Strategy where
  choose := fun past _ => if past.length % 4 = 0 then .left else .right
  legal := by
    intro past v own
    cases v with
    | own =>
      change (if past.length % 4 = 0 then Node.left else Node.right) ≠ Node.own
      split <;> decide
    | left => simp [arena] at own
    | right => simp [arena] at own

def path : Nat → Node := arena.play memoryStrategy counter.response .own

/-- 0手目と2手目は同じ局面だが、選択手は異なる。履歴不要戦略のテストではない。 -/
theorem genuinely_history_dependent :
    path 0 = path 2 ∧ path 1 = .left ∧ path 3 = .right := by
  decide

theorem all_history_strategies_lose :
    ∀ root : Node, ¬ arena.HistoryWinning root :=
  counter.not_history_winning arena

theorem generated_path_infinitely_bad :
    ∀ n, ∃ i, n ≤ i ∧ arena.bad (path i) (path (i + 1)) :=
  counter.defeats_history arena memoryStrategy .own

theorem nonbad_gap_at_most_one (strategy : arena.Strategy) (root : Node) (n : Nat) :
    ∃ i, n ≤ i ∧ i ≤ n + 1 ∧
      arena.bad (arena.play strategy counter.response root i)
        (arena.play strategy counter.response root (i + 1)) := by
  obtain ⟨i, after, bound, hb⟩ := counter.ranking.bad_within_rank
    (arena.play strategy counter.response root) (arena.play_follows strategy counter root) n
  refine ⟨i, after, ?_, hb⟩
  have small : counter.ranking.rank (arena.play strategy counter.response root n) ≤ 1 := by
    generalize arena.play strategy counter.response root n = v
    cases v <;> decide
  omega

end PetaProof.HistoryStrategyExamples
