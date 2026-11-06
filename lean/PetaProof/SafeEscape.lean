import PetaProof.EscapeComputation
import PetaProof.ValueStratumFilter

/-! 安全なbest候補を固定した脱出グラフから元の指し手へ戻しても、評価値保証を保つ。 -/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} {G : ThresholdGame V}

structure SafeEscapeInput (table : G.ValueRankTable) where
  kept : V → Move V → Prop
  safe : ∀ vertex move, G.owner vertex = G.player → kept vertex move → table.admissibleMove vertex move
  own_nonempty : ∀ vertex, G.owner vertex = G.player → ∃ move, kept vertex move
  replies : table.AllReplies

namespace SafeEscapeInput

variable {table : G.ValueRankTable} (input : SafeEscapeInput table)

def permitted (vertex : V) (move : Move V) : Prop :=
  if G.owner vertex = G.player then input.kept vertex move else G.legal vertex move

theorem permitted_legal (vertex : V) (move : Move V) (allowed : input.permitted vertex move) :
    G.legal vertex move := by
  by_cases own : G.owner vertex = G.player
  · rw [permitted, if_pos own] at allowed
    exact (input.safe vertex move own allowed).1
  · simpa only [permitted, if_neg own] using allowed

theorem permitted_exists (vertex : V) : ∃ move, input.permitted vertex move := by
  by_cases own : G.owner vertex = G.player
  · simpa only [permitted, if_pos own] using input.own_nonempty vertex own
  · simpa only [permitted, if_neg own] using G.nonempty_moves vertex

/-- noneはleafへ出たことを表す。目標到達後の自己辺は全域化のためだけに使う。 -/
def edge : Option V → Option V → Prop
  | none, child => child = none
  | some vertex, some child => input.permitted vertex (.node child)
  | some vertex, none => ∃ score, input.permitted vertex (.leaf score)

def arena : HistoryArena (Option V) where
  edge := input.edge
  owner := fun vertex => match vertex with | some v => G.owner v | none => G.player
  player := G.player
  bad := fun _ _ => False
  moves_exist := by
    intro state
    cases state with
    | none => exact ⟨none, rfl⟩
    | some vertex =>
      obtain ⟨move, allowed⟩ := input.permitted_exists vertex
      cases move with
      | node child => exact ⟨some child, allowed⟩
      | leaf score => exact ⟨none, score, allowed⟩

def target (component : V → Prop) : Option V → Prop
  | none => True
  | some vertex => ¬ component vertex

def encode : Move V → Option V
  | .node vertex => some vertex
  | .leaf _ => none

noncomputable def realize (vertex : V) (child : Option V) (law : input.edge (some vertex) child) : Move V :=
  match child with
  | some next => .node next
  | none => .leaf (Classical.choose law)

theorem realize_spec (vertex : V) (child : Option V) (law : input.edge (some vertex) child) :
    input.permitted vertex (input.realize vertex child law) ∧ encode (input.realize vertex child law) = child := by
  cases child with
  | some next => exact ⟨law, rfl⟩
  | none => exact ⟨Classical.choose_spec law, rfl⟩

noncomputable def movePlan (strategy : input.arena.Strategy) : G.MovePlan := by
  classical
  let choose := fun past vertex => if own : G.owner vertex = G.player then
    input.realize vertex (strategy.choose (past.map some) (some vertex)) (strategy.legal _ _ own)
    else G.defaultPlan.choose past vertex
  exact {
    choose := choose
    legal := by
      intro past vertex
      simp only [choose]
      split
      · exact input.permitted_legal vertex _ (input.realize_spec _ _ _).1
      · exact G.defaultPlan.legal past vertex
  }

theorem movePlan_permitted (strategy : input.arena.Strategy) (past : List V) (vertex : V)
    (own : G.owner vertex = G.player) : input.permitted vertex ((input.movePlan strategy).choose past vertex) := by
  classical
  simpa only [movePlan, dif_pos own] using
    (input.realize_spec vertex (strategy.choose (past.map some) (some vertex)) (strategy.legal _ _ own)).1

theorem movePlan_encode (strategy : input.arena.Strategy) (past : List V) (vertex : V)
    (own : G.owner vertex = G.player) : encode ((input.movePlan strategy).choose past vertex) =
      strategy.choose (past.map some) (some vertex) := by
  classical
  simpa only [movePlan, dif_pos own] using
    (input.realize_spec vertex (strategy.choose (past.map some) (some vertex)) (strategy.legal _ _ own)).2

theorem movePlan_safe (strategy : input.arena.Strategy) : table.AdmissiblePlan (input.movePlan strategy) := by
  intro past vertex own
  have allowed := input.movePlan_permitted strategy past vertex own
  rw [permitted, if_pos own] at allowed
  exact input.safe vertex _ own allowed

theorem score_guarantee [DecidableEq V] (strategy : input.arena.Strategy) (opponent : G.MovePlan)
    (root : V) (payoff : Int) (result : G.TerminalResult (G.combinePlans (input.movePlan strategy) opponent) root payoff) :
    table.value root ≤ payoff :=
  table.terminal_lower input.replies _ opponent (input.movePlan_safe strategy) root payoff result

/-- 元の指し手列でも、leafまたは成分外への最初の到達を数える。千日手の終局判定とは別の量。 -/
def withinMoves (component : V → Prop) (plan : G.MovePlan) : List V → Nat → V → Prop
  | _, 0, vertex => ¬ component vertex
  | past, n + 1, vertex => ¬ component vertex ∨
      ∀ move, G.legal vertex move → (G.owner vertex = G.player → plan.choose past vertex = move) →
        match move with
        | .leaf _ => True
        | .node child => withinMoves component plan (past ++ [vertex]) n child

/-- グラフ上の保証手数を、選び直した元の合法手に対しても保つ。 -/
theorem withinMoves_of_arena (component : V → Prop) (strategy : input.arena.Strategy)
    (past : List V) (n : Nat) (vertex : V)
    (guaranteed : input.arena.escapeWithin (target component) strategy (past.map some) n (some vertex)) :
    withinMoves component (input.movePlan strategy) past n vertex := by
  induction n generalizing past vertex with
  | zero => exact guaranteed
  | succ n ih =>
    rcases guaranteed with goal | replies
    · exact Or.inl goal
    · right
      intro move legal selected
      cases move with
      | leaf score => trivial
      | node child =>
        have allowed : input.permitted vertex (.node child) := by
          by_cases own : G.owner vertex = G.player
          · rw [← selected own]
            exact input.movePlan_permitted strategy past vertex own
          · simpa only [permitted, if_neg own] using legal
        have compatible : input.arena.owner (some vertex) = input.arena.player →
            some child = strategy.choose (past.map some) (some vertex) := by
          intro own
          have encoded := input.movePlan_encode strategy past vertex own
          rw [selected own] at encoded
          exact encoded
        have next := replies (some child) allowed compatible
        apply ih (past ++ [vertex]) child
        simpa only [List.map_append, List.map_cons, List.map_nil] using next

/-- 計算した最短手を元のbest候補へ戻した計画について、脱出上界と評価値保証を同時に得る。 -/
theorem distance_and_score [DecidableEq V] (component : V → Prop)
    (graph : HistoryArena.EscapeInput input.arena (target component))
    (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (root : V) (n : Nat) (computed : graph.computedDistance vertices.length (some root) = some n)
    (opponent : G.MovePlan) (payoff : Int)
    (result : G.TerminalResult
      (G.combinePlans (input.movePlan (graph.computedStrategy vertices.length)) opponent) root payoff) :
    withinMoves component (input.movePlan (graph.computedStrategy vertices.length)) [] n root ∧
      table.value root ≤ payoff := by
  have layer := ((graph.computedDistance_some vertices.length n (some root)).mp computed).2.1
  have inside := input.arena.escapeLayer_complete (target component) vertices covered n (some root) layer
  have rank := (input.arena.escapeRank_le_iff (target component) vertices.length (some root) inside n).mpr layer
  have guaranteed := input.arena.escapeOptimal_guarantees (target component) vertices covered _
    (graph.computedStrategy_optimal vertices covered) [] n (some root) inside rank
  exact ⟨input.withinMoves_of_arena component _ [] n root guaranteed, input.score_guarantee _ opponent root payoff result⟩

end SafeEscapeInput
end PetaProof.ThresholdGame
