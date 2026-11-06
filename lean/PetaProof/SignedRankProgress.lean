import PetaProof.SignedRankGame
import PetaProof.SafeEscape

/-! 符号別選択が有限rankを減らすことと、相手の全応手に対する脱出上界。 -/
namespace PetaProof.ThresholdGame.SignedRank.Input

universe u
variable {V : Type u} {G : ThresholdGame V} {table : G.ValueRankTable} (input : Input table)

theorem selected_child_rank (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (history : List V) (vertex child : V) (d : Nat)
    (found : input.graph.rank vertices.length (some vertex) = some d)
    (notGoal : ¬ input.graph.target (some vertex))
    (legal : G.legal vertex (.node child))
    (selected : G.owner vertex = G.player → (input.plan vertices.length).choose history vertex = .node child) :
    ∃ k, input.graph.rank vertices.length (some child) = some k ∧ k + 1 ≤ d := by
  by_cases own : G.owner vertex = G.player
  · have preferred : input.preferred vertices.length vertex (.node child) := by
      rw [← selected own]
      exact input.plan_preferred _ history vertex own
    obtain ⟨k, next, equal⟩ := input.graph.preferred_finite vertices covered (some vertex) (some child)
      notGoal (input.preferred_graph _ vertex own _ preferred) d found
    exact ⟨k, next, by omega⟩
  · have member := input.all_replies vertex own (.node child) legal
    have edge : some child ∈ input.graph.moves (some vertex) :=
      List.mem_map.mpr ⟨.node child, member, rfl⟩
    have large : input.graph.minimizes (some vertex) = false := by simp [graph, own]
    exact input.graph.finite_max_all vertices covered (some vertex) d found notGoal large (some child) edge

/-- 有限rankなら、負値最大・非負最小の実選択と相手の全応手にも同じ手数上界が成立する。 -/
theorem plan_within (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (n : Nat) (history : List V) (vertex : V) (d : Nat)
    (found : input.graph.rank vertices.length (some vertex) = some d) (bound : d ≤ n) :
    SafeEscapeInput.withinMoves (fun vertex => input.goal vertex = false)
      (input.plan vertices.length) history n vertex := by
  induction n generalizing history vertex d with
  | zero =>
    have equal : d = 0 := by omega
    subst d
    have goal := ((input.graph.computation.computedDistance_some vertices.length 0 (some vertex)).mp found).2.1
    change input.goal vertex = true at goal
    change ¬ input.goal vertex = false
    simp [goal]
  | succ n ih =>
    by_cases goal : input.goal vertex = true
    · left
      simp [goal]
    · right
      intro move legal follows
      cases move with
      | leaf score => trivial
      | node child =>
        have notGoal : ¬ input.graph.target (some vertex) := goal
        obtain ⟨k, next, upper⟩ := input.selected_child_rank vertices covered history vertex child d
          found notGoal legal follows
        exact ih (history ++ [vertex]) child k next (by omega)

theorem plan_distance_and_score [DecidableEq V] (replies : table.AllReplies)
    (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (root : V) (n : Nat) (found : input.graph.rank vertices.length (some root) = some n)
    (opponent : G.MovePlan) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans (input.plan vertices.length) opponent) root payoff) :
    SafeEscapeInput.withinMoves (fun vertex => input.goal vertex = false)
      (input.plan vertices.length) [] n root ∧ table.value root ≤ payoff :=
  ⟨input.plan_within vertices covered n [] root n found (Nat.le_refl _),
    input.plan_lower replies _ opponent root payoff result⟩

/-- 自分は実際の符号別出力手、相手は延長を実現する応手を選ぶ参照経路。 -/
noncomputable def prolong (cap : Nat) : Option V → Option V
  | none => none
  | some vertex => if G.owner vertex = G.player then
      encode ((input.plan cap).choose [] vertex)
    else input.graph.next cap (some vertex)

theorem prolong_preferred (cap : Nat) (vertex : V) :
    input.graph.preferred cap (some vertex) (input.prolong cap (some vertex)) := by
  by_cases own : G.owner vertex = G.player
  · simpa only [prolong, if_pos own] using
      input.preferred_graph cap vertex own _ (input.plan_preferred cap [] vertex own)
  · simpa only [prolong, if_neg own] using input.graph.next_preferred cap (some vertex)

theorem prolong_legal (cap : Nat) (state : Option V) : input.prolong cap state ∈ input.graph.moves state := by
  cases state with
  | none => simp [prolong, graph]
  | some vertex => exact (input.prolong_preferred cap vertex).1

/-- 無限rankは、実際に選んだ自分の手と両立する延長経路を持つ。相手の全応手への強制ではない。 -/
theorem plan_infinite_opportunity (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (root : V) (infinite : input.graph.rank vertices.length (some root) = none) :
    ∀ n, input.graph.rank vertices.length
      (SignedRankGraph.Input.run (input.prolong vertices.length) (some root) n) = none ∧
      ¬ input.graph.target (SignedRankGraph.Input.run (input.prolong vertices.length) (some root) n) := by
  have step : ∀ state, input.graph.rank vertices.length state = none →
      input.graph.rank vertices.length (input.prolong vertices.length state) = none := by
    intro state found
    cases state with
    | none =>
      have zero := input.graph.goal_rank vertices.length none (by rfl)
      rw [found] at zero
      cases zero
    | some vertex =>
      exact input.graph.preferred_infinite vertices covered _ _
        (input.prolong_preferred vertices.length vertex) found
  have stays : ∀ n, input.graph.rank vertices.length
      (SignedRankGraph.Input.run (input.prolong vertices.length) (some root) n) = none := by
    intro n
    induction n with
    | zero => exact infinite
    | succ n ih => exact step _ ih
  intro n
  refine ⟨stays n, ?_⟩
  intro goal
  have zero := input.graph.goal_rank vertices.length _ goal
  rw [stays n] at zero
  cases zero

end PetaProof.ThresholdGame.SignedRank.Input
