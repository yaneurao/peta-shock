import PetaProof.SignedRankGraph
import PetaProof.PathRankOutput
import PetaProof.GeneratedOutputSafety

/-! 固定プレイヤー視点で、非負の自分番を短縮、負の自分番を延長するrankと安全な出力。 -/
namespace PetaProof.ThresholdGame.SignedRank

universe u v
variable {V : Type u} {G : ThresholdGame V}

structure Input (table : G.ValueRankTable) where
  rows : V → List (Move V)
  nonempty : ∀ vertex, rows vertex ≠ []
  legal : ∀ vertex move, move ∈ rows vertex → G.legal vertex move
  safe : ∀ vertex, G.owner vertex = G.player → ∀ move, move ∈ rows vertex → table.admissibleMove vertex move
  best : ∀ vertex, G.owner vertex = G.player → ∀ move, move ∈ rows vertex →
    moveValue table.value move = table.value vertex
  all_replies : ∀ vertex, G.owner vertex ≠ G.player → ∀ move, G.legal vertex move → move ∈ rows vertex
  goal : V → Bool

/-- 元の有限出辺から自分の安全なbestだけを残す。相手の全合法手は残す。 -/
noncomputable def ofIndexed {E : Type v} (table : G.ValueRankTable) (indexed : G.IndexedMoves E)
    (available : ∀ vertex, G.owner vertex = G.player →
      ∃ move, table.admissibleMove vertex move ∧ moveValue table.value move = table.value vertex)
    (goal : V → Bool) : Input table := by
  classical
  let allowed := fun vertex move => G.owner vertex ≠ G.player ∨
    (table.admissibleMove vertex move ∧ moveValue table.value move = table.value vertex)
  let rows := fun vertex => ((indexed.outgoing vertex).filter
    (fun edge => decide (allowed vertex (indexed.move edge)))).map indexed.move
  have membership : ∀ vertex move, move ∈ rows vertex ↔ G.legal vertex move ∧ allowed vertex move := by
    intro vertex move
    constructor
    · intro member
      obtain ⟨edge, kept, same⟩ := List.mem_map.mp member
      have parts := List.mem_filter.mp kept
      have legal := indexed.legal vertex edge parts.1
      have permitted : allowed vertex (indexed.move edge) := of_decide_eq_true parts.2
      exact same ▸ ⟨legal, permitted⟩
    · rintro ⟨legal, permitted⟩
      obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
      apply List.mem_map.mpr
      refine ⟨edge, List.mem_filter.mpr ⟨member, ?_⟩, same⟩
      simpa only [same, decide_eq_true_eq] using permitted
  refine ⟨rows, ?_, ?_, ?_, ?_, ?_, goal⟩
  · intro vertex empty
    have present : ∃ move, move ∈ rows vertex := by
      by_cases own : G.owner vertex = G.player
      · obtain ⟨move, safe, best⟩ := available vertex own
        exact ⟨move, (membership vertex move).mpr ⟨safe.1, Or.inr ⟨safe, best⟩⟩⟩
      · obtain ⟨move, legal⟩ := G.nonempty_moves vertex
        exact ⟨move, (membership vertex move).mpr ⟨legal, Or.inl own⟩⟩
    obtain ⟨move, member⟩ := present
    rw [empty] at member
    exact List.not_mem_nil member
  · intro vertex move member
    exact ((membership vertex move).mp member).1
  · intro vertex own move member
    have permitted := ((membership vertex move).mp member).2
    exact (permitted.resolve_left (fun other => other own)).1
  · intro vertex own move member
    have permitted := ((membership vertex move).mp member).2
    exact (permitted.resolve_left (fun other => other own)).2
  · intro vertex other move legal
    exact (membership vertex move).mpr ⟨legal, Or.inl other⟩

namespace Input
variable {table : G.ValueRankTable} (input : Input table)

def encode : Move V → Option V
  | .leaf _ => none
  | .node child => some child

/-- 相手の応手は延長側として残す。負値では引き分けの機会を比較するのであり、強制を主張しない。 -/
def graph : SignedRankGraph.Input (Option V) where
  moves := fun state => match state with
    | none => [none]
    | some vertex => (input.rows vertex).map encode
  nonempty := by
    intro state
    cases state with
    | none => simp
    | some vertex => simpa using input.nonempty vertex
  minimizes := fun state => match state with
    | none => true
    | some vertex => decide (G.owner vertex = G.player ∧ 0 ≤ table.value vertex)
  goal := fun state => match state with
    | none => true
    | some vertex => input.goal vertex

def moveRank (cap : Nat) (move : Move V) : PathRank.Rank :=
  (input.graph.rank cap (encode move)).map Nat.succ

theorem moveRank_bound (cap : Nat) (move : Move V) : PathRank.Bounded (cap + 1) (input.moveRank cap move) := by
  intro n found
  have bound := input.graph.rank_bound cap (encode move)
  unfold moveRank at found
  cases rank : input.graph.rank cap (encode move) with
  | none => simp [rank] at found
  | some k =>
    have limit := bound k rank
    simp [rank] at found
    omega

def preferred (cap : Nat) (vertex : V) : Move V → Prop :=
  PathRank.Preferred (moveValue table.value) (input.moveRank cap) (cap + 1)
    (fun move => move ∈ input.rows vertex) (table.value vertex)

theorem preferred_exists (cap : Nat) (vertex : V) (own : G.owner vertex = G.player) :
    ∃ move ∈ input.rows vertex, input.preferred cap vertex move := by
  obtain ⟨move, member⟩ : ∃ move, move ∈ input.rows vertex := by
    cases found : input.rows vertex with
    | nil => exact False.elim (input.nonempty vertex found)
    | cons first rest => exact ⟨first, by simp [found]⟩
  exact PathRank.preferred_exists _ _ _ _ _ (input.rows vertex) (fun _ member => member)
    ⟨move, member, member, input.best vertex own move member⟩

noncomputable def plan (cap : Nat) : G.MovePlan where
  choose := fun _ vertex => if own : G.owner vertex = G.player then
    Classical.choose (input.preferred_exists cap vertex own)
    else G.defaultPlan.choose [] vertex
  legal := by
    intro history vertex
    split
    · rename_i own
      exact input.legal vertex _ (Classical.choose_spec (input.preferred_exists cap vertex own)).1
    · exact G.defaultPlan.legal [] vertex

theorem plan_preferred (cap : Nat) (history : List V) (vertex : V) (own : G.owner vertex = G.player) :
    input.preferred cap vertex ((input.plan cap).choose history vertex) := by
  simp only [plan, dif_pos own]
  exact (Classical.choose_spec (input.preferred_exists cap vertex own)).2

theorem plan_admissible (cap : Nat) : table.AdmissiblePlan (input.plan cap) := by
  intro history vertex own
  have chosen := input.plan_preferred cap history vertex own
  exact input.safe vertex own _ chosen.1

theorem plan_lower [DecidableEq V] (replies : table.AllReplies) (cap : Nat)
    (opponent : G.MovePlan) (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans (input.plan cap) opponent) root payoff) : table.value root ≤ payoff :=
  table.terminal_lower replies _ opponent (input.plan_admissible cap) root payoff result

/-- 負値なら無限の安全な同点手を優先する。rankは入力せず有限出辺から計算している。 -/
theorem negative_plan_infinite (cap : Nat) (history : List V) (vertex : V)
    (own : G.owner vertex = G.player) (negative : table.value vertex < 0)
    (other : Move V) (member : other ∈ input.rows vertex)
    (infinite : input.moveRank cap other = none) :
    input.moveRank cap ((input.plan cap).choose history vertex) = none :=
  PathRank.negative_prefers_infinite _ _ _ _ _ _ other
    (input.plan_preferred cap history vertex own) negative (input.moveRank_bound cap _)
    member (input.best vertex own other member) infinite

theorem plan_direction (cap : Nat) (history : List V) (vertex : V)
    (own : G.owner vertex = G.player) (other : Move V) (member : other ∈ input.rows vertex) :
    (0 ≤ table.value vertex → PathRank.LE (input.moveRank cap ((input.plan cap).choose history vertex))
      (input.moveRank cap other)) ∧
    (table.value vertex < 0 → PathRank.LE (input.moveRank cap other)
      (input.moveRank cap ((input.plan cap).choose history vertex))) :=
  PathRank.preferred_direction _ _ _ _ _ _ other (input.plan_preferred cap history vertex own)
    (input.moveRank_bound cap _) (input.moveRank_bound cap other) member (input.best vertex own other member)

/-- 実際の負値最大・非負最小の選別が、生成グラフのmin/maxと同じ比較を使うこと。 -/
theorem preferred_graph (cap : Nat) (vertex : V) (own : G.owner vertex = G.player)
    (move : Move V) (chosen : input.preferred cap vertex move) :
    input.graph.preferred cap (some vertex) (encode move) := by
  refine ⟨List.mem_map.mpr ⟨move, chosen.1, rfl⟩, rfl, ?_⟩
  intro other member _
  obtain ⟨next, kept, same⟩ := List.mem_map.mp member
  rw [← same]
  have compare := chosen.2.2 next kept (input.best vertex own next kept)
  change (if 0 ≤ (if input.graph.minimizes (some vertex) then (0 : Int) else -1) then
    PathRank.code (cap + 1) (input.moveRank cap move) ≤ PathRank.code (cap + 1) (input.moveRank cap next)
    else PathRank.code (cap + 1) (input.moveRank cap next) ≤ PathRank.code (cap + 1) (input.moveRank cap move))
  by_cases nonnegative : 0 ≤ table.value vertex
  · have flag : input.graph.minimizes (some vertex) = true := by simp [graph, own, nonnegative]
    rw [flag]
    simpa only [if_pos nonnegative, Bool.true_eq, if_true, Int.le_refl, if_true] using compare
  · have flag : input.graph.minimizes (some vertex) = false := by simp [graph, own, nonnegative]
    rw [flag]
    simpa only [if_neg nonnegative, Bool.false_eq_true, if_false, show ¬ (0 : Int) ≤ -1 by omega, if_false] using compare

theorem plan_rank (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (history : List V) (vertex : V) (own : G.owner vertex = G.player)
    (notGoal : ¬ input.graph.target (some vertex)) :
    input.graph.rank vertices.length (some vertex) =
      input.moveRank vertices.length ((input.plan vertices.length).choose history vertex) :=
  input.graph.preferred_rank vertices covered _ _ notGoal
    (input.preferred_graph _ vertex own _ (input.plan_preferred _ history vertex own))

theorem node_nondecreasing (replies : table.AllReplies) (vertex child : V)
    (member : Move.node child ∈ input.rows vertex) : table.value vertex ≤ table.value child := by
  by_cases own : G.owner vertex = G.player
  · exact (input.safe vertex own _ member).2.1
  · exact (replies vertex _ own (input.legal vertex _ member)).1

/-- 計算したrankで選別した後にのみ1点補正する。最大手の任意切替でも値の保証を保つ。 -/
theorem encoded_plan_lower [DecidableEq V] (replies : table.AllReplies) (cap : Nat)
    (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ move ∈ input.rows vertex, self.choose history vertex = move ∧
        ∀ other ∈ input.rows vertex,
          OutputPreference.encoded (moveValue table.value) (input.preferred cap vertex) (table.value vertex) other ≤
          OutputPreference.encoded (moveValue table.value) (input.preferred cap vertex) (table.value vertex) move)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply table.terminal_lower replies self opponent _ root payoff result
  intro history vertex own
  obtain ⟨move, member, same, maximal⟩ := selected history vertex own
  have accepted := (PathRank.encoded_maximum_iff (moveValue table.value) (input.moveRank cap) (cap + 1)
    (fun move => move ∈ input.rows vertex) (table.value vertex) (input.rows vertex)
    (fun _ member => member) (fun move member => by
      rw [input.best vertex own move member]
      exact Int.le_refl _)
    ⟨move, member, member, input.best vertex own move member⟩ move member).mp maximal
  rw [same]
  exact input.safe vertex own move accepted.1

end Input
end PetaProof.ThresholdGame.SignedRank

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

noncomputable def generatedSignedRankInput (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
    (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)
    (goal : V → Bool) : SignedRank.Input (ctx.generatedTable atTop otherCore leaves covers otherCovers) :=
  SignedRank.ofIndexed (ctx.generatedTable atTop otherCore leaves covers otherCovers) ctx.indexed
    (fun vertex own => by
      obtain ⟨edge, _, safe, same⟩ := ctx.generated_safe_best atTop otherCore leaves covers otherCovers vertex own
      exact ⟨ctx.indexed.move edge, safe, same⟩) goal

theorem generated_signed_rank_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
    (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)
    (goal : V → Bool) (cap : Nat) (opponent : G.MovePlan) (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans
      ((ctx.generatedSignedRankInput atTop otherCore leaves covers otherCovers goal).plan cap) opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff :=
  (ctx.generatedSignedRankInput atTop otherCore leaves covers otherCovers goal).plan_lower
    (ctx.generatedTable_replies atTop otherCore leaves covers otherCovers) cap opponent root payoff result

/-- 元の全出辺を保存する場合も、安全で符号別rankが優先される同点だけを最大値に残す。 -/
theorem generated_signed_rank_output_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
    (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)
    (goal : V → Bool) (cap : Nat) (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ ctx.indexed.outgoing vertex, self.choose history vertex = ctx.indexed.move edge ∧
        ∀ other ∈ ctx.indexed.outgoing vertex,
          OutputPreference.encoded (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
            (PathRank.Preferred (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
              (fun e => (ctx.generatedSignedRankInput atTop otherCore leaves covers otherCovers goal).moveRank cap (ctx.indexed.move e))
              (cap + 1) (fun e => e ∈ ctx.indexed.outgoing vertex ∧
                (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex (ctx.indexed.move e))
              (ctx.generatedValue otherCore vertex)) (ctx.generatedValue otherCore vertex) other ≤
          OutputPreference.encoded (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
            (PathRank.Preferred (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
              (fun e => (ctx.generatedSignedRankInput atTop otherCore leaves covers otherCovers goal).moveRank cap (ctx.indexed.move e))
              (cap + 1) (fun e => e ∈ ctx.indexed.outgoing vertex ∧
                (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex (ctx.indexed.move e))
              (ctx.generatedValue otherCore vertex)) (ctx.generatedValue otherCore vertex) edge)
    (root : V) (payoff : Int) (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff := by
  apply PathRank.encoded_plan_lower
    (ctx.generatedTable atTop otherCore leaves covers otherCovers)
    (ctx.generatedTable_replies atTop otherCore leaves covers otherCovers)
    ctx.indexed.outgoing ctx.indexed.move
    (fun _ edge => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge))
    (fun _ edge => (ctx.generatedSignedRankInput atTop otherCore leaves covers otherCovers goal).moveRank cap (ctx.indexed.move edge))
    (cap + 1) (ctx.generatedValue otherCore) _ _ self opponent selected root payoff result
  · intro vertex own edge member
    exact ctx.generated_moveValue_upper atTop otherCore leaves covers otherCovers vertex own _
      (ctx.indexed.legal vertex edge member)
  · exact ctx.generated_safe_best atTop otherCore leaves covers otherCovers

end PetaProof.ThresholdGame.QueueContext
