import PetaProof.EscapePartition
import PetaProof.SafeEscape

/-! 成分別の最短戦略を合成し、元の合法手へ戻した場合の脱出・評価値保証。 -/
namespace PetaProof.ThresholdGame.SafeEscapeInput

universe u v
variable {V : Type u} {I : Type v} {G : ThresholdGame V}
variable {table : G.ValueRankTable} (input : SafeEscapeInput table)

theorem partition_target (label : V → I) (key : I) :
    (fun state : Option V => state.map label ≠ some key) =
      target (fun vertex => label vertex = key) := by
  funext state
  cases state <;> simp [target]

/-- 成分IDは元局面に付ける。leafのnoneは全成分に共通する脱出先として扱う。 -/
noncomputable def partitionPlan (label : V → I) (family : I → input.arena.Strategy)
    (fallback : input.arena.Strategy) : G.MovePlan :=
  input.movePlan (input.arena.partitionStrategy (fun state => state.map label) family fallback)

theorem partitionPlan_safe (label : V → I) (family : I → input.arena.Strategy)
    (fallback : input.arena.Strategy) :
    table.AdmissiblePlan (input.partitionPlan label family fallback) :=
  input.movePlan_safe _

/-- 合成した一つの選択計画で、各成分からの最短保証手数と元ゲームの値の保証を両立する。 -/
theorem partition_distance_and_score [DecidableEq V] (label : V → I)
    (family : I → input.arena.Strategy) (fallback : input.arena.Strategy)
    (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (optimal : ∀ key, input.arena.EscapeOptimal (target (fun vertex => label vertex = key))
      vertices (family key))
    (key : I) (root : V) (n : Nat)
    (inside : input.arena.escapeLayer (target (fun vertex => label vertex = key)) vertices.length (some root))
    (bound : input.arena.escapeRank (target (fun vertex => label vertex = key)) vertices.length (some root) ≤ n)
    (opponent : G.MovePlan) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans (input.partitionPlan label family fallback) opponent) root payoff) :
    withinMoves (fun vertex => label vertex = key) (input.partitionPlan label family fallback) [] n root ∧
      table.value root ≤ payoff := by
  have joined := input.arena.partitionStrategy_guarantees (fun state => state.map label) family fallback
    vertices covered (fun key => by rw [partition_target label key]; exact optimal key)
    key [] n (some root) (by rw [partition_target label key]; exact inside)
      (by rw [partition_target label key]; exact bound)
  rw [partition_target label key] at joined
  exact ⟨input.withinMoves_of_arena _ _ [] n root joined,
    input.score_guarantee _ opponent root payoff result⟩

/-- 最短戦略は既証の到達層から作る。成分ごとの正解戦略を入力として要求しない。 -/
noncomputable def shortestPartitionPlan (label : V → I) (vertices : List (Option V))
    (covered : ∀ state, state ∈ vertices) : G.MovePlan :=
  input.partitionPlan label
    (fun key => input.arena.escapeStrategy (target (fun vertex => label vertex = key)) vertices covered)
    input.arena.defaultStrategy

theorem shortestPartitionPlan_safe (label : V → I) (vertices : List (Option V))
    (covered : ∀ state, state ∈ vertices) :
    table.AdmissiblePlan (input.shortestPartitionPlan label vertices covered) :=
  input.partitionPlan_safe _ _ _

theorem shortestPartitionPlan_distance_and_score [DecidableEq V] (label : V → I)
    (vertices : List (Option V)) (covered : ∀ state, state ∈ vertices)
    (key : I) (root : V) (n : Nat)
    (inside : input.arena.escapeLayer (target (fun vertex => label vertex = key)) vertices.length (some root))
    (bound : input.arena.escapeRank (target (fun vertex => label vertex = key)) vertices.length (some root) ≤ n)
    (opponent : G.MovePlan) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans
      (input.shortestPartitionPlan label vertices covered) opponent) root payoff) :
    withinMoves (fun vertex => label vertex = key)
      (input.shortestPartitionPlan label vertices covered) [] n root ∧ table.value root ≤ payoff :=
  input.partition_distance_and_score label _ _ vertices covered
    (fun _ => input.arena.escapeStrategy_optimal _ vertices covered)
    key root n inside bound opponent payoff result

end PetaProof.ThresholdGame.SafeEscapeInput
