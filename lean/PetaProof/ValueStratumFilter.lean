import PetaProof.ValueStratumFamily
import PetaProof.CountedRowOps

/-! 値の層を統合した一つの候補表を、元辺の一回の安定filterで生成する。 -/
namespace PetaProof.ValueStratumFilter

universe u v w
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

structure Input (table : G.ValueRankTable) (E : Type v) where
  indexed : G.IndexedMoves E
  checked : V → V → Bool
  checked_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace Input

variable {table : G.ValueRankTable} (input : Input table E)

def sameLevelFlag (vertex child : V) : Bool :=
  if 0 < table.value vertex then
    decide (table.rank (table.value vertex) child ≤ table.rank (table.value vertex) vertex) &&
      (decide (G.owner vertex = G.player) || input.checked vertex child ||
        decide (table.rank (table.value vertex) child < table.rank (table.value vertex) vertex))
  else if -G.mate < table.value vertex then
    (decide (G.owner vertex = G.player) && !input.checked vertex child) ||
      decide (table.rank (table.value vertex) child < table.rank (table.value vertex) vertex)
  else true

theorem sameLevelFlag_spec (vertex child : V) :
    input.sameLevelFlag vertex child = true ↔ table.sameLevelCondition vertex child := by
  classical
  have unchecked : input.checked vertex child = false ↔ ¬ G.check vertex child := by
    rw [← input.checked_correct vertex child]
    cases input.checked vertex child <;> decide
  by_cases positive : 0 < table.value vertex <;> by_cases better : -G.mate < table.value vertex <;>
    by_cases own : G.owner vertex = G.player <;> by_cases check : G.check vertex child <;>
    simp [sameLevelFlag, ThresholdGame.ValueRankTable.sameLevelCondition,
      input.checked_correct, unchecked, positive, better, own, check]

def conditionFlag (vertex : V) : Move V → Bool
  | .leaf score => decide (table.value vertex ≤ score)
  | .node child => decide (table.value vertex ≤ table.value child) &&
      (decide (table.value child ≠ table.value vertex) || input.sameLevelFlag vertex child)

theorem conditionFlag_spec (vertex : V) (move : Move V) :
    input.conditionFlag vertex move = true ↔ table.candidateCondition vertex move := by
  cases move with
  | leaf score => simp [conditionFlag, ThresholdGame.ValueRankTable.candidateCondition]
  | node child =>
    by_cases same : table.value child = table.value vertex <;>
      simp [conditionFlag, ThresholdGame.ValueRankTable.candidateCondition, input.sameLevelFlag_spec, same]

def kept (vertex : V) : List E :=
  (input.indexed.outgoing vertex).filter (fun edge => input.conditionFlag vertex (input.indexed.move edge))

theorem kept_iff (vertex : V) (edge : E) : edge ∈ input.kept vertex ↔
    edge ∈ input.indexed.outgoing vertex ∧ table.admissibleMove vertex (input.indexed.move edge) := by
  simp only [kept, List.mem_filter, input.conditionFlag_spec]
  constructor
  · rintro ⟨member, condition⟩
    exact ⟨member, input.indexed.legal vertex edge member, condition⟩
  · rintro ⟨member, _, condition⟩
    exact ⟨member, condition⟩

theorem all_replies_survive (replies : table.AllReplies) (vertex : V) (other : G.owner vertex ≠ G.player)
    (edge : E) (member : edge ∈ input.indexed.outgoing vertex) : edge ∈ input.kept vertex :=
  (input.kept_iff vertex edge).mpr ⟨member, input.indexed.legal vertex edge member,
    replies vertex _ other (input.indexed.legal vertex edge member)⟩

theorem nonempty_of_safe (vertex : V) (move : Move V) (safe : table.admissibleMove vertex move) :
    ∃ edge ∈ input.kept vertex, input.indexed.move edge = move := by
  obtain ⟨edge, member, same⟩ := input.indexed.covers vertex move safe.1
  exact ⟨edge, (input.kept_iff vertex edge).mpr ⟨member, same ▸ safe⟩, same⟩

def counted (vertex : V) : List E × Nat :=
  CountedRowOps.filter (fun edge => input.conditionFlag vertex (input.indexed.move edge)) (input.indexed.outgoing vertex)

theorem counted_spec (vertex : V) :
    (input.counted vertex).1 = input.kept vertex ∧
      (input.counted vertex).2 = (input.indexed.outgoing vertex).length + (input.kept vertex).length :=
  CountedRowOps.filter_spec _ _

theorem counted_bound (vertex : V) : (input.counted vertex).2 ≤ 2 * (input.indexed.outgoing vertex).length := by
  have count := (input.counted_spec vertex).2
  have bound := List.length_filter_le (fun edge => input.conditionFlag vertex (input.indexed.move edge))
    (input.indexed.outgoing vertex)
  change (input.kept vertex).length ≤ _ at bound
  omega

theorem total_bound (vertices : List V) :
    (vertices.map (fun vertex => (input.counted vertex).2)).sum ≤
      2 * (vertices.flatMap input.indexed.outgoing).length := by
  induction vertices with
  | nil => exact Nat.le_refl _
  | cons vertex rest ih =>
    have row := input.counted_bound vertex
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append] at *
    omega

theorem filtered_plan_lower [DecidableEq V] (replies : table.AllReplies) (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ input.kept vertex, self.choose history vertex = input.indexed.move edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply table.terminal_lower replies self opponent ?_ root payoff result
  intro history vertex own
  obtain ⟨edge, member, same⟩ := selected history vertex own
  rw [same]
  exact ((input.kept_iff vertex edge).mp member).2

theorem filtered_plan_exact [DecidableEq V] {E' : Type w} {other : G.opposite.ValueRankTable}
    (right : Input other E') (sameValue : ∀ vertex, other.value vertex = -table.value vertex)
    (replies : table.AllReplies) (otherReplies : other.AllReplies) (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ input.kept vertex, self.choose history vertex = input.indexed.move edge)
    (rightSelected : ∀ history vertex, G.opposite.owner vertex = G.opposite.player →
      ∃ edge ∈ right.kept vertex, opponent.opposite.choose history vertex = right.indexed.move edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : payoff = table.value root := by
  have lower := input.filtered_plan_lower replies self opponent selected root payoff result
  have reflected := ThresholdGame.TerminalResult.opposite G result
  rw [G.opposite_combine] at reflected
  have upper := right.filtered_plan_lower otherReplies opponent.opposite self.opposite rightSelected root (-payoff) reflected
  rw [sameValue root] at upper
  omega

end Input

/-- 閾値証拠族から得る保証手が、実際の有限出力行にも残っていること。 -/
theorem family_nonempty (family : G.StratumFamily) (input : Input family.table E)
    (vertex : V) (own : G.owner vertex = G.player) :
    ∃ edge ∈ input.kept vertex, input.indexed.move edge = family.referenceMove vertex :=
  input.nonempty_of_safe vertex (family.referenceMove vertex) (family.referenceMove_safe vertex own)

end PetaProof.ValueStratumFilter
