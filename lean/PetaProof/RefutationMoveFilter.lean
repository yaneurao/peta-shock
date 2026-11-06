import PetaProof.RefutationMoveEnvelope
import PetaProof.CountedRowOps

/-! 反証側の順位を使う安定filter。非王手のリセットと0・負の下限に接続する。 -/
namespace PetaProof.RefutationMoveFilter

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V} {lost : V → Prop}

structure Input (region : G.RefutationRegion lost) (E : Type v) where
  indexed : G.IndexedMoves E
  member : V → Bool
  member_correct : ∀ vertex, member vertex = true ↔ lost vertex
  checked : V → V → Bool
  checked_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace Input

variable {region : G.RefutationRegion lost} (input : Input region E)

def conditionFlag (vertex : V) : Move V → Bool
  | .leaf score => decide (score < G.threshold)
  | .node child => input.member child &&
      ((decide (G.owner vertex ≠ G.player) && !input.checked vertex child) ||
        decide (region.rank child < region.rank vertex))

theorem conditionFlag_spec (vertex : V) (move : Move V) :
    input.conditionFlag vertex move = true ↔ region.candidateCondition vertex move := by
  classical
  cases move with
  | leaf score => simp [conditionFlag, ThresholdGame.RefutationRegion.candidateCondition]
  | node child =>
    have unchecked : input.checked vertex child = false ↔ ¬ G.check vertex child := by
      rw [← input.checked_correct vertex child]
      cases input.checked vertex child <;> decide
    by_cases own : G.owner vertex = G.player <;> by_cases check : G.check vertex child <;>
      simp [conditionFlag, ThresholdGame.RefutationRegion.candidateCondition,
        input.member_correct, input.checked_correct, unchecked, own, check]

def kept (vertex : V) : List E :=
  (input.indexed.outgoing vertex).filter (fun edge => input.conditionFlag vertex (input.indexed.move edge))

theorem kept_iff (vertex : V) (edge : E) : edge ∈ input.kept vertex ↔
    edge ∈ input.indexed.outgoing vertex ∧ region.admissibleMove vertex (input.indexed.move edge) := by
  simp only [kept, List.mem_filter, input.conditionFlag_spec]
  constructor
  · rintro ⟨member, condition⟩
    exact ⟨member, input.indexed.legal vertex edge member, condition⟩
  · rintro ⟨member, _, condition⟩
    exact ⟨member, condition⟩

theorem kept_sound (vertex : V) (edge : E) (member : edge ∈ input.kept vertex) :
    region.admissibleMove vertex (input.indexed.move edge) := (input.kept_iff vertex edge).mp member |>.2

theorem reference_survives (vertex : V) (inside : lost vertex) (other : G.owner vertex ≠ G.player) :
    ∃ edge ∈ input.kept vertex, input.indexed.move edge = region.response vertex := by
  obtain ⟨edge, member, same⟩ := input.indexed.covers vertex _ (region.chosen_legal vertex inside other)
  refine ⟨edge, (input.kept_iff vertex edge).mpr ⟨member, ?_⟩, same⟩
  rw [same]
  exact region.reference_candidate vertex inside other

theorem own_all_survive (vertex : V) (inside : lost vertex) (own : G.owner vertex = G.player)
    (edge : E) (member : edge ∈ input.indexed.outgoing vertex) : edge ∈ input.kept vertex :=
  (input.kept_iff vertex edge).mpr ⟨member,
    region.own_candidate vertex inside own _ (input.indexed.legal vertex edge member)⟩

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

theorem filtered_plan_upper [DecidableEq V] (self opponent : G.MovePlan)
    (selected : ∀ history vertex, lost vertex → G.owner vertex ≠ G.player →
      ∃ edge ∈ input.kept vertex, opponent.choose history vertex = input.indexed.move edge)
    (root : V) (inside : lost root) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : payoff < G.threshold := by
  apply region.admissible_plan_upper self opponent ?_ root inside payoff result
  intro history vertex parent other
  obtain ⟨edge, member, same⟩ := selected history vertex parent other
  rw [same]
  exact input.kept_sound vertex edge member

theorem filtered_plan_opposite_lower [DecidableEq V] (self opponent : G.opposite.MovePlan)
    (selected : ∀ history vertex, lost vertex → G.owner vertex ≠ G.player →
      ∃ edge ∈ input.kept vertex, (self.choose history vertex).negate = input.indexed.move edge)
    (root : V) (inside : lost root) (payoff : Int)
    (result : G.opposite.TerminalResult (G.opposite.combinePlans self opponent) root payoff) :
    1 - G.threshold ≤ payoff := by
  apply region.admissible_plan_opposite_lower self opponent ?_ root inside payoff result
  intro history vertex parent other
  obtain ⟨edge, member, same⟩ := selected history vertex parent other
  change region.admissibleMove vertex (self.choose history vertex).negate
  rw [same]
  exact input.kept_sound vertex edge member

end Input
end PetaProof.RefutationMoveFilter
