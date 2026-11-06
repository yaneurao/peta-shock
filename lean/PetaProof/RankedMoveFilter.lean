import PetaProof.RankedMoveEnvelope
import PetaProof.CountedRowOps

/-! 同じ順位・領域フラグ・王手フラグから候補を有限一回走査で残す。正の閾値保証が対象。 -/
namespace PetaProof.RankedMoveFilter

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V} {won : V → Prop}

structure Input (region : G.RankedRegion won) (E : Type v) where
  indexed : G.IndexedMoves E
  member : V → Bool
  member_correct : ∀ vertex, member vertex = true ↔ won vertex
  checked : V → V → Bool
  checked_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace Input

variable {region : G.RankedRegion won} (input : Input region E)

def conditionFlag (vertex : V) : Move V → Bool
  | .leaf score => decide (G.threshold ≤ score)
  | .node child => input.member child && decide (region.rank child ≤ region.rank vertex) &&
      (decide (G.owner vertex = G.player) || input.checked vertex child ||
        decide (region.rank child < region.rank vertex))

theorem conditionFlag_spec (vertex : V) (move : Move V) :
    input.conditionFlag vertex move = true ↔ region.candidateCondition vertex move := by
  classical
  cases move with
  | leaf score => simp [conditionFlag, ThresholdGame.RankedRegion.candidateCondition]
  | node child =>
    by_cases own : G.owner vertex = G.player <;> by_cases check : G.check vertex child <;>
      simp [conditionFlag, ThresholdGame.RankedRegion.candidateCondition,
        input.member_correct, input.checked_correct, own, check, and_assoc]

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

theorem reference_survives (vertex : V) (inside : won vertex) (own : G.owner vertex = G.player) :
    ∃ edge ∈ input.kept vertex, input.indexed.move edge = region.choice vertex := by
  obtain ⟨edge, member, same⟩ := input.indexed.covers vertex _ (region.chosen_legal vertex inside own)
  refine ⟨edge, (input.kept_iff vertex edge).mpr ⟨member, ?_⟩, same⟩
  rw [same]
  exact region.reference_candidate vertex inside own

theorem opponents_all_survive (vertex : V) (inside : won vertex) (other : G.owner vertex ≠ G.player)
    (edge : E) (member : edge ∈ input.indexed.outgoing vertex) : edge ∈ input.kept vertex :=
  (input.kept_iff vertex edge).mpr ⟨member,
    region.opponent_candidate vertex inside other _ (input.indexed.legal vertex edge member)⟩

/-- 出力を安定なfilterに保ち、判定一回と採用時の格納一回を数える。 -/
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

theorem filtered_plan_guarantee [DecidableEq V] (self opponent : G.MovePlan)
    (selected : ∀ history vertex, won vertex → G.owner vertex = G.player →
      ∃ edge ∈ input.kept vertex, self.choose history vertex = input.indexed.move edge)
    (root : V) (inside : won root) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : G.threshold ≤ payoff := by
  apply region.admissible_plan_guarantee self opponent ?_ root inside payoff result
  intro history vertex parent own
  obtain ⟨edge, member, same⟩ := selected history vertex parent own
  rw [same]
  exact input.kept_sound vertex edge member

end Input
end PetaProof.RankedMoveFilter
