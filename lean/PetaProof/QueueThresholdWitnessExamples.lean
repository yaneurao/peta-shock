import PetaProof.QueueCounterWitness
import PetaProof.QueueThresholdScanExamples
import PetaProof.FinitePayoffExamples

/-! 実phaseの未確定集合全体、低いleafの応手、0・負の下限へ移す共通順位を検査する。 -/
namespace PetaProof.QueueThresholdWitnessExamples

open ThresholdGame

namespace Leaves

open QueueThresholdScanExamples

/-- 閾値30で未確定の同じ一局面について、応手20を抽出する。 -/
theorem response_twenty :
    ∃ regions : (game.retune 30 (by decide) (by decide)).ResolvedRegions after30.won 3,
      regions.negative.region.response () = .leaf 20 ∧ regions.negative.region.rank () ≤ 3 := by
  obtain ⟨regions⟩ := top.phase_regions initial top.seeded_certificate top.seeded_boundary
    no_own_cycles 30 (by decide) (by decide)
  have outside : ¬ after30.won () := by change ¬ (after30.counters ()).admitted = true; decide
  have turn : (game.retune 30 (by decide) (by decide)).owner () ≠
      (game.retune 30 (by decide) (by decide)).player := by decide
  have legal := regions.negative.region.chosen_legal () outside turn
  have closed := regions.negative.region.closed () outside (regions.negative.region.response ())
    ⟨legal, fun _ => rfl⟩
  refine ⟨regions, ?_, regions.negative.rank_bound () outside⟩
  rcases legal with high | low
  · rw [high] at closed
    change (30 : Int) < 30 at closed
    omega
  · exact low

/-- 同じカウンターを引き継いだ次の閾値20では正側へ移り、負側の領域は空。 -/
theorem next_phase_positive :
    ∃ regions : (game.retune 20 (by decide) (by decide)).ResolvedRegions after20.won 3,
      after20.won () ∧ (game.retune 20 (by decide) (by decide)).FourfoldWinning () ∧
        regions.positive.rank () ≤ regions.positive.stage := by
  obtain ⟨before⟩ := top.phase_certified initial top.seeded_certificate 30 (by decide) (by decide)
  have boundary := top.phase_boundary initial top.seeded_boundary 30 (by decide) (by decide)
  obtain ⟨regions⟩ := at30.phase_regions after30 before boundary no_own_cycles 20 (by decide) (by decide)
  have inside : after20.won () := by change (after20.counters ()).admitted = true; decide
  exact ⟨regions, inside, regions.positive.fourfold_winning () inside, regions.positive.rank_bound () inside⟩

end Leaves

namespace Quiet

def game : ThresholdGame Bool := {
  FinitePayoffExamples.drawGame with
  threshold := 4
  mate := 4
  positive := by decide
  bounded := by decide
}

def indexed : game.IndexedMoves Bool where
  outgoing := fun vertex => [vertex]
  source := id
  move := fun vertex => .node (!vertex)
  unique := fun _ => by simp
  at_source := fun _ => by simp
  source_of_mem := by intro vertex edge member; simpa using member
  legal := by
    intro vertex edge member
    have same : edge = vertex := by simpa using member
    subst edge
    rfl
  covers := fun vertex move law => ⟨vertex, by simp, law.symm⟩

def context : game.QueueContext Bool where
  vertices := [false, true]
  unique := by decide
  covered := by intro vertex; cases vertex <;> decide
  indexed := indexed
  parents := {
    incoming := fun child => [!child]
    unique := fun _ => by simp
    exact := by intro child edge; cases child <;> cases edge <;> simp [indexed]
  }
  core := fun _ => true
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [game, FinitePayoffExamples.drawGame]

theorem bounded_leaves : game.BoundedLeaves := by intro vertex score impossible; cases impossible
theorem own_core : ∀ vertex, CyclicVertex game.OpponentChecking vertex → context.core vertex = true := by
  intro _ _; rfl
theorem other_core : ∀ vertex, CyclicVertex game.opposite.OpponentChecking vertex → true = true := by
  intro _ _; rfl

theorem computed_zero (vertex : Bool) : context.generatedValue (fun _ => true) vertex = 0 := by
  cases vertex <;> decide

theorem sign_from_both_runs (vertex : Bool) :
    (context.opposite (fun _ => true)).generatedValue context.core vertex =
      -context.generatedValue (fun _ => true) vertex :=
  context.generated_opposite_sign (fun _ => true) bounded_leaves own_core other_core vertex

/-- 2頂点全体を一つのrankで覆う。通常循環では非王手での順位回復を許す。 -/
theorem zero_common_rank :
    ∃ region : (game.counterThreshold 0 (by decide) (by decide)).RefutationRegion (fun _ => True),
      (∀ vertex, region.rank vertex ≤ 4) ∧ region.rank false < region.rank true := by
  let other := context.opposite (fun _ => true)
  obtain ⟨original, bound⟩ := context.phase_counter_region (fun _ => true) bounded_leaves own_core other_core
    other.seeded other.seeded_certificate other.seeded_boundary 0 (by decide) (by decide) (by decide)
  have same (vertex : Bool) : 0 ≤ context.generatedValue (fun _ => true) vertex ↔ True := by
    rw [computed_zero]; simp
  let region := original.reindex same
  have legal : (game.counterThreshold 0 (by decide) (by decide)).legal true (.node false) := rfl
  have reply : (game.counterThreshold 0 (by decide) (by decide)).Replies region.response true (.node false) := by
    exact ⟨legal, fun impossible => False.elim (impossible rfl)⟩
  have decrease := region.strict_checking true false trivial reply (fun impossible => False.elim (impossible rfl))
  exact ⟨region, (fun vertex => bound vertex (by rw [computed_zero]; omega)), decrease⟩

theorem negative_common_rank :
    ∃ region : (game.counterThreshold (-1) (by decide) (by decide)).RefutationRegion (fun _ => True),
      ∀ vertex, region.rank vertex ≤ 4 := by
  let other := context.opposite (fun _ => true)
  obtain ⟨original, bound⟩ := context.phase_counter_region (fun _ => true) bounded_leaves own_core other_core
    other.seeded other.seeded_certificate other.seeded_boundary (-1) (by decide) (by decide) (by decide)
  have same (vertex : Bool) : -1 ≤ context.generatedValue (fun _ => true) vertex ↔ True := by
    rw [computed_zero]; simp
  exact ⟨original.reindex same, fun vertex => bound vertex (by rw [computed_zero]; omega)⟩

end Quiet
end PetaProof.QueueThresholdWitnessExamples
