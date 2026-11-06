import PetaProof.SharedRankCapture
import PetaProof.GeneratedFamilyExamples

/-! 同一代表の証拠共有、正負の取得先、視点タグ、要求表、順位保存の接続を検査する。 -/
namespace PetaProof.SharedWitnessExamples

open ThresholdGame

namespace Gap
open QueueThresholdScanExamples

noncomputable def source : SharedPhaseWitness top (fun _ => 20) :=
  SharedPhaseWitness.fromRecords rfl
    (fun _ => ⟨(game.lower_retune_iff 40 (by decide) (by decide) () 20).mpr exact_twenty.1,
      (game.upper_retune_iff 40 (by decide) (by decide) () 20).mpr exact_twenty.2⟩) no_own_cycles

theorem same_representative : top.witnessLevel 21 = top.witnessLevel 29 := by decide

theorem same_positive_rank : (source.atQuery 21 (by decide) (by decide)).positive.rank () =
    (source.atQuery 29 (by decide) (by decide)).positive.rank () :=
  source.same_positive_rank 21 29 (by decide) (by decide) (by decide) (by decide) same_representative ()

theorem same_negative_rank : (source.atQuery 21 (by decide) (by decide)).negative.region.rank () =
    (source.atQuery 29 (by decide) (by decide)).negative.region.rank () :=
  source.same_negative_rank 21 29 (by decide) (by decide) (by decide) (by decide) same_representative ()

end Gap

namespace TwoLeaves

def score (vertex : Fin 2) : Int := if vertex.val = 0 then 20 else -20

def game : ThresholdGame (Fin 2) where
  legal := fun vertex move => move = .leaf (score vertex)
  owner := fun vertex => vertex.val == 1
  check := fun _ _ => False
  player := false
  threshold := 40
  mate := 40
  positive := by decide
  bounded := by decide
  alternating := by intro _ _ edge; contradiction
  nonempty_moves := fun _ => ⟨_, rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def indexed : game.IndexedMoves (Fin 2) where
  outgoing := fun vertex => [vertex]
  source := id
  move := fun vertex => .leaf (score vertex)
  unique := fun _ => by simp
  at_source := fun _ => by simp
  source_of_mem := by intro vertex edge present; simpa using present
  legal := by
    intro vertex edge present
    have same : edge = vertex := by simpa using present
    subst edge
    rfl
  covers := fun vertex move legal => ⟨vertex, by simp, legal.symm⟩

def context : game.QueueContext (Fin 2) where
  vertices := [0, 1]
  unique := by decide
  covered := by
    intro vertex
    have bound := vertex.isLt
    have alternatives : vertex.val = 0 ∨ vertex.val = 1 := by omega
    rcases alternatives with zero | one
    · have same : vertex = 0 := Fin.ext zero
      simp [same]
    · have same : vertex = 1 := Fin.ext one
      simp [same]
  indexed := indexed
  parents := {
    incoming := fun _ => []
    unique := fun _ => by simp
    exact := by intro _ _; simp [indexed]
  }
  core := fun _ => false
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [game]

theorem leaves : game.BoundedLeaves := by
  intro vertex actual legal
  have same : actual = score vertex := Move.leaf.inj legal
  subst actual
  unfold score
  split <;> decide

theorem own_core : ∀ vertex, CyclicVertex game.OpponentChecking vertex → context.core vertex = true := by
  intro _ ⟨_, edge, _⟩
  cases edge.1

theorem other_core : ∀ vertex, CyclicVertex game.opposite.OpponentChecking vertex → false = true := by
  intro _ ⟨_, edge, _⟩
  cases edge.1

theorem terminal_value (plan : game.MovePlan) (root : Fin 2) (payoff : Int)
    (result : game.TerminalResult plan root payoff) : payoff = score root := by
  cases result with
  | leaf trace _ _ _ legal _ =>
    cases trace with
    | nil => exact Move.leaf.inj legal
    | cons edge _ => cases edge
  | repetition _ _ _ _ edge _ _ _ _ _ => cases edge

theorem exactValue (vertex : Fin 2) : game.ExactValue vertex (score vertex) := by
  let plan : game.MovePlan := ⟨fun _ v => .leaf (score v), fun _ _ => rfl⟩
  refine ⟨⟨plan, ?_⟩, ⟨plan, ?_⟩⟩
  · intro opponent payoff result
    have same := terminal_value _ vertex payoff result
    omega
  · intro self payoff result
    have same := terminal_value _ vertex payoff result
    omega

theorem value_computed (vertex : Fin 2) : context.generatedValue (fun _ => false) vertex = score vertex :=
  ExactValue.unique game context.vertices context.covered vertex
    (context.generatedValue_exact (fun _ => false) leaves own_core other_core vertex) (exactValue vertex)

noncomputable def shared : SharedRankFamily context (fun _ => false) where
  value := score
  bounded := by intro vertex; unfold score; split <;> decide
  leaves := leaves
  own := SharedPhaseWitness.fromRecords rfl exactValue own_core
  opponent := SharedPhaseWitness.fromRecords rfl (fun vertex => by
    have result := context.other_generated_exact (fun _ => false) leaves own_core other_core vertex
    rw [context.generated_opposite_sign (fun _ => false) leaves own_core other_core vertex, value_computed] at result
    exact result) other_core

theorem positive_target : shared.target 0 = some (false, 20) := by
  have representative : context.witnessLevel 20 = 20 := by decide
  simp only [SharedRankFamily.target, show shared.value 0 = 20 from rfl, if_pos (show 0 < (20 : Int) by decide), representative]

theorem negative_target : shared.target 1 = some (true, 40) := by
  have representative : (context.opposite (fun _ => false)).witnessLevel 21 = 40 := by decide
  simp only [SharedRankFamily.target, show shared.value 1 = -20 from rfl,
    if_neg (show ¬ 0 < (-20 : Int) by decide), if_pos (show -game.mate < (-20 : Int) by decide)]
  change some (true, (context.opposite (fun _ => false)).witnessLevel 21) = _
  rw [representative]

noncomputable def requests := shared.buildRequests

def indices : SharedRankFamily.WitnessIndices context (fun _ => false) :=
  SharedRankFamily.buildWitnessIndices

theorem indexed_positive_target : shared.indexedTarget indices 0 = some (false, 20) := by
  rw [shared.indexedTarget_eq]
  exact positive_target

theorem indexed_negative_target : shared.indexedTarget indices 1 = some (true, 40) := by
  rw [shared.indexedTarget_eq]
  exact negative_target

theorem actual_positive_index : indices.own[20]? = some 20 := by
  have found := indices.own_correct 20 (by decide) (by decide)
  have representative : context.witnessLevel 20 = 20 := by decide
  simpa only [representative] using found

theorem actual_opponent_index : indices.opponent[21]? = some 40 := by
  have found := indices.opponent_correct 21 (by decide) (by decide)
  have representative : (context.opposite (fun _ => false)).witnessLevel 21 = 40 := by decide
  simpa only [representative] using found

theorem indexed_whole_requests : requests.buckets =
    RankRequestBuckets.build shared.route (List.finRange 2) := shared.buildRequests_buckets_eq

theorem own_row : (0 : Fin 2) ∈ requests.get (false, 20) := (requests.get_iff _ _).mpr positive_target
theorem opponent_row : (1 : Fin 2) ∈ requests.get (true, 40) := (requests.get_iff _ _).mpr negative_target
theorem side_not_interchangeable : (0 : Fin 2) ∉ requests.get (true, 20) := by
  intro present
  have found := (requests.get_iff _ _).mp present
  rw [positive_target] at found
  cases found

theorem bucket_headers : requests.buckets.size = 82 := requests.size
theorem slot_count : (shared.captured requests).size = 2 := shared.captured_size requests
theorem reads_at_most_two : SelectiveRankCapture.reads shared.keys requests.get ≤ 2 := shared.captured_reads_bound requests

theorem saved_rank_exact (vertex : Fin 2) : SelectiveRankCapture.storedRank (shared.captured requests) vertex =
    shared.table.rank (shared.table.value vertex) vertex := shared.captured_correct requests vertex

noncomputable def generated : SharedRankFamily context (fun _ => false) :=
  SharedRankFamily.fromGenerated rfl leaves own_core other_core

theorem from_input_lower (self opponent : game.MovePlan)
    (selected : (SelectiveRankCapture.cachedTable generated.table (generated.captured generated.buildRequests)).AdmissiblePlan self)
    (payoff : Int) (result : game.TerminalResult (game.combinePlans self opponent) 0 payoff) : 20 ≤ payoff := by
  have lower := SharedRankFamily.generated_capture_lower (ctx := context) (otherCore := fun _ => false)
    rfl leaves own_core other_core self opponent selected 0 payoff result
  rw [value_computed] at lower
  exact lower

end TwoLeaves
end PetaProof.SharedWitnessExamples
