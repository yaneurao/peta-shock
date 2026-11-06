import PetaProof.GeneratedOutputSafety
import PetaProof.QueueThresholdWitnessExamples

/-! 未処理の反証閾値、両符号の生成候補、出力計画への接続を検査する。 -/
namespace PetaProof.GeneratedFamilyExamples

open ThresholdGame

namespace Leaves
open QueueThresholdScanExamples

theorem only_three_phases : top.generatedLevels = [40, 30, 20] := by decide
theorem gap_representative : top.witnessLevel 21 = 30 := by decide
theorem below_first_leaf : top.witnessLevel 1 = 20 := by decide
theorem above_last_leaf : top.witnessLevel 31 = 40 := by decide
theorem exact_leaf_unchanged : top.witnessLevel 20 = 20 := by decide

theorem gap_same_cut : game.SameLeafCut 21 30 :=
  top.witnessLevel_cut 21 (by decide) (by decide)

/-- 21のphaseを新たに実行せず、[40,30,20]の記録から領域の証拠を得る。 -/
theorem omitted_threshold_certified :
    Nonempty (((game.retune 40 (by decide) (by decide)).retune 21 (by decide) (by decide)).ResolvedRegions
      (fun vertex => 21 ≤ top.generatedValue (fun _ => false) vertex) 3) :=
  top.generated_cut_regions rfl (fun _ => false) bounded_leaves no_own_cycles no_other_cycles 21 (by decide) (by decide)

def other := top.opposite (fun _ => false)

theorem negative_value : other.generatedValue top.core () = -20 := by
  have target : (game.retune 40 (by decide) (by decide)).ExactValue () 20 :=
    ⟨(game.lower_retune_iff 40 (by decide) (by decide) () 20).mpr exact_twenty.1,
      (game.upper_retune_iff 40 (by decide) (by decide) () 20).mpr exact_twenty.2⟩
  have positive : top.generatedValue (fun _ => false) () = 20 :=
    ExactValue.unique _ top.vertices top.covered ()
      (top.generatedValue_exact (fun _ => false) bounded_leaves no_own_cycles no_other_cycles ()) target
  have sign := top.generated_opposite_sign (fun _ => false) bounded_leaves no_own_cycles no_other_cycles ()
  simpa only [positive] using sign

/-- 元の値-20に必要な反証閾値21は、相手走査の30の証拠へ丸められる。 -/
theorem negative_safe_best :
    ∃ edge ∈ other.indexed.outgoing (),
      (other.generatedTable rfl top.core (game.opposite_bounded_leaves bounded_leaves)
        no_other_cycles (top.opposite_opposite_core no_own_cycles)).admissibleMove () (other.indexed.move edge) ∧
      moveValue (other.generatedValue top.core) (other.indexed.move edge) = -20 := by
  obtain ⟨edge, member, safe, exact⟩ := other.generated_safe_best rfl top.core
    (game.opposite_bounded_leaves bounded_leaves) no_other_cycles (top.opposite_opposite_core no_own_cycles)
    () rfl
  exact ⟨edge, member, safe, by simpa only [negative_value] using exact⟩

end Leaves

namespace Quiet
open QueueThresholdWitnessExamples.Quiet

theorem no_leaf_still_has_representative : context.witnessLevel 1 = 4 := by decide

theorem generated_nonempty :
    ∃ edge, edge ∈ (context.generatedInput rfl (fun _ => true) bounded_leaves own_core other_core).kept false :=
  context.generated_kept_nonempty rfl (fun _ => true) bounded_leaves own_core other_core false rfl

theorem one_rank_per_vertex (level : Int) (vertex : Bool) :
    (context.generatedTable rfl (fun _ => true) bounded_leaves own_core other_core).rank level vertex =
      (context.generatedTable rfl (fun _ => true) bounded_leaves own_core other_core).rank 0 vertex :=
  context.generatedTable_rank_independent rfl (fun _ => true) bounded_leaves own_core other_core level vertex

theorem exactly_two_stored_rows :
    (context.generatedStoredRows rfl (fun _ => true) bounded_leaves own_core other_core).length = 2 :=
  context.generatedStoredRows_length rfl (fun _ => true) bounded_leaves own_core other_core

theorem constructed_output_guarantees_zero (depth : Bool → Nat) (opponent : game.MovePlan) (payoff : Int)
    (result : game.TerminalResult
      (game.combinePlans (context.generatedOutputPlan rfl (fun _ => true) bounded_leaves own_core other_core depth)
        opponent) false payoff) : 0 ≤ payoff := by
  have lower := context.generatedOutputPlan_lower rfl (fun _ => true) bounded_leaves own_core other_core
    depth opponent false payoff result
  rw [computed_zero] at lower
  exact lower

end Quiet
end PetaProof.GeneratedFamilyExamples
