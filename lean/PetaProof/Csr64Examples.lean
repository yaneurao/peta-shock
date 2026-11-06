import PetaProof.MoveRowsCsr64
import PetaProof.Csr32Examples

/-! 有限な配列での回帰例と、巨大配列を確保しない64-bit演算の境界例。 -/
namespace PetaProof.Csr64Examples

open MoveRows32Examples (book book_valid move_counts_fit selective empty)
open Csr32Examples (poison)
open MoveRowsCsr64

theorem capacity_fits : CapacityFits book :=
  capacityFits_of_bounds (by unfold TurnEncoding32.Fits; decide) book move_counts_fit
theorem count_intermediate : Csr64.countStep (fun value : Nat => value) 1 #[0, 0, 0] = #[0, 0, 1] := by decide
theorem prefix_intermediate : Csr64.prefixRun 2 1 #[0, 2, 1, 3] = #[0, 2, 3, 3] := by decide
theorem actual_positions : (build book poison).positions = #[0, 0, 1, 3] := by decide
theorem terminal_cursors : (build book poison).state.cursor = #[0, 1, 3, 3] := by decide
theorem payload_unchanged : (build book poison).state.memory = #[(2, 0), (1, 0), (1, 2)] := by decide
theorem actual_row : incoming book poison 2 = [(1, 0), (1, 2)] := by decide
theorem actual_callback : callbacks book poison (2, true) = [(2, 0), (2, 2)] := by decide
theorem parent_allow : parents book poison selective (2, true) = [(1, false)] := by decide

theorem full_build_refines : Csr64.unpackBuilt (build book poison) = MoveRowsCsr32.build book poison :=
  build_refines (by unfold TurnEncoding32.Fits; decide) book move_counts_fit capacity_fits poison

theorem all_phases_safe : Csr64.Safe 3 poison (MoveRowsCsr32.target book) (MoveRowsCsr32.edges book) :=
  Csr64.build_safe 3 poison _ _ (MoveRowsCsr32.bounded (by unfold TurnEncoding32.Fits; decide) book move_counts_fit) capacity_fits

set_option maxRecDepth 4096 in
theorem computed_core : (core book poison selective).map (fun state => (TurnEncoding32.encode state).toNat) =
    [2, 3, 4, 5] := by decide

theorem core_meaning (state : TurnEncoding.State 3) :
    state ∈ core book poison selective ↔ CyclicVertex (MoveRows32.relation book selective) state :=
  core_correct (by unfold TurnEncoding32.Fits; decide) book book_valid move_counts_fit capacity_fits poison selective state

-- 最大値の一つ手前から最大値までは正確。さらに+1すると折り返す。
theorem largest_exact_increment : (18446744073709551614 + 1 : UInt64).toNat = 18446744073709551615 := by decide
theorem unguarded_increment_wrap : (18446744073709551615 + 1 : UInt64).toNat = 0 := by decide
theorem unguarded_prefix_wrap : Csr64.prefixStep 1 #[18446744073709551615, 1] = #[18446744073709551615, 0] := by decide
theorem ordered_subtraction : (3 - 1 : UInt64).toNat = 2 := by decide
theorem unguarded_subtraction_wrap : (1 - 3 : UInt64).toNat = 18446744073709551614 := by decide

theorem empty_positions : (build empty poison).positions = #[0] := by decide
theorem empty_memory : (build empty poison).state.memory = #[] := by decide
theorem empty_core : core empty poison (fun _ _ => true) = [] := by decide

end PetaProof.Csr64Examples
