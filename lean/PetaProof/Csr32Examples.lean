import PetaProof.MoveRowsCsr32
import PetaProof.MoveRows32Examples

/-! UInt32対を直接格納する配列と、そこからのcallback・SCCの回帰例。 -/
namespace PetaProof.Csr32Examples

open MoveRowsCsr32
open MoveRows32Examples (book book_valid move_counts_fit selective empty empty_valid)

-- 0番局面に手はなく、(0,0)は辺IDとして不正。最大値のseedでも結果は同じ。
def poison : Pair := (TurnEncoding32.none, TurnEncoding32.none)

theorem actual_offsets : (build book poison).positions = #[0, 0, 1, 3] := by decide
theorem actual_cursor : (build book poison).state.cursor = #[0, 1, 3, 3] := by decide
theorem actual_payload : (build book poison).state.memory = #[(2, 0), (1, 0), (1, 2)] := by decide
theorem leaf_not_stored : (build book poison).state.memory.size = 3 := by decide
theorem full_build_refines : CsrMap.mapBuilt unpack (build book poison) =
    CsrConstructArray.build 3 (unpack poison) (MoveRowsCsr.target (MoveRows32.rows book))
      (MoveRowsCsr.rawEdges (MoveRows32.rows book)) :=
  build_refines (by unfold TurnEncoding32.Fits; decide) book move_counts_fit poison

theorem constructed_safe : CsrConstructArray.Safe 3 poison (target book) (edges book) :=
  construction_safe (by unfold TurnEncoding32.Fits; decide) book move_counts_fit poison

theorem direct_row : incoming book poison 2 = [(1, 0), (1, 2)] := by decide
theorem empty_row : incoming book poison 0 = [] := by decide
theorem seed_does_not_leak : incoming book (0, 0) 2 = incoming book poison 2 :=
  seed_independent (by unfold TurnEncoding32.Fits; decide) book move_counts_fit _ _ _

theorem direct_callback : callbacks book poison (2, true) = [(2, 0), (2, 2)] := by decide
theorem allow_uses_parent : parents32 book poison selective (2, true) = [2] := by decide
theorem parallel_parents : parents32 book poison selective (2, false) = [3, 3] := by decide
theorem decoded_parents : parents book poison selective (2, false) = [(1, true), (1, true)] := by decide

set_option maxRecDepth 4096 in
theorem computed_core : (core book poison selective).map (fun state => (TurnEncoding32.encode state).toNat) =
    [2, 3, 4, 5] := by decide

theorem core_meaning (state : TurnEncoding.State 3) :
    state ∈ core book poison selective ↔ CyclicVertex (MoveRows32.relation book selective) state :=
  core_correct (by unfold TurnEncoding32.Fits; decide) book book_valid move_counts_fit poison selective state

theorem empty_counts : MoveRows32.CountsFit empty := by intro vertex; exact Fin.elim0 vertex
theorem empty_safe : CsrConstructArray.Safe 0 poison (target empty) (edges empty) :=
  construction_safe (by unfold TurnEncoding32.Fits; decide) empty empty_counts poison
theorem empty_payload : (build empty poison).state.memory = #[] := by decide
theorem empty_offsets : (build empty poison).positions = #[0] := by decide
theorem empty_core : core empty poison (fun _ _ => true) = [] := by decide

end PetaProof.Csr32Examples
