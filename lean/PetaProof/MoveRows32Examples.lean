import PetaProof.MoveRows32

/-! 抽象グラフと32-bit境界値の回帰例。巨大な配列を確保する例ではない。 -/
namespace PetaProof.MoveRows32Examples

open MoveRows32

theorem largest_accepted_count : TurnEncoding32.Fits 2147483646 := by unfold TurnEncoding32.Fits; decide
theorem first_rejected_count : ¬TurnEncoding32.Fits 2147483647 := by unfold TurnEncoding32.Fits; decide
theorem boundary_no_wrap : TurnEncoding32.flipIndex 2147483645 0 = 4294967291 := by decide
theorem boundary_no_sentinel : TurnEncoding32.flipIndex 2147483645 0 ≠ TurnEncoding32.none := by decide

-- 局面数制限を外すと、内部辺がNoneに化けることがある。
theorem unguarded_collision : TurnEncoding32.flipIndex 2147483647 0 = TurnEncoding32.none := by decide
theorem unguarded_count_wrap : (UInt32.ofNat 4294967296).toNat = 0 := by decide
theorem leaf_is_sentinel : child32 .leaf 17 = TurnEncoding32.none := rfl
theorem invalid_internal_is_not_valid : ¬MoveValid 3 (.internal 3) := by decide
theorem valid_internal_is_not_leaf : child32 (.internal 2) 2 = 5 := by decide
theorem flip_even : TurnEncoding32.flipIndex 2 2 = 5 := by decide
theorem flip_odd : TurnEncoding32.flipIndex 2 3 = 4 := by decide

def book : Book 3 := fun vertex =>
  if vertex.val = 0 then #[]
  else if vertex.val = 1 then #[.internal 2, .leaf, .internal 2]
  else #[.internal 1]

theorem book_valid : Valid book := by unfold Valid; decide
theorem move_counts_fit : CountsFit book := by unfold CountsFit; decide
theorem converted_row : rows book 1 = #[some 2, none, some 2] := by decide
theorem original_move_numbers : MoveRowsCsr.rawIncoming (rows book) (0, 0) 2 = [(1, 0), (1, 2)] := by decide

def selective (parent move : UInt32) : Bool := !(parent == 2 && move == 0)

theorem callbacks_keep_move_numbers : callbacks32 book (0, 0) (2, true) = [(2, 0), (2, 2)] := by decide
theorem parent_turn_before_allow : parents32 book (0, 0) selective (2, true) = [2] := by decide
theorem parallel_parents_preserved : parents32 book (0, 0) selective (2, false) = [3, 3] := by decide

theorem machine_transpose (parent target : TurnEncoding.State 3) :
    TurnEncoding32.encode parent ∈ parents32 book (0, 0) selective target ↔ relation book selective parent target :=
  parents32_transpose (by unfold TurnEncoding32.Fits; decide) book book_valid (0, 0) selective parent target

set_option maxRecDepth 4096 in
theorem computed_core : (core book (0, 0) selective).map (fun state => (TurnEncoding32.encode state).toNat) =
    [2, 3, 4, 5] := by decide

theorem machine_core_meaning (state : TurnEncoding.State 3) :
    state ∈ core book (0, 0) selective ↔ CyclicVertex (relation book selective) state :=
  core_correct (by unfold TurnEncoding32.Fits; decide) book book_valid (0, 0) selective state

def empty : Book 0 := fun vertex => Fin.elim0 vertex
theorem empty_valid : Valid empty := by intro vertex; exact Fin.elim0 vertex
theorem empty_core : core empty (0, 0) (fun _ _ => true) = [] := by decide

end PetaProof.MoveRows32Examples
