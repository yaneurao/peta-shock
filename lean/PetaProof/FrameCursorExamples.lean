import PetaProof.FrameCursorStep32

/-! UInt32カーソルの境界と、元出辺の位置を保つ局所遷移の回帰例。 -/
namespace PetaProof.FrameCursorExamples

open FrameCursor32

def rows (vertex : Fin 4) : Array (Option (Fin 4)) :=
  match vertex.val with
  | 0 => #[none, some 1, some 1, some 2]
  | 1 => #[some 3]
  | 2 => #[some 3]
  | _ => #[some 0]

theorem counts : CountsFit rows := by unfold CountsFit; decide

def initial_valid : Valid rows (0, 0) := ⟨by decide, by decide⟩
def second_valid : Valid rows (0, 1) := ⟨by decide, by decide⟩
def end_valid : Valid rows (0, 4) := ⟨by decide, by decide⟩

theorem start_raw_pair : start (0 : Fin 4) = (0, 0) := by decide
theorem start_todo : (view rows (0, 0) initial_valid).todo = [none, some 1, some 1, some 2] := by decide
theorem consumes_none_slot : step rows (0, 0) = .consume (0, 1) none := by decide
theorem first_duplicate_slot : step rows (0, 1) = .consume (0, 2) (some 1) := by decide
theorem second_duplicate_slot : step rows (0, 2) = .consume (0, 3) (some 1) := by decide
theorem last_slot : step rows (0, 3) = .consume (0, 4) (some 2) := by decide
theorem terminal_no_read : step rows (0, 4) = .retire 0 := by decide
theorem new_cursor_has_tail : (view rows (0, 1) second_valid).todo = [some 1, some 1, some 2] := by decide
theorem terminal_todo_empty : (view rows (0, 4) end_valid).todo = [] := by decide
theorem original_cursor_read : target rows (0, 0) initial_valid = none ∧ target rows (0, 1) second_valid = some 1 := by decide
theorem cursor_reconstructs : (rows 0).size - (view rows (0, 1) second_valid).todo.length = 1 := by decide

theorem actual_local_correspondence : Corresponds rows (0, 0) initial_valid (step rows (0, 0)) :=
  step_correct rows counts (0, 0) initial_valid

def state : ForwardDfsFrameArray.State 4 :=
  ⟨#[1, 0, 0, 0], #[view rows (0, 0) initial_valid], #[]⟩

theorem none_slot_does_not_push :
    (ForwardDfsFrameArray.tick (fun vertex => (rows vertex).toList) state).stack.map ForwardDfs.Frame.vertex = #[0] := by decide
theorem none_slot_advances_todo :
    ((ForwardDfsFrameArray.tick (fun vertex => (rows vertex).toList) state).stack.back?).map ForwardDfs.Frame.todo =
      some [some 1, some 1, some 2] := by decide
theorem two_ticks_push_child :
    (ForwardDfsFrameArray.walk (fun vertex => (rows vertex).toList) 2 state).stack.map ForwardDfs.Frame.vertex = #[0, 1] := by decide

theorem bad_vertex_rejected : decode rows (4, 0) = none ∧ step rows (4, 0) = .invalid := by
  constructor
  · rfl
  · decide
theorem overshoot_excluded : ¬ Valid rows (0, 5) := by
  intro valid
  have bound := valid.cursor
  change 5 ≤ 4 at bound
  omega
theorem empty_row_retires : step (fun _ : Fin 1 => #[]) (0, 0) = .retire 0 := by decide
theorem zero_vertices_invalid : step (fun vertex : Fin 0 => Fin.elim0 vertex) (0, 0) = .invalid := by decide

-- 巨大配列を確保せず、整数演算だけで境界を検査する。
theorem last_safe_increment : (4294967294 + 1 : UInt32).toNat = 4294967295 := by decide
theorem certified_last_increment : (4294967294 + 1 : UInt32).toNat = (4294967294 : UInt32).toNat + 1 :=
  increment_exact 4294967294 4294967295 (by decide) (by decide)
theorem unchecked_increment_wraps : (4294967295 + 1 : UInt32).toNat = 0 := by decide
theorem unchecked_degree_cast_wraps : (UInt32.ofNat 4294967296).toNat = 0 := by decide

end PetaProof.FrameCursorExamples
