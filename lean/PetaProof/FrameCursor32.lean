import PetaProof.FrameArrayScc

/-!
フレームをUInt32の(v,j)へ写す。jは次に読む元出辺枠で、次数と等しければ終了する。
rowsはleaf・不許可辺もnoneの枠として保持する。元出辺をフィルタしてjをずらさない。
-/
namespace PetaProof.FrameCursor32

variable {n : Nat}
abbrev Frame := UInt32 × UInt32
abbrev Rows (n : Nat) := IndexedMoveRows.Rows n

def CountsFit (rows : Rows n) : Prop := ∀ vertex, (rows vertex).size < UInt32.size

theorem counts_from_move_rows (book : MoveRows32.Book n) (counts : MoveRows32.CountsFit book) :
    CountsFit (MoveRows32.rows book) := by
  intro vertex
  simpa only [MoveRows32.row_size] using counts vertex

structure Valid (rows : Rows n) (frame : Frame) : Prop where
  vertex : frame.1.toNat < n
  cursor : frame.2.toNat ≤ (rows ⟨frame.1.toNat, vertex⟩).size

def view (rows : Rows n) (frame : Frame) (valid : Valid rows frame) : ForwardDfs.Frame (Fin n) :=
  ⟨⟨frame.1.toNat, valid.vertex⟩, (rows ⟨frame.1.toNat, valid.vertex⟩).toList.drop frame.2.toNat⟩

def decode (rows : Rows n) (frame : Frame) : Option (ForwardDfs.Frame (Fin n)) :=
  if vertex : frame.1.toNat < n then
    some ⟨⟨frame.1.toNat, vertex⟩, (rows ⟨frame.1.toNat, vertex⟩).toList.drop frame.2.toNat⟩
  else none

def start (vertex : Fin n) : Frame := (VertexStack32.encode vertex, 0)
def advance (frame : Frame) : Frame := (frame.1, frame.2 + 1)
def degree (rows : Rows n) (frame : Frame) (valid : Valid rows frame) : UInt32 :=
  UInt32.ofNat (rows (view rows frame valid).vertex).size
def target (rows : Rows n) (frame : Frame) (valid : Valid rows frame) : Option (Fin n) :=
  (rows (view rows frame valid).vertex)[frame.2.toNat]?.getD none

theorem decode_success (rows : Rows n) (frame : Frame) (valid : Valid rows frame) :
    decode rows frame = some (view rows frame valid) := by
  simp only [decode, dif_pos valid.vertex, view]

theorem view_vertex_word (rows : Rows n) (frame : Frame) (valid : Valid rows frame) :
    VertexStack32.encode (view rows frame valid).vertex = frame.1 := by
  simp only [view, VertexStack32.encode, UInt32.ofNat_toNat]

theorem start_valid (fits : n ≤ UInt32.size) (rows : Rows n) (vertex : Fin n) : Valid rows (start vertex) := by
  refine ⟨?_, ?_⟩
  · simpa only [start, VertexStack32.encode_toNat fits] using vertex.isLt
  · change 0 ≤ _
    omega

theorem start_view (fits : n ≤ UInt32.size) (rows : Rows n) (vertex : Fin n) :
    view rows (start vertex) (start_valid fits rows vertex) = ⟨vertex, (rows vertex).toList⟩ := by
  simp only [view, start, VertexStack32.encode_toNat fits, UInt32.toNat_zero, List.drop_zero]

theorem degree_exact (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame) :
    (degree rows frame valid).toNat = (rows (view rows frame valid).vertex).size :=
  UInt32.toNat_ofNat_of_lt' (counts _)

theorem end_iff (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame) :
    frame.2 = degree rows frame valid ↔ frame.2.toNat = (rows (view rows frame valid).vertex).size := by
  constructor
  · intro same
    rw [same, degree_exact rows counts frame valid]
  · intro same
    have encoded := congrArg UInt32.ofNat same
    simpa only [UInt32.ofNat_toNat, degree] using encoded

theorem end_iff_empty (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame) :
    frame.2 = degree rows frame valid ↔ (view rows frame valid).todo = [] := by
  rw [end_iff rows counts frame valid]
  simp only [view, List.drop_eq_nil_iff, Array.length_toList]
  have bound := valid.cursor
  omega

theorem before_end (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) : frame.2.toNat < (rows (view rows frame valid).vertex).size := by
  have different : frame.2.toNat ≠ (rows (view rows frame valid).vertex).size :=
    fun same => running ((end_iff rows counts frame valid).mpr same)
  have bound := valid.cursor
  change frame.2.toNat ≤ (rows (view rows frame valid).vertex).size at bound
  omega

/-- 次数未満の場合だけ増分するので、最後の有効なjの次もUInt32で正確に保持できる。 -/
theorem increment_exact (cursor : UInt32) (size : Nat) (fits : size < UInt32.size) (inside : cursor.toNat < size) :
    (cursor + 1).toNat = cursor.toNat + 1 := by
  have small : cursor.toNat + 1 < UInt32.size := by omega
  rw [UInt32.toNat_add]
  change (cursor.toNat + 1) % 4294967296 = cursor.toNat + 1
  exact Nat.mod_eq_of_lt small

theorem advance_exact (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) : (advance frame).2.toNat = frame.2.toNat + 1 :=
  increment_exact frame.2 _ (counts _) (before_end rows counts frame valid running)

theorem advance_valid (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) : Valid rows (advance frame) := by
  refine ⟨valid.vertex, ?_⟩
  rw [advance_exact rows counts frame valid running]
  have inside := before_end rows counts frame valid running
  change frame.2.toNat + 1 ≤ (rows (view rows frame valid).vertex).size
  omega

theorem target_checked (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    target rows frame valid = (rows (view rows frame valid).vertex)[frame.2.toNat]'(before_end rows counts frame valid running) := by
  simp [target, before_end rows counts frame valid running]

theorem target_read_success (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    (rows (view rows frame valid).vertex)[frame.2.toNat]? = some (target rows frame valid) := by
  rw [target_checked rows counts frame valid running]
  simp [before_end rows counts frame valid running]

theorem advance_view (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    view rows (advance frame) (advance_valid rows counts frame valid running) =
      { view rows frame valid with todo := (rows (view rows frame valid).vertex).toList.drop (frame.2.toNat + 1) } := by
  have exact_cursor := advance_exact rows counts frame valid running
  change (frame.2 + 1).toNat = frame.2.toNat + 1 at exact_cursor
  simp only [view, advance, exact_cursor]

/-- 旧jで読む枠と、新しいjが表す残り部分を一つの等式にする。noneの枠も消費する。 -/
theorem consume_exact (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    (view rows frame valid).todo = target rows frame valid ::
      (view rows (advance frame) (advance_valid rows counts frame valid running)).todo := by
  rw [advance_view rows counts frame valid running, target_checked rows counts frame valid running]
  exact List.drop_eq_getElem_cons (before_end rows counts frame valid running)

theorem advance_is_tail (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    view rows (advance frame) (advance_valid rows counts frame valid running) =
      { view rows frame valid with todo := (view rows frame valid).todo.tail } := by
  have consumed := consume_exact rows counts frame valid running
  have same_vertex : (view rows (advance frame) (advance_valid rows counts frame valid running)).vertex =
      (view rows frame valid).vertex := rfl
  cases before : view rows frame valid with
  | mk vertex todo =>
    cases after : view rows (advance frame) (advance_valid rows counts frame valid running) with
    | mk next rest =>
      simp only [before, after] at consumed same_vertex ⊢
      rw [consumed, same_vertex]
      rfl

theorem cursor_recovered (rows : Rows n) (frame : Frame) (valid : Valid rows frame) :
    (rows (view rows frame valid).vertex).size - (view rows frame valid).todo.length = frame.2.toNat := by
  simp only [view, List.length_drop, Array.length_toList]
  have bound := valid.cursor
  omega

end PetaProof.FrameCursor32
