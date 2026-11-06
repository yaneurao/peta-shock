import PetaProof.FrameCursorStep32

/-!
UInt32対のフレーム配列を型付きフレーム配列へ対応させる。
全フレームのValidにより復号成功と長さ一致を保証し、filterMapで不正要素を捨てて合わせない。
-/
namespace PetaProof.RawFrameStack32

open FrameCursor32 (Frame Rows)
variable {n : Nat}

def Valid (rows : Rows n) (array : Array Frame) : Prop :=
  ∀ frame ∈ array.toList, FrameCursor32.Valid rows frame
def model (rows : Rows n) (array : Array Frame) : Array (ForwardDfs.Frame (Fin n)) :=
  array.filterMap (FrameCursor32.decode rows)

theorem valid_empty (rows : Rows n) : Valid rows #[] := by simp [Valid]
theorem model_empty (rows : Rows n) : model rows #[] = #[] := rfl

theorem valid_push (rows : Rows n) (array : Array Frame) (valid : Valid rows array)
    (frame : Frame) (fresh : FrameCursor32.Valid rows frame) : Valid rows (array.push frame) := by
  intro other member
  simp only [Array.push_toList, List.mem_append, List.mem_singleton] at member
  rcases member with old | same
  · exact valid other old
  · simpa only [same] using fresh

theorem valid_of_push (rows : Rows n) (array : Array Frame) (frame : Frame)
    (valid : Valid rows (array.push frame)) : Valid rows array := by
  intro other member
  exact valid other (by simpa only [Array.push_toList] using List.mem_append_left [frame] member)

theorem top_valid (rows : Rows n) (array : Array Frame) (valid : Valid rows array)
    (frame : Frame) (top : array.back? = some frame) : FrameCursor32.Valid rows frame := by
  obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
  subst array
  exact valid frame (by simp)

theorem valid_pop (rows : Rows n) (array : Array Frame) (valid : Valid rows array) : Valid rows array.pop := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    exact valid_empty rows
  | some frame =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simpa only [Array.pop_push] using valid_of_push rows rest frame valid

theorem valid_replace (rows : Rows n) (array : Array Frame) (valid : Valid rows array)
    (frame : Frame) (fresh : FrameCursor32.Valid rows frame) : Valid rows (ArrayLifo.replaceBack array frame) := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    exact valid_empty rows
  | some old =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    rw [ArrayLifo.replace_push]
    exact valid_push rows rest (valid_of_push rows rest old valid) frame fresh

theorem model_push (rows : Rows n) (array : Array Frame) (frame : Frame) (valid : FrameCursor32.Valid rows frame) :
    model rows (array.push frame) = (model rows array).push (FrameCursor32.view rows frame valid) := by
  exact Array.filterMap_push_some (FrameCursor32.decode_success rows frame valid) (by simp)

theorem model_back (rows : Rows n) (array : Array Frame) (valid : Valid rows array) :
    (model rows array).back? = array.back?.bind (FrameCursor32.decode rows) := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some frame =>
    have frame_valid := top_valid rows array valid frame top
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simp only [model_push rows rest frame frame_valid, Array.back?_push]
    change some (FrameCursor32.view rows frame frame_valid) = FrameCursor32.decode rows frame
    exact (FrameCursor32.decode_success rows frame frame_valid).symm

theorem model_pop (rows : Rows n) (array : Array Frame) (valid : Valid rows array) :
    model rows array.pop = (model rows array).pop := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some frame =>
    have frame_valid := top_valid rows array valid frame top
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simp only [Array.pop_push, model_push rows rest frame frame_valid]

theorem model_replace (rows : Rows n) (array : Array Frame) (old frame : Frame)
    (top : array.back? = some old) (old_valid : FrameCursor32.Valid rows old) (fresh : FrameCursor32.Valid rows frame) :
    model rows (ArrayLifo.replaceBack array frame) =
      ArrayLifo.replaceBack (model rows array) (FrameCursor32.view rows frame fresh) := by
  obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
  subst array
  simp only [ArrayLifo.replace_push, model_push rows rest old old_valid, model_push rows rest frame fresh]

theorem decoded_all (rows : Rows n) (array : Array Frame) (valid : Valid rows array) :
    array.toList.map (FrameCursor32.decode rows) = (model rows array).toList.map some := by
  unfold model
  rw [Array.toList_filterMap]
  generalize words : array.toList = input
  have bounded : ∀ frame ∈ input, FrameCursor32.Valid rows frame := by
    intro frame member
    rw [← words] at member
    exact valid frame member
  clear words valid array
  induction input with
  | nil => rfl
  | cons frame rest ih =>
    have fresh := bounded frame (by simp)
    have tail := ih (fun frame member => bounded frame (by simp [member]))
    simp only [List.map_cons, List.filterMap_cons, FrameCursor32.decode_success rows frame fresh, tail]

theorem model_size (rows : Rows n) (array : Array Frame) (valid : Valid rows array) :
    (model rows array).size = array.size := by
  have all := decoded_all rows array valid
  have length := congrArg List.length all
  simpa only [List.length_map, Array.length_toList] using length.symm

end PetaProof.RawFrameStack32
