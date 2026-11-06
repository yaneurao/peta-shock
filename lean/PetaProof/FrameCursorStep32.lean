import PetaProof.FrameCursor32

/-!
生の(v,j)から終了・一枠消費を判定し、第51段階のtick/trim/retireへ接続する。
UInt32フレームを配列へ保存した全実行ではなく、非空の末尾フレーム一つの遷移である。
-/
namespace PetaProof.FrameCursor32

variable {n : Nat}

inductive Action (n : Nat) where
  | invalid
  | retire (vertex : UInt32)
  | consume (next : Frame) (target : Option (Fin n))
  deriving DecidableEq

def step (rows : Rows n) (frame : Frame) : Action n :=
  if vertex : frame.1.toNat < n then
    let source : Fin n := ⟨frame.1.toNat, vertex⟩
    if frame.2 = UInt32.ofNat (rows source).size then .retire frame.1
    else .consume (advance frame) ((rows source)[frame.2.toNat]?.getD none)
  else .invalid

theorem step_retire (rows : Rows n) (frame : Frame) (valid : Valid rows frame)
    (done : frame.2 = degree rows frame valid) : step rows frame = .retire frame.1 := by
  simp only [step, dif_pos valid.vertex]
  exact if_pos done

theorem step_consume (rows : Rows n) (frame : Frame) (valid : Valid rows frame)
    (running : frame.2 ≠ degree rows frame valid) :
    step rows frame = .consume (advance frame) (target rows frame valid) := by
  simp only [step, dif_pos valid.vertex]
  exact if_neg running

def Corresponds (rows : Rows n) (frame : Frame) (valid : Valid rows frame) : Action n → Prop
  | .invalid => False
  | .retire vertex => vertex = frame.1 ∧ (view rows frame valid).todo = []
  | .consume next picked => next.1 = frame.1 ∧ ∃ next_valid : Valid rows next,
      (view rows frame valid).todo = picked :: (view rows next next_valid).todo ∧
        (view rows next next_valid).vertex = (view rows frame valid).vertex

theorem step_correct (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame) :
    Corresponds rows frame valid (step rows frame) := by
  by_cases done : frame.2 = degree rows frame valid
  · rw [step_retire rows frame valid done]
    exact ⟨rfl, (end_iff_empty rows counts frame valid).mp done⟩
  · rw [step_consume rows frame valid done]
    exact ⟨rfl, advance_valid rows counts frame valid done, consume_exact rows counts frame valid done, rfl⟩

theorem step_not_invalid (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame) :
    step rows frame ≠ .invalid := by
  intro same
  have correct := step_correct rows counts frame valid
  rw [same] at correct
  exact correct

theorem retire_tick (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (state : ForwardDfsFrameArray.State n) (top : state.stack.back? = some (view rows frame valid))
    (done : frame.2 = degree rows frame valid) :
    ForwardDfsFrameArray.tick (fun vertex => (rows vertex).toList) state = ForwardDfsFrameArray.retire state := by
  simp only [ForwardDfsFrameArray.tick, top, (end_iff_empty rows counts frame valid).mp done]

theorem consume_tick (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (state : ForwardDfsFrameArray.State n) (top : state.stack.back? = some (view rows frame valid))
    (running : frame.2 ≠ degree rows frame valid) :
    ForwardDfsFrameArray.tick (fun vertex => (rows vertex).toList) state =
      match target rows frame valid with
      | none => ForwardDfsFrameArray.trim state
      | some child => ForwardDfsFrameArray.discover (fun vertex => (rows vertex).toList) (ForwardDfsFrameArray.trim state) child := by
  simp only [ForwardDfsFrameArray.tick, top, consume_exact rows counts frame valid running]
  cases picked : target rows frame valid <;> rfl

theorem advance_matches_trim (rows : Rows n) (counts : CountsFit rows) (frame : Frame) (valid : Valid rows frame)
    (state : ForwardDfsFrameArray.State n) (top : state.stack.back? = some (view rows frame valid))
    (running : frame.2 ≠ degree rows frame valid) :
    ArrayLifo.replaceBack state.stack (view rows (advance frame) (advance_valid rows counts frame valid running)) =
      (ForwardDfsFrameArray.trim state).stack := by
  rw [advance_is_tail rows counts frame valid running, ForwardDfsFrameArray.trim, top]

theorem retire_appends_raw (rows : Rows n) (frame : Frame) (valid : Valid rows frame)
    (state : ForwardDfsFrameArray.State n) (top : state.stack.back? = some (view rows frame valid)) :
    (ForwardDfsFrameArray.retire state).finished = state.finished.push frame.1 := by
  simp only [ForwardDfsFrameArray.retire, top, view_vertex_word]

end PetaProof.FrameCursor32
