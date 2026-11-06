import PetaProof.RawFrameStack32

/-!
第一DFSのフレームをUInt32対の配列で実行する。未走査部分のリストは復号仕様だけに現れる。
rowsは元の全出辺枠を保持する型付き配列。機械式child/allowとの接続は別に必要。
-/
namespace PetaProof.ForwardDfsRaw32

open FrameCursor32 (Frame Rows)
variable {n : Nat}

structure State (n : Nat) where
  seen : Array UInt8
  stack : Array Frame
  finished : Array UInt32

def outgoing (rows : Rows n) (vertex : Fin n) : List (Option (Fin n)) := (rows vertex).toList
def unpack (rows : Rows n) (state : State n) : ForwardDfsFrameArray.State n :=
  ⟨state.seen, RawFrameStack32.model rows state.stack, state.finished⟩

structure Valid (rows : Rows n) (state : State n) : Prop where
  base : ForwardDfsFrameArray.Valid (unpack rows state)
  stack : RawFrameStack32.Valid rows state.stack

def initial (n : Nat) : State n := ⟨SeenArray8.empty n, #[], #[]⟩

theorem initial_refines (rows : Rows n) : unpack rows (initial n) = ForwardDfsFrameArray.initial n := rfl
theorem initial_valid (rows : Rows n) : Valid rows (initial n) :=
  ⟨ForwardDfsFrameArray.initial_valid n, RawFrameStack32.valid_empty rows⟩

def discover (_rows : Rows n) (state : State n) (vertex : Fin n) : State n :=
  if SeenArray8.model state.seen vertex then state else
    { state with seen := SeenArray8.mark state.seen vertex
                 stack := state.stack.push (FrameCursor32.start vertex) }

def retire (state : State n) (vertex : UInt32) : State n :=
  { state with stack := state.stack.pop, finished := state.finished.push vertex }

def update (state : State n) (frame : Frame) : State n :=
  { state with stack := ArrayLifo.replaceBack state.stack frame }

theorem discover_refines (fits : n ≤ UInt32.size) (rows : Rows n) (state : State n) (vertex : Fin n) :
    unpack rows (discover rows state vertex) = ForwardDfsFrameArray.discover (outgoing rows) (unpack rows state) vertex := by
  unfold discover ForwardDfsFrameArray.discover unpack
  split <;> simp only [RawFrameStack32.model_push rows _ _ (FrameCursor32.start_valid fits rows vertex),
    FrameCursor32.start_view fits rows vertex, outgoing]

theorem discover_stack_valid (fits : n ≤ UInt32.size) (rows : Rows n) (state : State n)
    (valid : RawFrameStack32.Valid rows state.stack) (vertex : Fin n) :
    RawFrameStack32.Valid rows (discover rows state vertex).stack := by
  unfold discover
  split
  · exact valid
  · exact RawFrameStack32.valid_push rows state.stack valid _ (FrameCursor32.start_valid fits rows vertex)

theorem discover_valid (fits : n ≤ UInt32.size) (rows : Rows n) (state : State n) (valid : Valid rows state) (vertex : Fin n) :
    Valid rows (discover rows state vertex) := by
  refine ⟨?_, discover_stack_valid fits rows state valid.stack vertex⟩
  rw [discover_refines fits]
  exact ForwardDfsFrameArray.discover_valid (outgoing rows) _ valid.base vertex

theorem typed_top (rows : Rows n) (state : State n) (valid : RawFrameStack32.Valid rows state.stack)
    (frame : Frame) (top : state.stack.back? = some frame) :
    (unpack rows state).stack.back? =
      some (FrameCursor32.view rows frame (RawFrameStack32.top_valid rows state.stack valid frame top)) := by
  simp only [unpack, RawFrameStack32.model_back rows state.stack valid, top]
  change FrameCursor32.decode rows frame = _
  exact FrameCursor32.decode_success rows frame _

theorem top_step_not_invalid (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) (frame : Frame) (top : state.stack.back? = some frame) :
    FrameCursor32.step rows frame ≠ .invalid :=
  FrameCursor32.step_not_invalid rows counts frame (RawFrameStack32.top_valid rows state.stack valid.stack frame top)

theorem retire_refines (rows : Rows n) (state : State n) (valid : RawFrameStack32.Valid rows state.stack)
    (frame : Frame) (top : state.stack.back? = some frame) :
    unpack rows (retire state frame.1) = ForwardDfsFrameArray.retire (unpack rows state) := by
  have found := typed_top rows state valid frame top
  simp only [unpack] at found
  simp only [retire, unpack, RawFrameStack32.model_pop rows state.stack valid, ForwardDfsFrameArray.retire, found,
    FrameCursor32.view_vertex_word]

theorem update_refines (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (state : State n)
    (valid : RawFrameStack32.Valid rows state.stack) (frame : Frame) (top : state.stack.back? = some frame)
    (running : frame.2 ≠ FrameCursor32.degree rows frame (RawFrameStack32.top_valid rows state.stack valid frame top)) :
    unpack rows (update state (FrameCursor32.advance frame)) = ForwardDfsFrameArray.trim (unpack rows state) := by
  let frame_valid := RawFrameStack32.top_valid rows state.stack valid frame top
  have found := typed_top rows state valid frame top
  simp only [unpack] at found
  simp only [update, unpack, RawFrameStack32.model_replace rows state.stack frame _ top frame_valid
    (FrameCursor32.advance_valid rows counts frame frame_valid running),
    FrameCursor32.advance_is_tail rows counts frame frame_valid running, ForwardDfsFrameArray.trim, found]

def tick (rows : Rows n) (state : State n) : State n :=
  match state.stack.back? with
  | none => state
  | some frame =>
    match FrameCursor32.step rows frame with
    | .invalid => state
    | .retire vertex => retire state vertex
    | .consume next picked =>
      match picked with
      | none => update state next
      | some child => discover rows (update state next) child

theorem tick_refines (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) :
    unpack rows (tick rows state) = ForwardDfsFrameArray.tick (outgoing rows) (unpack rows state) := by
  unfold outgoing
  cases top : state.stack.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    have typed_empty : (unpack rows state).stack.back? = none := by
      simp only [unpack, empty, RawFrameStack32.model_empty]
      rfl
    simp only [tick, top, ForwardDfsFrameArray.tick, typed_empty]
  | some frame =>
    let frame_valid := RawFrameStack32.top_valid rows state.stack valid.stack frame top
    have found := typed_top rows state valid.stack frame top
    by_cases done : frame.2 = FrameCursor32.degree rows frame frame_valid
    · rw [FrameCursor32.retire_tick rows counts frame frame_valid (unpack rows state) found done]
      simp only [tick, top, FrameCursor32.step_retire rows frame frame_valid done]
      exact retire_refines rows state valid.stack frame top
    · rw [FrameCursor32.consume_tick rows counts frame frame_valid (unpack rows state) found done]
      simp only [tick, top, FrameCursor32.step_consume rows frame frame_valid done]
      cases picked : FrameCursor32.target rows frame frame_valid with
      | none =>
        simp only [picked]
        exact update_refines rows counts state valid.stack frame top done
      | some child =>
        simp only [picked]
        rw [discover_refines fits, update_refines rows counts state valid.stack frame top done]
        rfl

theorem tick_stack_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : RawFrameStack32.Valid rows state.stack) : RawFrameStack32.Valid rows (tick rows state).stack := by
  cases top : state.stack.back? with
  | none => simpa only [tick, top] using valid
  | some frame =>
    let frame_valid := RawFrameStack32.top_valid rows state.stack valid frame top
    by_cases done : frame.2 = FrameCursor32.degree rows frame frame_valid
    · simp only [tick, top, FrameCursor32.step_retire rows frame frame_valid done, retire]
      exact RawFrameStack32.valid_pop rows state.stack valid
    · have updated : RawFrameStack32.Valid rows (update state (FrameCursor32.advance frame)).stack :=
        RawFrameStack32.valid_replace rows state.stack valid _ (FrameCursor32.advance_valid rows counts frame frame_valid done)
      simp only [tick, top, FrameCursor32.step_consume rows frame frame_valid done]
      cases picked : FrameCursor32.target rows frame frame_valid with
      | none => simpa only [picked] using updated
      | some child =>
        simpa only [picked] using discover_stack_valid fits rows (update state (FrameCursor32.advance frame)) updated child

theorem tick_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) : Valid rows (tick rows state) := by
  refine ⟨?_, tick_stack_valid fits rows counts state valid.stack⟩
  rw [tick_refines fits rows counts state valid]
  exact ForwardDfsFrameArray.tick_valid fits (outgoing rows) _ valid.base

def walk (rows : Rows n) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state =>
    match state.stack.back? with
    | none => state
    | some _ => walk rows fuel (tick rows state)

theorem walk_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (fuel : Nat)
    (state : State n) (valid : Valid rows state) : Valid rows (walk rows fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases top : state.stack.back? with
    | none => simpa only [walk, top] using valid
    | some frame => simpa only [walk, top] using ih _ (tick_valid fits rows counts state valid)

theorem walk_refines (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (fuel : Nat)
    (state : State n) (valid : Valid rows state) :
    unpack rows (walk rows fuel state) = ForwardDfsFrameArray.walk (outgoing rows) fuel (unpack rows state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases top : state.stack.back? with
    | none =>
      have empty := Array.back?_eq_none_iff.mp top
      have typed_empty : (unpack rows state).stack.back? = none := by
        simp only [unpack, empty, RawFrameStack32.model_empty]
        rfl
      simp only [walk, top, ForwardDfsFrameArray.walk, typed_empty]
    | some frame =>
      have found := typed_top rows state valid.stack frame top
      rw [walk, top, ih _ (tick_valid fits rows counts state valid), tick_refines fits rows counts state valid]
      simp only [ForwardDfsFrameArray.walk, found]

def root (rows : Rows n) (state : State n) (vertex : Fin n) : State n :=
  walk rows (ForwardDfs.capacity (List.finRange n) (outgoing rows)) (discover rows state vertex)

theorem root_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) (vertex : Fin n) : Valid rows (root rows state vertex) :=
  walk_valid fits rows counts _ _ (discover_valid fits rows state valid vertex)

theorem root_refines (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) (vertex : Fin n) :
    unpack rows (root rows state vertex) = ForwardDfsFrameArray.root (outgoing rows) (unpack rows state) vertex := by
  rw [root, walk_refines fits rows counts _ _ (discover_valid fits rows state valid vertex), discover_refines fits]
  rfl

def forest (rows : Rows n) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => forest rows rest (root rows state vertex)

theorem forest_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (roots : List (Fin n)) (state : State n) (valid : Valid rows state) : Valid rows (forest rows roots state) := by
  induction roots generalizing state with
  | nil => exact valid
  | cons vertex rest ih => exact ih _ (root_valid fits rows counts state valid vertex)

theorem forest_refines (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (roots : List (Fin n)) (state : State n) (valid : Valid rows state) :
    unpack rows (forest rows roots state) = ForwardDfsFrameArray.forest (outgoing rows) roots (unpack rows state) := by
  induction roots generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [forest, ih _ (root_valid fits rows counts state valid vertex), root_refines fits rows counts state valid,
      ForwardDfsFrameArray.forest]

def finish (rows : Rows n) (roots : List (Fin n)) : State n := forest rows roots (initial n)

theorem finish_valid (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (roots : List (Fin n)) :
    Valid rows (finish rows roots) := forest_valid fits rows counts roots _ (initial_valid rows)

theorem finish_refines (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (roots : List (Fin n)) :
    unpack rows (finish rows roots) = ForwardDfsFrameArray.finish (outgoing rows) roots := by
  rw [finish, forest_refines fits rows counts roots _ (initial_valid rows), initial_refines, ForwardDfsFrameArray.finish]

theorem finish_array_exact (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (roots : List (Fin n)) :
    (finish rows roots).finished = (ForwardDfsFrameArray.finish (outgoing rows) roots).finished :=
  congrArg ForwardDfsFrameArray.State.finished (finish_refines fits rows counts roots)

theorem finish_seen_exact (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (roots : List (Fin n)) :
    (finish rows roots).seen = (ForwardDfsFrameArray.finish (outgoing rows) roots).seen :=
  congrArg ForwardDfsFrameArray.State.seen (finish_refines fits rows counts roots)

theorem finish_stack_empty (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (roots : List (Fin n)) :
    (finish rows roots).stack = #[] := by
  have drained := ForwardDfsFrameArray.finish_stack_empty fits (outgoing rows) roots
  have same := congrArg ForwardDfsFrameArray.State.stack (finish_refines fits rows counts roots)
  have size := RawFrameStack32.model_size rows (finish rows roots).stack (finish_valid fits rows counts roots).stack
  change (RawFrameStack32.model rows (finish rows roots).stack) = _ at same
  rw [same, drained] at size
  exact Array.eq_empty_of_size_eq_zero size.symm

theorem stack_bound (rows : Rows n) (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) : state.stack.size ≤ n := by
  rw [← RawFrameStack32.model_size rows state.stack valid.stack]
  exact ForwardDfsFrameArray.stack_bound (unpack rows state) invariant

theorem walk_invariant (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (fuel : Nat)
    (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) :
    ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows (walk rows fuel state))) := by
  rw [walk_refines fits rows counts fuel state valid]
  exact ForwardDfsFrameArray.walk_invariant fits (outgoing rows) fuel _ valid.base invariant

theorem walk_stack_bound (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (fuel : Nat)
    (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) :
    (walk rows fuel state).stack.size ≤ n :=
  stack_bound rows _ (walk_valid fits rows counts fuel state valid) (walk_invariant fits rows counts fuel state valid invariant)

theorem initial_invariant (rows : Rows n) :
    ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows (initial n))) := by
  rw [initial_refines]
  exact ForwardDfsFrameArray.initial_invariant n

theorem discover_invariant (fits : n ≤ UInt32.size) (rows : Rows n) (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) (vertex : Fin n) :
    ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows (discover rows state vertex))) := by
  rw [discover_refines fits]
  exact ForwardDfsFrameArray.discover_invariant (outgoing rows) _ valid.base invariant vertex

theorem seeded_walk_bound (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows) (fuel : Nat)
    (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) (vertex : Fin n) :
    (walk rows fuel (discover rows state vertex)).stack.size ≤ n :=
  walk_stack_bound fits rows counts fuel _ (discover_valid fits rows state valid vertex)
    (discover_invariant fits rows state valid invariant vertex)

theorem root_drains (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (state : State n) (valid : Valid rows state) (empty : state.stack = #[]) (vertex : Fin n) :
    (root rows state vertex).stack = #[] := by
  have typed_empty : (unpack rows state).stack = #[] := by simp only [unpack, empty, RawFrameStack32.model_empty]
  have drained := ForwardDfsFrameArray.root_drains fits (outgoing rows) (unpack rows state) valid.base typed_empty vertex
  have same := congrArg ForwardDfsFrameArray.State.stack (root_refines fits rows counts state valid vertex)
  have size := RawFrameStack32.model_size rows (root rows state vertex).stack (root_valid fits rows counts state valid vertex).stack
  change RawFrameStack32.model rows (root rows state vertex).stack = _ at same
  rw [same, drained] at size
  exact Array.eq_empty_of_size_eq_zero size.symm

theorem forest_invariant (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (roots : List (Fin n)) (state : State n) (valid : Valid rows state)
    (invariant : ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows state))) :
    ForwardDfs.Invariant (ForwardDfsFrameArray.abstract (unpack rows (forest rows roots state))) := by
  rw [forest_refines fits rows counts roots state valid]
  exact ForwardDfsFrameArray.forest_invariant fits (outgoing rows) roots _ valid.base invariant

end PetaProof.ForwardDfsRaw32
