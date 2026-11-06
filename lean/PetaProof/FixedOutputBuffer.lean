import PetaProof.ReverseDfsStores

/-! 長さNの出力表を先に初期化し、次の空欄へ一度ずつ格納する。列末尾の全走査や再確保は不要。 -/
namespace PetaProof.FixedOutputBuffer

universe u
variable {V : Type u}

structure Buffer (V : Type u) where
  data : Array (Option V)
  used : Nat

def initial (n : Nat) : Buffer V := ⟨Array.replicate n none, 0⟩

def append (state : Buffer V) (value : V) : Buffer V :=
  if state.used < state.data.size then
    ⟨state.data.setIfInBounds state.used (some value), state.used + 1⟩
  else state

theorem append_size (state : Buffer V) (value : V) : (append state value).data.size = state.data.size := by
  by_cases room : state.used < state.data.size <;> simp [append, room]

theorem append_used (state : Buffer V) (value : V) (room : state.used < state.data.size) :
    (append state value).used = state.used + 1 := by simp [append, room]

theorem append_writes (state : Buffer V) (value : V) (room : state.used < state.data.size) :
    (append state value).data[state.used]? = some (some value) := by
  simp [append, room, Array.getElem?_setIfInBounds]

theorem append_preserves (state : Buffer V) (value : V) (index : Nat) (different : state.used ≠ index) :
    (append state value).data[index]? = state.data[index]? := by
  by_cases room : state.used < state.data.size
  · simp [append, room, Array.getElem?_setIfInBounds, different]
  · simp [append, room]

def fill : List V → Buffer V → Buffer V
  | [], state => state
  | value :: rest, state => fill rest (append state value)

def SafeFill : List V → Buffer V → Prop
  | [], _ => True
  | value :: rest, state => state.used < state.data.size ∧ SafeFill rest (append state value)

theorem fill_safe (values : List V) (state : Buffer V) (enough : state.used + values.length ≤ state.data.size) :
    SafeFill values state := by
  induction values generalizing state with
  | nil => trivial
  | cons value rest ih =>
    have room : state.used < state.data.size := by simp only [List.length_cons] at enough; omega
    refine ⟨room, ih (append state value) ?_⟩
    rw [append_used state value room, append_size]
    simp only [List.length_cons] at enough
    omega

theorem fill_size (values : List V) (state : Buffer V) : (fill values state).data.size = state.data.size := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih => rw [fill, ih, append_size]

theorem fill_used (values : List V) (state : Buffer V) (enough : state.used + values.length ≤ state.data.size) :
    (fill values state).used = state.used + values.length := by
  induction values generalizing state with
  | nil => simp [fill]
  | cons value rest ih =>
    have room : state.used < state.data.size := by simp only [List.length_cons] at enough; omega
    have remaining : (append state value).used + rest.length ≤ (append state value).data.size := by
      rw [append_used state value room, append_size]
      simp only [List.length_cons] at enough
      omega
    rw [fill, ih _ remaining, append_used state value room]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem fill_preserves_prefix (values : List V) (state : Buffer V) (index : Nat) (old : index < state.used)
    (enough : state.used + values.length ≤ state.data.size) :
    (fill values state).data[index]? = state.data[index]? := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
    have room : state.used < state.data.size := by simp only [List.length_cons] at enough; omega
    have remaining : (append state value).used + rest.length ≤ (append state value).data.size := by
      rw [append_used state value room, append_size]
      simp only [List.length_cons] at enough
      omega
    rw [fill, ih _ (by rw [append_used state value room]; omega) remaining,
      append_preserves state value index (by omega)]

theorem fill_lookup (values : List V) (state : Buffer V) (enough : state.used + values.length ≤ state.data.size)
    (index : Nat) (inside : index < values.length) :
    (fill values state).data[state.used + index]? = (values[index]?).map some := by
  induction values generalizing state index with
  | nil => simp at inside
  | cons value rest ih =>
    have room : state.used < state.data.size := by simp only [List.length_cons] at enough; omega
    have remaining : (append state value).used + rest.length ≤ (append state value).data.size := by
      rw [append_used state value room, append_size]
      simp only [List.length_cons] at enough
      omega
    cases index with
    | zero =>
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.map_some]
      rw [fill, fill_preserves_prefix rest (append state value) state.used
        (by rw [append_used state value room]; omega) remaining, append_writes state value room]
      rfl
    | succ index =>
      have tail := ih (append state value) remaining index (by simpa using inside)
      simpa only [fill, append_used state value room, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.getElem?_cons_succ] using tail

/-- 満杯まで格納しても、データ表の長さを増やさない。 -/
theorem output_safe (values : List V) (n : Nat) (bounded : values.length ≤ n) :
    SafeFill values (initial n) ∧ (fill values (initial n)).used = values.length ∧
      (fill values (initial n)).data.size = n := by
  have enough : (initial n : Buffer V).used + values.length ≤ (initial n : Buffer V).data.size := by
    simpa [initial] using bounded
  exact ⟨fill_safe values _ enough, by simpa [initial] using fill_used values _ enough,
    by simpa [initial] using fill_size values (initial n)⟩

end PetaProof.FixedOutputBuffer
