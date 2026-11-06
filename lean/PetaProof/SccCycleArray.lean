import PetaProof.SccReportFlag

/-!
第二DFSの根走査と同時に、count>1 || self_loopをUInt8配列へ書く。
既割当の根はDFSも書込も行わない。成分ごとの全頂点再走査は証明用仕様にだけ現れる。
-/
namespace PetaProof.SccCycleArray

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

def byte (flag : Bool) : UInt8 := if flag then 1 else 0

theorem byte_nonzero (flag : Bool) : (byte flag != 0) = flag := by cases flag <;> decide

structure State (V : Type u) where
  number : ComponentNumbering.State V
  flags : Array UInt8

def initial (capacity : Nat) : State V := ⟨ComponentNumbering.initial, Array.replicate capacity 0⟩

def step (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool) (state : State V) (root : V) : State V :=
  if state.number.result root = none then
    let report := SccParentCallback.explore view vertices allow state.number.result state.number.roots.length root
    ⟨⟨report.1.result, state.number.roots ++ [root]⟩,
      state.flags.setIfInBounds state.number.roots.length (byte (SccReportFlag.reportFlag report))⟩
  else state

def pass (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool) : List V → State V → State V
  | [], state => state
  | root :: rest, state => pass view vertices allow rest (step view vertices allow state root)

theorem step_number (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool) (state : State V) (root : V) :
    (step view vertices allow state root).number =
      ComponentNumbering.step vertices.length (SccIndexedView.parents view vertices allow) state.number root := by
  by_cases fresh : state.number.result root = none
  · simp only [step, ComponentNumbering.step, if_pos fresh, SccParentCallback.explore_graph]
    rfl
  · simp only [step, ComponentNumbering.step, if_neg fresh]

theorem pass_number (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool) (order : List V) (state : State V) :
    (pass view vertices allow order state).number =
      ComponentNumbering.pass vertices.length (SccIndexedView.parents view vertices allow) order state.number := by
  induction order generalizing state with
  | nil => rfl
  | cons root rest ih => rw [pass, ih, step_number, ComponentNumbering.pass]

structure Invariant (vertices : List V) (selfLoop : V → Bool) (state : State V) : Prop where
  numbering : ComponentNumbering.Invariant state.number
  size : state.flags.size = vertices.length
  written : ∀ id, id < state.number.roots.length → state.flags[id]? =
    some (byte (SccReportFlag.flag vertices state.number.result selfLoop id))
  unused : ∀ id, state.number.roots.length ≤ id → id < vertices.length → state.flags[id]? = some 0

omit [DecidableEq V] in
theorem initial_invariant (vertices : List V) (selfLoop : V → Bool) : Invariant vertices selfLoop (initial vertices.length : State V) := by
  refine ⟨ComponentNumbering.initial_invariant, by simp [initial], ?_, ?_⟩
  · intro id bound
    change id < 0 at bound
    omega
  · intro id _ inside
    simp [initial, Array.getElem?_replicate, inside]

theorem write_in_bounds (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (state : State V)
    (inv : Invariant vertices (SccIndexedView.selfLoop view vertices allow) state) (root : V)
    (fresh : state.number.result root = none) : state.number.roots.length < state.flags.size := by
  have next_valid := ComponentNumbering.step_preserves vertices.length (SccIndexedView.parents view vertices allow)
    state.number inv.numbering root
  have bound := ComponentNumbering.roots_bound vertices unique covered _ next_valid
  simp only [ComponentNumbering.step, if_pos fresh, List.length_append, List.length_singleton] at bound
  rw [inv.size]
  omega

/-- 既割当の根では番号もフラグ配列も変更しない。 -/
theorem skip_assigned (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool)
    (state : State V) (root : V) (assigned : state.number.result root ≠ none) :
    step view vertices allow state root = state := by simp only [step, if_neg assigned]

theorem step_eq_checked (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (state : State V)
    (inv : Invariant vertices (SccIndexedView.selfLoop view vertices allow) state) (root : V)
    (fresh : state.number.result root = none) :
    let report := SccParentCallback.explore view vertices allow state.number.result state.number.roots.length root
    step view vertices allow state root =
      ⟨⟨report.1.result, state.number.roots ++ [root]⟩,
        state.flags.set state.number.roots.length (byte (SccReportFlag.reportFlag report))
          (write_in_bounds view vertices unique covered allow state inv root fresh)⟩ := by
  simp only [step, if_pos fresh]
  rw [Array.setIfInBounds, dif_pos (write_in_bounds view vertices unique covered allow state inv root fresh)]

theorem step_preserves (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (state : State V)
    (inv : Invariant vertices (SccIndexedView.selfLoop view vertices allow) state) (root : V) :
    Invariant vertices (SccIndexedView.selfLoop view vertices allow) (step view vertices allow state root) := by
  have next_number : ComponentNumbering.Invariant (step view vertices allow state root).number := by
    rw [step_number]
    exact ComponentNumbering.step_preserves _ _ state.number inv.numbering root
  by_cases fresh : state.number.result root = none
  · have room := write_in_bounds view vertices unique covered allow state inv root fresh
    let report := SccParentCallback.explore view vertices allow state.number.result state.number.roots.length root
    have report_exact := SccReportFlag.report_exact view vertices unique covered allow state.number inv.numbering root
    rw [step, if_pos fresh] at next_number ⊢
    refine ⟨next_number, by simp [inv.size], ?_, ?_⟩
    · intro id lower
      change id < (state.number.roots ++ [root]).length at lower
      simp only [List.length_append, List.length_singleton] at lower
      change (state.flags.setIfInBounds state.number.roots.length (byte (SccReportFlag.reportFlag report)))[id]? =
        some (byte (SccReportFlag.flag vertices report.1.result (SccIndexedView.selfLoop view vertices allow) id))
      by_cases same : id = state.number.roots.length
      · subst id
        simp only [Array.getElem?_setIfInBounds, if_pos room, ↓reduceIte]
        exact congrArg (fun flag => some (byte flag)) report_exact
      · have old : id < state.number.roots.length := by omega
        simp only [Array.getElem?_setIfInBounds, if_pos room, if_neg (Ne.symm same)]
        have kept := SccReportFlag.old_members_stable view vertices allow state.number root id old
        rw [SccReportFlag.flag, kept]
        exact inv.written id old
    · intro id later inside
      change (state.number.roots ++ [root]).length ≤ id at later
      simp only [List.length_append, List.length_singleton] at later
      have different : state.number.roots.length ≠ id := by omega
      simp only [Array.getElem?_setIfInBounds, if_pos room, if_neg different]
      exact inv.unused id (by omega) inside
  · simpa only [step, if_neg fresh] using inv

def WritesSafe (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool) : List V → State V → Prop
  | [], _ => True
  | root :: rest, state =>
      (state.number.result root = none → state.number.roots.length < state.flags.size) ∧
        WritesSafe view vertices allow rest (step view vertices allow state root)

theorem pass_preserves_and_safe (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (order : List V) (state : State V)
    (inv : Invariant vertices (SccIndexedView.selfLoop view vertices allow) state) :
    Invariant vertices (SccIndexedView.selfLoop view vertices allow) (pass view vertices allow order state) ∧
      WritesSafe view vertices allow order state := by
  induction order generalizing state with
  | nil => exact ⟨inv, trivial⟩
  | cons root rest ih =>
    have head := write_in_bounds view vertices unique covered allow state inv root
    obtain ⟨after, tail_safe⟩ := ih _ (step_preserves view vertices unique covered allow state inv root)
    exact ⟨after, head, tail_safe⟩

def finish (view : SccIndexedView.View V E) (vertices order : List V) (allow : E → Bool) : State V :=
  pass view vertices allow order (initial vertices.length)

theorem finish_number (view : SccIndexedView.View V E) (vertices order : List V) (allow : E → Bool) :
    (finish view vertices order allow).number =
      ComponentNumbering.finish vertices order (SccIndexedView.parents view vertices allow) :=
  pass_number view vertices allow order _

theorem finish_invariant (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V) (allow : E → Bool) :
    Invariant vertices (SccIndexedView.selfLoop view vertices allow) (finish view vertices order allow) :=
  (pass_preserves_and_safe view vertices unique covered allow order _ (initial_invariant vertices _)).1

theorem finish_writes_safe (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V) (allow : E → Bool) :
    WritesSafe view vertices allow order (initial vertices.length) :=
  (pass_preserves_and_safe view vertices unique covered allow order _ (initial_invariant vertices _)).2

def component (state : State V) (vertex : V) : Nat := (state.number.result vertex).getD 0
def keep (state : State V) (vertex : V) : Bool := (state.flags[component state vertex]?.getD 0) != 0

end PetaProof.SccCycleArray
