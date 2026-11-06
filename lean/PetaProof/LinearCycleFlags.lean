import PetaProof.ComponentCycleFlags

/-! 成分番号が確定した後、各頂点を一度集計して循環フラグを作る。 -/
namespace PetaProof.LinearCycleFlags

universe u
variable {V : Type u}

structure State where
  counts : Array Nat
  self : Array Bool

def initial (n : Nat) : State := ⟨Array.replicate n 0, Array.replicate n false⟩

/-- 自己辺の有無は頂点ごとに一度入力する。成分の全頂点再走査はしない。 -/
def add (component : V → Nat) (selfLoop : V → Bool) (state : State) (vertex : V) : State :=
  let id := component vertex
  ⟨state.counts.setIfInBounds id (state.counts[id]?.getD 0 + 1),
    state.self.setIfInBounds id (state.self[id]?.getD false || selfLoop vertex)⟩

def scan (component : V → Nat) (selfLoop : V → Bool) : List V → State → State
  | [], state => state
  | vertex :: rest, state => scan component selfLoop rest (add component selfLoop state vertex)

theorem add_sizes (component : V → Nat) (selfLoop : V → Bool) (state : State) (vertex : V) :
    (add component selfLoop state vertex).counts.size = state.counts.size ∧
      (add component selfLoop state vertex).self.size = state.self.size := by
  simp [add]

theorem scan_sizes (component : V → Nat) (selfLoop : V → Bool) (vertices : List V) (state : State) :
    (scan component selfLoop vertices state).counts.size = state.counts.size ∧
      (scan component selfLoop vertices state).self.size = state.self.size := by
  induction vertices generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons vertex rest ih =>
    have tail := ih (add component selfLoop state vertex)
    have step := add_sizes component selfLoop state vertex
    exact ⟨tail.1.trans step.1, tail.2.trans step.2⟩

theorem scan_spec (component : V → Nat) (selfLoop : V → Bool) (vertices : List V)
    (state : State) (id : Nat) (count_bound : id < state.counts.size) (self_bound : id < state.self.size) :
    (scan component selfLoop vertices state).counts[id]?.getD 0 =
        state.counts[id]?.getD 0 + (vertices.filter (fun vertex => component vertex == id)).length ∧
      (scan component selfLoop vertices state).self[id]?.getD false =
        (state.self[id]?.getD false ||
          (vertices.filter (fun vertex => component vertex == id)).any selfLoop) := by
  induction vertices generalizing state with
  | nil => simp [scan]
  | cons vertex rest ih =>
    have sizes := add_sizes component selfLoop state vertex
    have tail := ih (add component selfLoop state vertex) (by omega) (by omega)
    by_cases same : component vertex = id
    · simp only [scan] at ⊢
      rw [tail.1, tail.2]
      simp [add, Array.getElem?_setIfInBounds, same, count_bound, self_bound,
        List.filter_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Bool.or_assoc]
    · simp only [scan] at ⊢
      rw [tail.1, tail.2]
      simp [add, Array.getElem?_setIfInBounds, same, List.filter_cons]

def build (vertices : List V) (component : V → Nat) (selfLoop : V → Bool) : State :=
  scan component selfLoop vertices (initial vertices.length)

def flag (state : State) (id : Nat) : Bool :=
  decide (1 < state.counts[id]?.getD 0) || state.self[id]?.getD false

theorem flag_eq (vertices : List V) (component : V → Nat) (selfLoop : V → Bool)
    (id : Nat) (bound : id < vertices.length) :
    flag (build vertices component selfLoop) id = ComponentCycleFlags.flag vertices component selfLoop id := by
  have spec := scan_spec component selfLoop vertices (initial vertices.length) id
    (by simpa [initial] using bound) (by simpa [initial] using bound)
  simp only [initial, Array.getElem?_replicate, bound, reduceIte, Option.getD_some,
    Nat.zero_add, Bool.false_or] at spec
  simp only [flag, build, initial, spec.1, spec.2, ComponentCycleFlags.flag, ComponentCycleFlags.members]

/-- 二つの配列初期化と、一頂点あたり二読出し・二更新のみを数える。
自己辺の検出や成分番号の算出費用はこの会計に含めない。 -/
def aggregationWork (vertices : List V) : Nat := 2 * vertices.length + 4 * vertices.length

theorem aggregationWork_eq (vertices : List V) : aggregationWork vertices = 6 * vertices.length := by
  unfold aggregationWork
  omega

end PetaProof.LinearCycleFlags
