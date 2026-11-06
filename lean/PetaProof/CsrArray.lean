import PetaProof.CsrFill

/-!
CSRのcursorと辺格納を有限Arrayへ精密化する。
totalな定義にはsetIfInBoundsを使うが、全アクセスが範囲内で通常のsetに等しいことを別途証明する。
要素は依然Natであり、機械整数の桁あふれやC++の実行モデルは扱わない。
-/
namespace PetaProof.CsrArray

universe u
variable {E : Type u}

structure State (E : Type u) where
  cursor : Array Nat
  memory : Array (Option E)

def offsets (n : Nat) (counts : Nat → Nat) : Array Nat :=
  Array.ofFn (fun vertex : Fin (n + 1) => Csr.offset counts vertex.val)

theorem offsets_size (n : Nat) (counts : Nat → Nat) : (offsets n counts).size = n + 1 := by
  simp [offsets]

theorem offsets_get (n : Nat) (counts : Nat → Nat) (vertex : Nat) (inside : vertex ≤ n) :
    (offsets n counts)[vertex]? = some (Csr.offset counts vertex) := by
  simp [offsets, Array.getElem?_ofFn, show vertex < n + 1 by omega]

def initial (n capacity : Nat) (counts : Nat → Nat) : State E :=
  ⟨offsets n counts, Array.replicate capacity none⟩

def put (target : E → Nat) (edge : E) (state : State E) : State E :=
  let vertex := target edge
  let address := state.cursor[vertex]?.getD 0
  ⟨state.cursor.setIfInBounds vertex (address + 1), state.memory.setIfInBounds address (some edge)⟩

def fill (target : E → Nat) : List E → State E → State E
  | [], state => state
  | edge :: rest, state => fill target rest (put target edge state)

structure Represents (n capacity : Nat) (array : State E) (model : Csr.State E) : Prop where
  cursor_size : array.cursor.size = n + 1
  memory_size : array.memory.size = capacity
  cursor_values : ∀ vertex, vertex ≤ n → array.cursor[vertex]? = some (model.cursor vertex)
  memory_values : ∀ address, address < capacity → array.memory[address]? = some (model.memory address)

theorem initial_represents (n capacity : Nat) (counts : Nat → Nat) :
    Represents n capacity (initial n capacity counts : State E) (Csr.initial counts) := by
  refine ⟨offsets_size n counts, by simp [initial], ?_, ?_⟩
  · exact offsets_get n counts
  · intro address inside
    simp [initial, Csr.initial, Array.getElem?_replicate, inside]

/-- cursorの参照・更新と格納先への書込の、両方の配列境界条件。 -/
def StepSafe (target : E → Nat) (edge : E) (state : State E) : Prop :=
  target edge < state.cursor.size ∧ state.cursor[target edge]?.getD 0 < state.memory.size

theorem put_safe {n capacity : Nat} (target : E → Nat) (edge : E) (array : State E) (model : Csr.State E)
    (rep : Represents n capacity array model) (child : target edge < n) (address : model.cursor (target edge) < capacity) :
    StepSafe target edge array := by
  constructor
  · rw [rep.cursor_size]; omega
  · rw [rep.cursor_values (target edge) (by omega), rep.memory_size]
    exact address

/-- 有効な入力ではtotalな更新が、境界証拠付きのArray.setそのものと一致する。 -/
theorem put_eq_checked (target : E → Nat) (edge : E) (state : State E) (safe : StepSafe target edge state) :
    put target edge state =
      ⟨state.cursor.set (target edge) (state.cursor[target edge]?.getD 0 + 1) safe.1,
       state.memory.set (state.cursor[target edge]?.getD 0) (some edge) safe.2⟩ := by
  change State.mk _ _ = State.mk _ _
  rw [State.mk.injEq]
  exact ⟨dif_pos safe.1, dif_pos safe.2⟩

theorem put_represents {n capacity : Nat} (target : E → Nat) (edge : E) (array : State E) (model : Csr.State E)
    (rep : Represents n capacity array model) (child : target edge < n) (address : model.cursor (target edge) < capacity) :
    Represents n capacity (put target edge array) (Csr.put target edge model) := by
  have found := rep.cursor_values (target edge) (by omega)
  have cursor_inside : target edge < array.cursor.size := by rw [rep.cursor_size]; omega
  have memory_inside : model.cursor (target edge) < array.memory.size := by rw [rep.memory_size]; exact address
  constructor
  · simp [put, rep.cursor_size]
  · simp [put, rep.memory_size]
  · intro vertex inside
    simp only [put, found, Option.getD_some, Array.getElem?_setIfInBounds, if_pos cursor_inside]
    by_cases same : vertex = target edge
    · subst vertex
      simp [Csr.put, Csr.increment]
    · simp [Csr.put, Csr.increment, same, Ne.symm same, rep.cursor_values vertex inside]
  · intro slot inside
    simp only [put, found, Option.getD_some, Array.getElem?_setIfInBounds, if_pos memory_inside]
    by_cases same : slot = model.cursor (target edge)
    · subst slot
      simp [Csr.put]
    · simp [Csr.put, same, Ne.symm same, rep.memory_values slot inside]

def AllSafe (target : E → Nat) : List E → State E → Prop
  | [], _ => True
  | edge :: rest, state => StepSafe target edge state ∧ AllSafe target rest (put target edge state)

/-- 各反復の安全性と、有限配列・論理メモリの同値を同時に帰納する。 -/
theorem fill_represents_and_safe {n capacity : Nat} (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (array : State E) (model : Csr.State E)
    (rep : Represents n capacity array model) (safe : Csr.WritesWithin capacity target edges model) :
    Represents n capacity (fill target edges array) (Csr.fill target edges model) ∧ AllSafe target edges array := by
  induction edges generalizing array model with
  | nil => exact ⟨rep, trivial⟩
  | cons edge rest ih =>
    have child := bounded edge (by simp)
    have head_safe := put_safe target edge array model rep child safe.1
    have next := put_represents target edge array model rep child safe.1
    have tail_bound : ∀ edge ∈ rest, target edge < n := fun edge member => bounded edge (by simp [member])
    obtain ⟨after, tail_safe⟩ := ih tail_bound _ _ next safe.2
    exact ⟨after, head_safe, tail_safe⟩

def built (n : Nat) (target : E → Nat) (edges : List E) : State E :=
  fill target edges (initial n edges.length (Csr.degrees target edges))

theorem built_represents_and_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    Represents n edges.length (built n target edges) (Csr.built target edges) ∧
      AllSafe target edges (initial n edges.length (Csr.degrees target edges)) :=
  fill_represents_and_safe target edges bounded _ _ (initial_represents n edges.length _)
    (Csr.built_writes_within target edges n bounded)

def readOptions (state : State E) (start count : Nat) : List (Option E) :=
  (List.range count).map (fun index => state.memory[start + index]?.getD none)

theorem readOptions_represents {n capacity : Nat} (array : State E) (model : Csr.State E)
    (rep : Represents n capacity array model) (start count : Nat) (inside : start + count ≤ capacity) :
    readOptions array start count = Csr.readOptions model.memory start count := by
  apply List.map_congr_left
  intro index member
  have smaller := List.mem_range.mp member
  have address : start + index < capacity := by omega
  simp only [rep.memory_values _ address, Option.getD_some]

/-- offsetも有限配列から2か所読み、半開区間の差を読出し長に使う。 -/
def rowOptions (n : Nat) (target : E → Nat) (edges : List E) (vertex : Nat) : List (Option E) :=
  let positions := offsets n (Csr.degrees target edges)
  let start := positions[vertex]?.getD 0
  let stop := positions[vertex + 1]?.getD 0
  readOptions (built n target edges) start (stop - start)

/-- offsetの2参照が有効で、半開区間が配列内に収まる。空区間の終端はsizeでもよい。 -/
theorem row_accesses_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    let positions := offsets n (Csr.degrees target edges)
    vertex < positions.size ∧ vertex + 1 < positions.size ∧
      positions[vertex]?.getD 0 ≤ positions[vertex + 1]?.getD 0 ∧
      positions[vertex + 1]?.getD 0 ≤ (built n target edges).memory.size := by
  have rep := (built_represents_and_safe n target edges bounded).1
  have ordered := Csr.offset_mono (Csr.degrees target edges) vertex (vertex + 1) (by omega)
  have end_bound := Csr.offset_mono (Csr.degrees target edges) (vertex + 1) n (by omega)
  have capacity := Csr.total_capacity target edges n bounded
  simp only [offsets_size, offsets_get n _ vertex (by omega), offsets_get n _ (vertex + 1) (by omega),
    Option.getD_some, rep.memory_size]
  exact ⟨by omega, by omega, ordered, by omega⟩

theorem rowOptions_exact (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    rowOptions n target edges vertex = (Csr.bucket target edges vertex).map some := by
  have rep := (built_represents_and_safe n target edges bounded).1
  have monotone := Csr.offset_mono (Csr.degrees target edges) vertex (vertex + 1) (by omega)
  have end_bound := Csr.offset_mono (Csr.degrees target edges) (vertex + 1) n (by omega)
  have capacity := Csr.total_capacity target edges n bounded
  simp only [rowOptions, offsets_get n _ vertex (by omega), offsets_get n _ (vertex + 1) (by omega), Option.getD_some]
  rw [readOptions_represents _ _ rep _ _ (by omega), Csr.offset_gap]
  exact Csr.readOptions_exact target edges vertex

def row (n : Nat) (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  (rowOptions n target edges vertex).filterMap id

theorem row_exact (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    row n target edges vertex = Csr.bucket target edges vertex := by
  rw [row, rowOptions_exact n target edges bounded vertex inside]
  simp [List.filterMap_map, Function.comp_def]

end PetaProof.CsrArray
