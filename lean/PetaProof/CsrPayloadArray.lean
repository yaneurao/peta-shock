import PetaProof.CsrArray

/-!
未書込を表すOptionは証明用とし、辺IDそのものを保存するArrayへ接続する。
任意の初期値seedで埋めても、完成した区間の読出し結果は変わらない。
-/
namespace PetaProof.CsrPayloadArray

universe u
variable {E : Type u}

structure State (E : Type u) where
  cursor : Array Nat
  memory : Array E

def erase (seed : E) (state : CsrArray.State E) : State E :=
  ⟨state.cursor, state.memory.map (fun value => value.getD seed)⟩

def initial (n capacity : Nat) (counts : Nat → Nat) (seed : E) : State E :=
  ⟨CsrArray.offsets n counts, Array.replicate capacity seed⟩

def put (target : E → Nat) (edge : E) (state : State E) : State E :=
  let address := state.cursor[target edge]?.getD 0
  ⟨state.cursor.setIfInBounds (target edge) (address + 1), state.memory.setIfInBounds address edge⟩

def fill (target : E → Nat) : List E → State E → State E
  | [], state => state
  | edge :: rest, state => fill target rest (put target edge state)

theorem erase_initial (n capacity : Nat) (counts : Nat → Nat) (seed : E) :
    erase seed (CsrArray.initial n capacity counts) = initial n capacity counts seed := by
  simp [erase, CsrArray.initial, initial]

theorem erase_put (seed : E) (target : E → Nat) (edge : E) (state : CsrArray.State E) :
    erase seed (CsrArray.put target edge state) = put target edge (erase seed state) := by
  simp [erase, CsrArray.put, put]

theorem erase_fill (seed : E) (target : E → Nat) (edges : List E) (state : CsrArray.State E) :
    erase seed (CsrArray.fill target edges state) = fill target edges (erase seed state) := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih => rw [CsrArray.fill, ih, erase_put]; rfl

def built (n : Nat) (seed : E) (target : E → Nat) (edges : List E) : State E :=
  fill target edges (initial n edges.length (Csr.degrees target edges) seed)

theorem erase_built (n : Nat) (seed : E) (target : E → Nat) (edges : List E) :
    erase seed (CsrArray.built n target edges) = built n seed target edges := by
  simp only [CsrArray.built, erase_fill, erase_initial, built]

def StepSafe (target : E → Nat) (edge : E) (state : State E) : Prop :=
  target edge < state.cursor.size ∧ state.cursor[target edge]?.getD 0 < state.memory.size

def AllSafe (target : E → Nat) : List E → State E → Prop
  | [], _ => True
  | edge :: rest, state => StepSafe target edge state ∧ AllSafe target rest (put target edge state)

theorem stepSafe_erase (seed : E) (target : E → Nat) (edge : E) (state : CsrArray.State E) :
    StepSafe target edge (erase seed state) ↔ CsrArray.StepSafe target edge state := by
  simp [StepSafe, CsrArray.StepSafe, erase]

theorem allSafe_erase (seed : E) (target : E → Nat) (edges : List E) (state : CsrArray.State E) :
    AllSafe target edges (erase seed state) ↔ CsrArray.AllSafe target edges state := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    change (StepSafe target edge (erase seed state) ∧ AllSafe target rest (put target edge (erase seed state))) ↔ _
    rw [stepSafe_erase, ← erase_put, ih]
    rfl

theorem built_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    AllSafe target edges (initial n edges.length (Csr.degrees target edges) seed) := by
  rw [← erase_initial, allSafe_erase]
  exact (CsrArray.built_represents_and_safe n target edges bounded).2

theorem built_sizes (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    (built n seed target edges).cursor.size = n + 1 ∧ (built n seed target edges).memory.size = edges.length := by
  rw [← erase_built]
  have rep := (CsrArray.built_represents_and_safe n target edges bounded).1
  simpa only [erase, Array.size_map] using And.intro rep.cursor_size rep.memory_size

theorem row_accesses_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    let positions := CsrArray.offsets n (Csr.degrees target edges)
    vertex < positions.size ∧ vertex + 1 < positions.size ∧
      positions[vertex]?.getD 0 ≤ positions[vertex + 1]?.getD 0 ∧
      positions[vertex + 1]?.getD 0 ≤ (built n seed target edges).memory.size := by
  have rep := (CsrArray.built_represents_and_safe n target edges bounded).1
  have safe := CsrArray.row_accesses_safe n target edges bounded vertex inside
  simpa only [rep.memory_size, (built_sizes n seed target edges bounded).2] using safe

/-- plain配列でも、全ての有効な更新は境界証拠付きsetに一致する。 -/
theorem put_eq_checked (target : E → Nat) (edge : E) (state : State E) (safe : StepSafe target edge state) :
    put target edge state =
      ⟨state.cursor.set (target edge) (state.cursor[target edge]?.getD 0 + 1) safe.1,
       state.memory.set (state.cursor[target edge]?.getD 0) edge safe.2⟩ := by
  change State.mk _ _ = State.mk _ _
  rw [State.mk.injEq]
  exact ⟨dif_pos safe.1, dif_pos safe.2⟩

def read (seed : E) (state : State E) (start count : Nat) : List E :=
  (List.range count).map (fun index => state.memory[start + index]?.getD seed)

theorem erase_read (seed : E) (state : CsrArray.State E) (start count : Nat) :
    read seed (erase seed state) start count =
      (CsrArray.readOptions state start count).map (fun value => value.getD seed) := by
  simp only [read, CsrArray.readOptions, List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [erase, Array.getElem?_map, Function.comp_apply]
  cases found : state.memory[start + index]? with
  | none => rfl
  | some value => rfl

def row (n : Nat) (seed : E) (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  let positions := CsrArray.offsets n (Csr.degrees target edges)
  let start := positions[vertex]?.getD 0
  let stop := positions[vertex + 1]?.getD 0
  read seed (built n seed target edges) start (stop - start)

theorem row_erases_options (n : Nat) (seed : E) (target : E → Nat) (edges : List E) (vertex : Nat) :
    row n seed target edges vertex =
      (CsrArray.rowOptions n target edges vertex).map (fun value => value.getD seed) := by
  simp only [row, ← erase_built, erase_read, CsrArray.rowOptions]

/-- 完成した区間は全て上書き済みなので、任意の初期値seedの影響は消える。 -/
theorem row_exact (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    row n seed target edges vertex = Csr.bucket target edges vertex := by
  rw [row_erases_options, CsrArray.rowOptions_exact n target edges bounded vertex inside]
  simp [List.map_map, Function.comp_def]

theorem row_seed_independent (n : Nat) (first second : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    row n first target edges vertex = row n second target edges vertex :=
  (row_exact n first target edges bounded vertex inside).trans (row_exact n second target edges bounded vertex inside).symm

end PetaProof.CsrPayloadArray
