import PetaProof.ComponentStackArray

/-!
第一DFSの訪問表をUInt8配列にする。非零判定をBool表へ対応させる。
範囲外の既定値は全域化用で、長さNの表をFin Nで読むときには使われない。
-/
namespace PetaProof.SeenArray8

variable {n : Nat}

def get (array : Array UInt8) (vertex : Fin n) : UInt8 := array[vertex.val]?.getD 0
def model (array : Array UInt8) : Fin n → Bool := fun vertex => get array vertex != 0
def empty (n : Nat) : Array UInt8 := Array.replicate n 0
def mark (array : Array UInt8) (vertex : Fin n) : Array UInt8 := array.setIfInBounds vertex.val 1

def Binary (array : Array UInt8) : Prop :=
  ∀ index : Nat, index < array.size → array[index]?.getD 0 = 0 ∨ array[index]?.getD 0 = 1

theorem get_safe (array : Array UInt8) (size : array.size = n) (vertex : Fin n) : vertex.val < array.size := by
  rw [size]
  exact vertex.isLt

theorem get_checked (array : Array UInt8) (size : array.size = n) (vertex : Fin n) :
    get array vertex = array[vertex.val]'(get_safe array size vertex) := by
  simp [get, get_safe array size vertex]

theorem empty_size (n : Nat) : (empty n).size = n := by simp [empty]

theorem empty_binary (n : Nat) : Binary (empty n) := by
  intro index inside
  simp only [empty, Array.size_replicate] at inside ⊢
  simp [Array.getElem?_replicate, inside]

theorem empty_model (n : Nat) : model (empty n) = fun _ : Fin n => false := by
  funext vertex
  simp [model, get, empty, Array.getElem?_replicate, vertex.isLt]

theorem mark_size (array : Array UInt8) (vertex : Fin n) : (mark array vertex).size = array.size := by
  simp [mark]

theorem mark_checked (array : Array UInt8) (size : array.size = n) (vertex : Fin n) :
    mark array vertex = array.set vertex.val 1 (get_safe array size vertex) := by
  exact dif_pos (get_safe array size vertex)

theorem mark_binary (array : Array UInt8) (binary : Binary array) (vertex : Fin n) : Binary (mark array vertex) := by
  intro index inside
  rw [mark_size] at inside
  by_cases same : vertex.val = index
  · simp [mark, Array.getElem?_setIfInBounds, same, inside]
  · simpa [mark, Array.getElem?_setIfInBounds, same] using binary index inside

theorem model_mark (array : Array UInt8) (size : array.size = n) (vertex : Fin n) :
    model (mark array vertex) = markSeen (model array) vertex := by
  funext other
  have inside := get_safe array size vertex
  by_cases same : other = vertex
  · subst other
    simp [model, get, mark, markSeen, Array.getElem?_setIfInBounds, inside]
  · have different : vertex.val ≠ other.val := by
      intro equal
      exact same (Fin.ext equal.symm)
    simp [model, get, mark, markSeen, Array.getElem?_setIfInBounds, different, same]

theorem guard_exact (array : Array UInt8) (vertex : Fin n) :
    model array vertex = true ↔ get array vertex ≠ 0 := by
  simp [model]

theorem guard_unvisited (array : Array UInt8) (vertex : Fin n) :
    model array vertex = false ↔ get array vertex = 0 := by
  simp [model]

theorem binary_get (array : Array UInt8) (size : array.size = n) (binary : Binary array) (vertex : Fin n) :
    get array vertex = 0 ∨ get array vertex = 1 := binary vertex.val (get_safe array size vertex)

theorem binary_seen_iff_one (array : Array UInt8) (size : array.size = n) (binary : Binary array) (vertex : Fin n) :
    model array vertex = true ↔ get array vertex = 1 := by
  rcases binary_get array size binary vertex with zero | one
  · simp [model, zero]
  · simp [model, one]

theorem marked_at (array : Array UInt8) (size : array.size = n) (vertex : Fin n) :
    get (mark array vertex) vertex = 1 := by
  simp [get, mark, Array.getElem?_setIfInBounds, get_safe array size vertex]

end PetaProof.SeenArray8
