import PetaProof.CsrPayloadArray

/-!
offsets[child+1]を1増やす、CSR構築の最初の配列カウント。
0番目は0のまま保ち、i+1番目を子iの入次数へ接続する。
-/
namespace PetaProof.CsrCountArray

universe u
variable {E : Type u}

def step (target : E → Nat) (edge : E) (array : Array Nat) : Array Nat :=
  let index := target edge + 1
  array.setIfInBounds index (array[index]?.getD 0 + 1)

def run (target : E → Nat) : List E → Array Nat → Array Nat
  | [], array => array
  | edge :: rest, array => run target rest (step target edge array)

structure Represents (n : Nat) (counts : Nat → Nat) (array : Array Nat) : Prop where
  size : array.size = n + 1
  zero : array[0]? = some 0
  values : ∀ vertex, vertex < n → array[vertex + 1]? = some (counts vertex)

theorem initial_represents (n : Nat) : Represents n (fun _ => 0) (Array.replicate (n + 1) 0) := by
  constructor
  · simp
  · simp
  · intro vertex inside
    simp [Array.getElem?_replicate, show vertex + 1 < n + 1 by omega]

theorem step_eq_checked (target : E → Nat) (edge : E) (array : Array Nat)
    (safe : target edge + 1 < array.size) :
    step target edge array = array.set (target edge + 1) (array[target edge + 1]?.getD 0 + 1) safe :=
  dif_pos safe

theorem step_represents (n : Nat) (target : E → Nat) (edge : E) (counts : Nat → Nat) (array : Array Nat)
    (rep : Represents n counts array) (inside : target edge < n) :
    Represents n (Csr.increment counts (target edge)) (step target edge array) := by
  have safe : target edge + 1 < array.size := by rw [rep.size]; omega
  have found := rep.values (target edge) inside
  constructor
  · simp [step, rep.size]
  · simp [step, Array.getElem?_setIfInBounds, rep.zero]
  · intro vertex bounded
    simp only [step, found, Option.getD_some, Array.getElem?_setIfInBounds, if_pos safe]
    by_cases same : vertex = target edge
    · subst vertex; simp [Csr.increment]
    · have different : target edge + 1 ≠ vertex + 1 := by omega
      simp [Csr.increment, same, different, rep.values vertex bounded]

def AllSafe (target : E → Nat) : List E → Array Nat → Prop
  | [], _ => True
  | edge :: rest, array => target edge + 1 < array.size ∧ AllSafe target rest (step target edge array)

theorem run_represents_and_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (counts : Nat → Nat) (array : Array Nat)
    (rep : Represents n counts array) :
    Represents n (Csr.countPass target edges counts) (run target edges array) ∧ AllSafe target edges array := by
  induction edges generalizing counts array with
  | nil => exact ⟨rep, trivial⟩
  | cons edge rest ih =>
    have child := bounded edge (by simp)
    have safe : target edge + 1 < array.size := by rw [rep.size]; omega
    have next := step_represents n target edge counts array rep child
    have tail : ∀ edge ∈ rest, target edge < n := fun edge member => bounded edge (by simp [member])
    obtain ⟨after, rest_safe⟩ := ih tail _ _ next
    exact ⟨after, safe, rest_safe⟩

def built (n : Nat) (target : E → Nat) (edges : List E) : Array Nat :=
  run target edges (Array.replicate (n + 1) 0)

theorem built_represents (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    Represents n (Csr.degrees target edges) (built n target edges) :=
  (run_represents_and_safe n target edges bounded _ _ (initial_represents n)).1

theorem built_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) : AllSafe target edges (Array.replicate (n + 1) 0) :=
  (run_represents_and_safe n target edges bounded _ _ (initial_represents n)).2

end PetaProof.CsrCountArray
