import PetaProof.MoveRowsCsr32

/-!
64-bit環境のsize_t要素をUInt64でモデル化したCSR入次数カウント。
配列添字と反復回数はNatであり、確保失敗やC++言語意味論は対象外。
-/
namespace PetaProof.Csr64

universe u
variable {E : Type u}

def unpackArray (array : Array UInt64) : Array Nat := array.map UInt64.toNat

theorem get_toNat (array : Array UInt64) (index : Nat) :
    (unpackArray array)[index]?.getD 0 = (array[index]?.getD 0).toNat := by
  simp only [unpackArray, Array.getElem?_map]
  cases array[index]? <;> rfl

theorem add_exact (a b : UInt64) (small : a.toNat + b.toNat < UInt64.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt small]

def countStep (target : E → Nat) (edge : E) (array : Array UInt64) : Array UInt64 :=
  let index := target edge + 1
  array.setIfInBounds index (array[index]?.getD 0 + 1)

def countRun (target : E → Nat) : List E → Array UInt64 → Array UInt64
  | [], array => array
  | edge :: rest, array => countRun target rest (countStep target edge array)

def CountSafe (target : E → Nat) : List E → Array UInt64 → Prop
  | [], _ => True
  | edge :: rest, array => target edge + 1 < array.size ∧ CountSafe target rest (countStep target edge array)

theorem countRun_safe (n : Nat) (target : E → Nat) (edges : List E) (array : Array UInt64)
    (bounded : ∀ edge ∈ edges, target edge < n) (size : array.size = n + 1) : CountSafe target edges array := by
  induction edges generalizing array with
  | nil => trivial
  | cons edge rest ih =>
    have child := bounded edge (by simp)
    refine ⟨by rw [size]; omega, ih _ (fun edge member => bounded edge (by simp [member])) ?_⟩
    simpa [countStep] using size

theorem countStep_refines (target : E → Nat) (edge : E) (array : Array UInt64)
    (room : (unpackArray array)[target edge + 1]?.getD 0 + 1 < UInt64.size) :
    unpackArray (countStep target edge array) = CsrCountArray.step target edge (unpackArray array) := by
  have small : (array[target edge + 1]?.getD 0).toNat + (1 : UInt64).toNat < UInt64.size := by
    rw [← get_toNat]
    exact room
  simp only [countStep, CsrCountArray.step, unpackArray, Array.map_setIfInBounds]
  rw [add_exact _ _ small]
  rw [← get_toNat]
  rfl

/-- 残り辺数を予算として残し、一回の加算後にも各要素の上界を維持する。 -/
theorem count_budget (target : E → Nat) (edge : E) (rest : List E) (array : Array Nat) (capacity : Nat)
    (budget : ∀ index : Nat, array[index]?.getD 0 + (edge :: rest).length ≤ capacity) :
    ∀ index : Nat, (CsrCountArray.step target edge array)[index]?.getD 0 + rest.length ≤ capacity := by
  intro index
  have old := budget index
  have at_write := budget (target edge + 1)
  simp only [List.length_cons] at old at_write
  by_cases inside : target edge + 1 < array.size
  · by_cases same : target edge + 1 = index
    · subst index
      simpa [CsrCountArray.step, Array.getElem?_setIfInBounds, inside, Nat.add_assoc, Nat.add_comm] using at_write
    · simp only [CsrCountArray.step, Array.getElem?_setIfInBounds, if_pos inside, if_neg same]
      omega
  · simp only [CsrCountArray.step, Array.setIfInBounds, dif_neg inside]
    omega

theorem countRun_refines (target : E → Nat) (edges : List E) (array : Array UInt64) (capacity : Nat)
    (fits : capacity < UInt64.size)
    (budget : ∀ index : Nat, (unpackArray array)[index]?.getD 0 + edges.length ≤ capacity) :
    unpackArray (countRun target edges array) = CsrCountArray.run target edges (unpackArray array) := by
  induction edges generalizing array with
  | nil => rfl
  | cons edge rest ih =>
    have room : (unpackArray array)[target edge + 1]?.getD 0 + 1 < UInt64.size := by
      have bound := budget (target edge + 1)
      simp only [List.length_cons] at bound
      omega
    have same := countStep_refines target edge array room
    have next : ∀ index : Nat, (unpackArray (countStep target edge array))[index]?.getD 0 + rest.length ≤ capacity := by
      rw [same]
      exact count_budget target edge rest (unpackArray array) capacity budget
    rw [countRun, ih _ next, same]
    rfl

def countBuilt (n : Nat) (target : E → Nat) (edges : List E) : Array UInt64 :=
  countRun target edges (Array.replicate (n + 1) 0)

theorem countBuilt_refines (n : Nat) (target : E → Nat) (edges : List E) (fits : edges.length < UInt64.size) :
    unpackArray (countBuilt n target edges) = CsrCountArray.built n target edges := by
  have budget : ∀ index : Nat, (unpackArray (Array.replicate (n + 1) (0 : UInt64)))[index]?.getD 0 + edges.length ≤ edges.length := by
    intro index
    by_cases inside : index < n + 1 <;> simp [unpackArray, Array.getElem?_replicate, inside]
  have same := countRun_refines target edges (Array.replicate (n + 1) 0) edges.length fits budget
  simpa [countBuilt, CsrCountArray.built, unpackArray] using same

end PetaProof.Csr64
