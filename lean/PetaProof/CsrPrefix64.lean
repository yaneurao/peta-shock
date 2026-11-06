import PetaProof.CsrCount64

/-! 昇順のインプレース累積和をUInt64の加算として実行し、Natの累積和へ接続する。 -/
namespace PetaProof.Csr64

universe u
variable {E : Type u}

def prefixStep (index : Nat) (array : Array UInt64) : Array UInt64 :=
  array.setIfInBounds index (array[index]?.getD 0 + array[index - 1]?.getD 0)

def prefixRun : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, array => array
  | fuel + 1, index, array => prefixRun fuel (index + 1) (prefixStep index array)

def PrefixSafe : Nat → Nat → Array UInt64 → Prop
  | 0, _, _ => True
  | fuel + 1, index, array =>
      (0 < index ∧ index < array.size ∧ index - 1 < array.size) ∧ PrefixSafe fuel (index + 1) (prefixStep index array)

theorem prefixRun_safe (fuel index : Nat) (array : Array UInt64) (positive : 0 < index)
    (room : index + fuel ≤ array.size) : PrefixSafe fuel index array := by
  induction fuel generalizing index array with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨⟨positive, by omega, by omega⟩, ih (index + 1) _ (by omega) ?_⟩
    simpa [prefixStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using room

theorem prefixStep_refines (index : Nat) (array : Array UInt64)
    (room : (unpackArray array)[index]?.getD 0 + (unpackArray array)[index - 1]?.getD 0 < UInt64.size) :
    unpackArray (prefixStep index array) = CsrPrefixArray.step index (unpackArray array) := by
  have small : (array[index]?.getD 0).toNat + (array[index - 1]?.getD 0).toNat < UInt64.size := by
    simpa only [get_toNat] using room
  simp only [prefixStep, CsrPrefixArray.step, unpackArray, Array.map_setIfInBounds]
  rw [add_exact _ _ small, ← get_toNat, ← get_toNat]
  rfl

/-- 次の二項の和は、完成後の次offsetそのもの。二倍の容量上限は要求しない。 -/
theorem prefix_room (n : Nat) (counts : Nat → Nat) (boundary : Nat) (array : Array Nat)
    (inv : CsrPrefixArray.Invariant n counts boundary array) (room : boundary < n)
    (fits : Csr.offset counts n < UInt64.size) :
    array[boundary + 1]?.getD 0 + array[boundary]?.getD 0 < UInt64.size := by
  have current := inv.future (boundary + 1) (by omega) (by omega)
  have previous := inv.completed boundary (Nat.le_refl boundary)
  have upper := Csr.offset_mono counts (boundary + 1) n (by omega)
  simp only [show boundary + 1 - 1 = boundary by omega] at current
  rw [current, previous]
  simp only [Option.getD_some, Csr.offset] at upper ⊢
  omega

theorem prefixRun_refines (n : Nat) (counts : Nat → Nat) (fuel boundary : Nat) (array : Array UInt64)
    (room : boundary + fuel ≤ n) (inv : CsrPrefixArray.Invariant n counts boundary (unpackArray array))
    (fits : Csr.offset counts n < UInt64.size) :
    unpackArray (prefixRun fuel (boundary + 1) array) = CsrPrefixArray.run fuel (boundary + 1) (unpackArray array) := by
  induction fuel generalizing boundary array with
  | zero => rfl
  | succ fuel ih =>
    have step_room : boundary < n := by omega
    have addition := prefix_room n counts boundary _ inv step_room fits
    have same := prefixStep_refines (boundary + 1) array (by simpa using addition)
    have next : CsrPrefixArray.Invariant n counts (boundary + 1) (unpackArray (prefixStep (boundary + 1) array)) := by
      rw [same]
      exact CsrPrefixArray.step_preserves n counts boundary _ inv step_room
    have tail := ih (boundary + 1) _ (by omega) next
    simpa only [prefixRun, CsrPrefixArray.run, Nat.add_assoc, same] using tail

def prefixBuilt (n : Nat) (target : E → Nat) (edges : List E) : Array UInt64 :=
  prefixRun n 1 (countBuilt n target edges)

theorem prefixBuilt_refines (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) :
    unpackArray (prefixBuilt n target edges) = CsrPrefixArray.built n target edges := by
  have initial : CsrPrefixArray.Invariant n (Csr.degrees target edges) 0 (unpackArray (countBuilt n target edges)) := by
    rw [countBuilt_refines n target edges fits]
    exact CsrPrefixArray.initial_invariant n _ _ (CsrCountArray.built_represents n target edges bounded)
  have capacity : Csr.offset (Csr.degrees target edges) n < UInt64.size := by
    rw [Csr.total_capacity target edges n bounded]
    exact fits
  have same := prefixRun_refines n (Csr.degrees target edges) n 0 _ (by omega) initial capacity
  simpa only [Nat.zero_add, prefixBuilt, CsrPrefixArray.built, countBuilt_refines n target edges fits] using same

end PetaProof.Csr64
