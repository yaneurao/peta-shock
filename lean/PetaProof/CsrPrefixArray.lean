import PetaProof.CsrCountArray

/-!
offsets[i] += offsets[i-1]をi=1..nの順に同じArrayへ適用する。
境界k以下は累積済み、kより先はまだ元の入次数という不変条件を保つ。
-/
namespace PetaProof.CsrPrefixArray

universe u
variable {E : Type u}

def step (index : Nat) (array : Array Nat) : Array Nat :=
  array.setIfInBounds index (array[index]?.getD 0 + array[index - 1]?.getD 0)

def run : Nat → Nat → Array Nat → Array Nat
  | 0, _, array => array
  | fuel + 1, index, array => run fuel (index + 1) (step index array)

structure Invariant (n : Nat) (counts : Nat → Nat) (boundary : Nat) (array : Array Nat) : Prop where
  size : array.size = n + 1
  completed : ∀ index, index ≤ boundary → array[index]? = some (Csr.offset counts index)
  future : ∀ index, boundary < index → index ≤ n → array[index]? = some (counts (index - 1))

def StepSafe (index : Nat) (array : Array Nat) : Prop :=
  0 < index ∧ index < array.size ∧ index - 1 < array.size

def AllSafe : Nat → Nat → Array Nat → Prop
  | 0, _, _ => True
  | fuel + 1, index, array => StepSafe index array ∧ AllSafe fuel (index + 1) (step index array)

theorem initial_invariant (n : Nat) (counts : Nat → Nat) (array : Array Nat)
    (raw : CsrCountArray.Represents n counts array) : Invariant n counts 0 array := by
  refine ⟨raw.size, ?_, ?_⟩
  · intro index bound
    have same : index = 0 := by omega
    subst index
    exact raw.zero
  · intro index positive bounded
    have found := raw.values (index - 1) (by omega)
    simpa only [show index - 1 + 1 = index by omega] using found

theorem step_safe (n : Nat) (counts : Nat → Nat) (boundary : Nat) (array : Array Nat)
    (inv : Invariant n counts boundary array) (room : boundary < n) : StepSafe (boundary + 1) array := by
  rw [StepSafe, inv.size]
  omega

theorem step_eq_checked (index : Nat) (array : Array Nat) (safe : StepSafe index array) :
    step index array = array.set index (array[index]?.getD 0 + array[index - 1]?.getD 0) safe.2.1 :=
  dif_pos safe.2.1

theorem step_preserves (n : Nat) (counts : Nat → Nat) (boundary : Nat) (array : Array Nat)
    (inv : Invariant n counts boundary array) (room : boundary < n) :
    Invariant n counts (boundary + 1) (step (boundary + 1) array) := by
  have inside : boundary + 1 < array.size := by rw [inv.size]; omega
  have current : array[boundary + 1]? = some (counts boundary) := by
    simpa using inv.future (boundary + 1) (by omega) (by omega)
  have previous := inv.completed boundary (Nat.le_refl boundary)
  constructor
  · simp [step, inv.size]
  · intro index bound
    by_cases same : index = boundary + 1
    · subst index
      simp [step, current, previous, inside, Csr.offset, Nat.add_comm]
    · have old : index ≤ boundary := by omega
      have different : boundary + 1 ≠ index := Ne.symm same
      simp [step, Array.getElem?_setIfInBounds, different, inv.completed index old]
  · intro index later bounded
    have different : boundary + 1 ≠ index := by omega
    simp [step, Array.getElem?_setIfInBounds, different, inv.future index (by omega) bounded]

theorem run_preserves_and_safe (n : Nat) (counts : Nat → Nat) (fuel boundary : Nat) (array : Array Nat)
    (room : boundary + fuel ≤ n) (inv : Invariant n counts boundary array) :
    Invariant n counts (boundary + fuel) (run fuel (boundary + 1) array) ∧ AllSafe fuel (boundary + 1) array := by
  induction fuel generalizing boundary array with
  | zero => simpa [run, AllSafe] using inv
  | succ fuel ih =>
    have step_room : boundary < n := by omega
    have safe := step_safe n counts boundary array inv step_room
    have next := step_preserves n counts boundary array inv step_room
    obtain ⟨after, tail_safe⟩ := ih (boundary + 1) _ (by omega) next
    constructor
    · simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using after
    · exact ⟨safe, tail_safe⟩

def built (n : Nat) (target : E → Nat) (edges : List E) : Array Nat :=
  run n 1 (CsrCountArray.built n target edges)

theorem built_invariant (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    Invariant n (Csr.degrees target edges) n (built n target edges) := by
  have raw := CsrCountArray.built_represents n target edges bounded
  simpa only [Nat.zero_add, built] using
    (run_preserves_and_safe n _ n 0 _ (by omega) (initial_invariant n _ _ raw)).1

theorem built_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) : AllSafe n 1 (CsrCountArray.built n target edges) := by
  have raw := CsrCountArray.built_represents n target edges bounded
  exact (run_preserves_and_safe n _ n 0 _ (by omega) (initial_invariant n _ _ raw)).2

/-- 配列上のカウントとインプレース累積和の出力が、以前の累積和配置と完全に等しい。 -/
theorem built_eq_offsets (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    built n target edges = CsrArray.offsets n (Csr.degrees target edges) := by
  have inv := built_invariant n target edges bounded
  apply Array.ext_getElem?
  intro index
  by_cases inside : index ≤ n
  · rw [inv.completed index inside, CsrArray.offsets_get n _ index inside]
  · have outside : n + 1 ≤ index := by omega
    rw [Array.getElem?_eq_none (by rw [inv.size]; exact outside),
      Array.getElem?_eq_none (by rw [CsrArray.offsets_size]; exact outside)]

end PetaProof.CsrPrefixArray
