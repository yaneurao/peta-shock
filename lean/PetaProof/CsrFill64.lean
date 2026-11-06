import PetaProof.CsrPrefix64

/-! cursorをUInt64にし、書込み前の容量内性から+1の非折返しを導く。 -/
namespace PetaProof.Csr64

universe u
variable {E : Type u}

structure State (E : Type u) where
  cursor : Array UInt64
  memory : Array E

def unpackState (state : State E) : CsrPayloadArray.State E := ⟨unpackArray state.cursor, state.memory⟩

def put (target : E → Nat) (edge : E) (state : State E) : State E :=
  let address := state.cursor[target edge]?.getD 0
  ⟨state.cursor.setIfInBounds (target edge) (address + 1), state.memory.setIfInBounds address.toNat edge⟩

def fill (target : E → Nat) : List E → State E → State E
  | [], state => state
  | edge :: rest, state => fill target rest (put target edge state)

def AllSafe (target : E → Nat) : List E → State E → Prop
  | [], _ => True
  | edge :: rest, state => CsrPayloadArray.StepSafe target edge (unpackState state) ∧ AllSafe target rest (put target edge state)

theorem put_refines (target : E → Nat) (edge : E) (state : State E)
    (safe : CsrPayloadArray.StepSafe target edge (unpackState state)) (fits : state.memory.size < UInt64.size) :
    unpackState (put target edge state) = CsrPayloadArray.put target edge (unpackState state) := by
  have address : (state.cursor[target edge]?.getD 0).toNat < state.memory.size := by
    simpa only [CsrPayloadArray.StepSafe, unpackState, get_toNat] using safe.2
  have small : (state.cursor[target edge]?.getD 0).toNat + (1 : UInt64).toNat < UInt64.size := by
    change (state.cursor[target edge]?.getD 0).toNat + 1 < UInt64.size
    omega
  simp only [unpackState, put, CsrPayloadArray.put, unpackArray, Array.map_setIfInBounds]
  rw [add_exact _ _ small, ← get_toNat]
  rfl

theorem fill_refines_and_safe (target : E → Nat) (edges : List E) (state : State E)
    (safe : CsrPayloadArray.AllSafe target edges (unpackState state)) (fits : state.memory.size < UInt64.size) :
    unpackState (fill target edges state) = CsrPayloadArray.fill target edges (unpackState state) ∧ AllSafe target edges state := by
  induction edges generalizing state with
  | nil => exact ⟨rfl, trivial⟩
  | cons edge rest ih =>
    have same := put_refines target edge state safe.1 fits
    have next_safe : CsrPayloadArray.AllSafe target rest (unpackState (put target edge state)) := by
      rw [same]
      exact safe.2
    have next_fits : (put target edge state).memory.size < UInt64.size := by simpa [put] using fits
    obtain ⟨after, tail_safe⟩ := ih (put target edge state) next_safe next_fits
    constructor
    · simpa only [fill, CsrPayloadArray.fill, same] using after
    · exact ⟨safe.1, tail_safe⟩

end PetaProof.Csr64
