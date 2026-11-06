import PetaProof.SccCycleArrayCore

/-!
成分番号をArray UInt32へ格納する。最大値は未割当専用で、有効番号とは区別する。
配列外の既定値は定義の全域化用であり、有効な頂点の読出しは必ず配列内と証明する。
-/
namespace PetaProof.ComponentLabels32

variable {n : Nat}
def unset : UInt32 := TurnEncoding32.none
def decode (label : UInt32) : Option Nat := if label = unset then none else some label.toNat
def get (array : Array UInt32) (vertex : Fin n) : UInt32 := array[vertex.val]?.getD unset
def model (array : Array UInt32) : Fin n → Option Nat := fun vertex => decode (get array vertex)
def empty (n : Nat) : Array UInt32 := Array.replicate n unset

theorem decode_unset : decode unset = none := by simp [decode]

theorem decode_id (id : Nat) (bounded : id < unset.toNat) : decode (UInt32.ofNat id) = some id := by
  have small : id < UInt32.size := by change id < 4294967295 at bounded; change id < 4294967296; omega
  have roundtrip := UInt32.toNat_ofNat_of_lt' small
  have different : UInt32.ofNat id ≠ unset := by
    intro same
    have equal := congrArg UInt32.toNat same
    rw [roundtrip] at equal
    omega
  simp only [decode, if_neg different, roundtrip]

theorem decode_none_iff (label : UInt32) : decode label = none ↔ label = unset := by
  by_cases same : label = unset <;> simp [decode, same]

theorem decode_some_iff (label : UInt32) (id : Nat) :
    decode label = some id ↔ label ≠ unset ∧ label.toNat = id := by
  by_cases same : label = unset <;> simp [decode, same]

theorem get_safe (array : Array UInt32) (size : array.size = n) (vertex : Fin n) : vertex.val < array.size := by
  rw [size]
  exact vertex.isLt

theorem empty_model (n : Nat) : model (empty n) = fun _ : Fin n => none := by
  funext vertex
  simp [model, empty, get, Array.getElem?_replicate, vertex.isLt, decode]

def write (array : Array UInt32) (vertex : Fin n) (id : Nat) : Array UInt32 :=
  array.setIfInBounds vertex.val (UInt32.ofNat id)

theorem write_size (array : Array UInt32) (vertex : Fin n) (id : Nat) : (write array vertex id).size = array.size := by
  simp [write]

theorem write_checked (array : Array UInt32) (size : array.size = n) (vertex : Fin n) (id : Nat) :
    write array vertex id = array.set vertex.val (UInt32.ofNat id) (get_safe array size vertex) := by
  exact dif_pos (get_safe array size vertex)

theorem model_write (array : Array UInt32) (size : array.size = n) (vertex : Fin n) (id : Nat)
    (bounded : id < unset.toNat) :
    model (write array vertex id) = fun other => if other = vertex then some id else model array other := by
  funext other
  have inside := get_safe array size vertex
  by_cases same : other = vertex
  · subst other
    simp [model, get, write, Array.getElem?_setIfInBounds, inside, decode_id id bounded]
  · have different : vertex.val ≠ other.val := by
      intro equal
      exact same (Fin.ext equal.symm)
    simp [model, get, write, Array.getElem?_setIfInBounds, inside, different, same]

theorem guard_exact (array : Array UInt32) (vertex : Fin n) :
    get array vertex = unset ↔ model array vertex = none := (decode_none_iff (get array vertex)).symm

end PetaProof.ComponentLabels32
