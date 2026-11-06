import PetaProof.KosarajuPartition

/-!
基礎局面と手番の対を、2*局面番号+手番の自然数番号へ写す。
Finによる範囲と往復を証明する。uint32への変換はまだ含まない。
-/
namespace PetaProof.TurnEncoding

abbrev State (n : Nat) := Fin n × Bool

def bit (turn : Bool) : Nat := if turn then 1 else 0

def encode {n : Nat} (state : State n) : Fin (2 * n) :=
  ⟨2 * state.1.val + bit state.2, by
    have bound := state.1.isLt
    cases turn : state.2 <;> simp [bit, turn] <;> omega⟩

def decode {n : Nat} (index : Fin (2 * n)) : State n :=
  (⟨index.val / 2, by have bound := index.isLt; omega⟩, decide (index.val % 2 = 1))

theorem decode_encode {n : Nat} (state : State n) : decode (encode state) = state := by
  rcases state with ⟨vertex, turn⟩
  apply Prod.ext
  · apply Fin.ext
    simp only [decode, encode]
    cases turn <;> simp only [bit, Bool.false_eq_true, ↓reduceIte] <;> omega
  · cases turn <;> simp [decode, encode, bit, Nat.add_mod, Nat.mul_mod]

theorem encode_decode {n : Nat} (index : Fin (2 * n)) : encode (decode index) = index := by
  apply Fin.ext
  change 2 * (index.val / 2) + bit (decide (index.val % 2 = 1)) = index.val
  have remainder : index.val % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases odd : index.val % 2 = 1
  · simp only [odd, decide_true, bit, ↓reduceIte]
    omega
  · have even : index.val % 2 = 0 := by omega
    simp only [even, Nat.zero_ne_one, decide_false, bit, Bool.false_eq_true, ↓reduceIte]
    omega

theorem encode_injective {n : Nat} {a b : State n} (same : encode a = encode b) : a = b := by
  have decoded := congrArg decode same
  simpa only [decode_encode] using decoded

theorem decode_injective {n : Nat} {a b : Fin (2 * n)} (same : decode a = decode b) : a = b := by
  have encoded := congrArg encode same
  simpa only [encode_decode] using encoded

theorem quotient {n : Nat} (state : State n) : (encode state).val / 2 = state.1.val := by
  have same := congrArg (fun value : State n => value.1.val) (decode_encode state)
  exact same

theorem parity {n : Nat} (state : State n) : (encode state).val % 2 = bit state.2 := by
  cases turn : state.2 <;> simp [encode, bit, turn, Nat.add_mod, Nat.mul_mod]

theorem decode_bit {n : Nat} (index : Fin (2 * n)) : bit (decode index).2 = index.val % 2 := by
  have same := parity (decode index)
  rw [encode_decode] at same
  exact same.symm

theorem owner_mask {n : Nat} (state : State n) : (encode state).val &&& 1 = bit state.2 := by
  rw [Nat.and_one_is_mod, parity]

theorem bit_flip (turn : Bool) : bit (!turn) = 1 - bit turn := by cases turn <;> decide

theorem encode_flip {n : Nat} (vertex : Fin n) (turn : Bool) :
    (encode (vertex, !turn)).val = 2 * vertex.val + (1 - bit turn) := by
  simp only [encode, bit_flip]

/-- C++の0..2*n-1の根走査を、型付きの局面・手番の対へ戻した順序。 -/
def vertices (n : Nat) : List (State n) := (List.finRange (2 * n)).map decode

theorem vertices_unique (n : Nat) : (vertices n).Nodup := by
  change List.Pairwise (fun a b => a ≠ b) ((List.finRange (2 * n)).map decode)
  rw [List.pairwise_map]
  apply (CoreEnumeration.finRange_unique (2 * n)).imp
  intro a b different same
  exact different (decode_injective same)

theorem vertices_cover (n : Nat) (state : State n) : state ∈ vertices n :=
  List.mem_map.mpr ⟨encode state, CoreEnumeration.finRange_covers (2 * n) _, decode_encode state⟩

theorem vertices_length (n : Nat) : (vertices n).length = 2 * n := by simp [vertices]

theorem vertices_numeric_order (n : Nat) : (vertices n).map encode = List.finRange (2 * n) := by
  simp [vertices, List.map_map, Function.comp_def, encode_decode]

end PetaProof.TurnEncoding
