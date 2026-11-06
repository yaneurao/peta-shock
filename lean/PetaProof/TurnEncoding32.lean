import PetaProof.MoveRowsScc
import Init.Data.UInt.Lemmas

/-!
二状態番号のUInt32演算とNone番兵を、自然数上の番号化へ接続する。
局面数の条件は本番の n < None/2 に合わせる。確保失敗・size_tは対象外。
-/
namespace PetaProof.TurnEncoding32

open TurnEncoding (State bit)
def none : UInt32 := 4294967295
def Fits (n : Nat) : Prop := n < none.toNat / 2

theorem fits_bound {n : Nat} (fits : Fits n) : 2 * n < 4294967295 := by
  change n < 4294967295 / 2 at fits
  omega

def encode {n : Nat} (state : State n) : UInt32 := UInt32.ofNat (TurnEncoding.encode state).val

theorem encode_toNat {n : Nat} (fits : Fits n) (state : State n) :
    (encode state).toNat = (TurnEncoding.encode state).val := by
  apply UInt32.toNat_ofNat_of_lt'
  have bound := (TurnEncoding.encode state).isLt
  have limit := fits_bound fits
  change (TurnEncoding.encode state).val < 4294967296
  omega

theorem encode_ne_none {n : Nat} (fits : Fits n) (state : State n) : encode state ≠ none := by
  intro same
  have numeric := congrArg UInt32.toNat same
  rw [encode_toNat fits state] at numeric
  have bound := (TurnEncoding.encode state).isLt
  have limit := fits_bound fits
  change (TurnEncoding.encode state).val = 4294967295 at numeric
  omega

theorem size_cast {n : Nat} (fits : Fits n) : (UInt32.ofNat (2 * n)).toNat = 2 * n := by
  apply UInt32.toNat_ofNat_of_lt'
  have limit := fits_bound fits
  change 2 * n < 4294967296
  omega

def decode (n : Nat) (index : UInt32) : Option (State n) :=
  if valid : index.toNat < 2 * n then some (TurnEncoding.decode ⟨index.toNat, valid⟩) else Option.none

theorem decode_encode {n : Nat} (fits : Fits n) (state : State n) : decode n (encode state) = some state := by
  simp only [decode, encode_toNat fits state]
  rw [dif_pos (TurnEncoding.encode state).isLt, TurnEncoding.decode_encode]

theorem decode_none {n : Nat} (fits : Fits n) : decode n none = Option.none := by
  have limit := fits_bound fits
  unfold decode
  rw [dif_neg (by change ¬4294967295 < 2 * n; omega)]

theorem encode_injective {n : Nat} (fits : Fits n) {a b : State n} (same : encode a = encode b) : a = b := by
  have recovered := congrArg (decode n) same
  rw [decode_encode fits, decode_encode fits] at recovered
  exact Option.some.inj recovered

/-- decodeが成功した番号は、同じ状態をencodeすると元の機械整数へ戻る。 -/
theorem encode_decoded {n : Nat} (index : UInt32) (state : State n)
    (found : decode n index = some state) : encode state = index := by
  unfold decode at found
  split at found
  · have same := Option.some.inj found
    subst state
    unfold encode
    rw [TurnEncoding.encode_decode]
    exact UInt32.ofNat_toNat
  · cases found

theorem decode_some_iff {n : Nat} (fits : Fits n) (index : UInt32) (state : State n) :
    decode n index = some state ↔ encode state = index :=
  ⟨encode_decoded index state, fun same => same ▸ decode_encode fits state⟩

/-- 本番と同じUInt32式。下位bitから親/子の反対手番を付ける。 -/
def flipIndex (base index : UInt32) : UInt32 := base * 2 + (1 - (index &&& 1))

theorem mask_toNat (index : UInt32) : (index &&& 1).toNat = index.toNat % 2 := by
  change (index.toBitVec &&& (1 : UInt32).toBitVec).toNat = _
  rw [BitVec.toNat_and]
  change index.toNat &&& 1 = index.toNat % 2
  exact Nat.and_one_is_mod _

theorem base_index {n : Nat} (fits : Fits n) (state : State n) :
    (encode state / 2).toNat = state.1.val := by
  rw [UInt32.toNat_div, encode_toNat fits]
  exact TurnEncoding.quotient state

theorem owner_index {n : Nat} (fits : Fits n) (state : State n) :
    (encode state &&& 1).toNat = bit state.2 := by
  rw [mask_toNat, encode_toNat fits, TurnEncoding.parity]

theorem flipIndex_toNat {n : Nat} (fits : Fits n) (base : UInt32) (inside : base.toNat < n) (index : UInt32) :
    (flipIndex base index).toNat = 2 * base.toNat + (1 - index.toNat % 2) := by
  have remainder : index.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  have mask_le : index &&& 1 ≤ (1 : UInt32) := by
    rw [UInt32.le_iff_toNat_le, mask_toNat]
    change index.toNat % 2 ≤ 1
    omega
  have limit := fits_bound fits
  have product : base.toNat * 2 < 4294967296 := by omega
  have total : base.toNat * 2 + (1 - index.toNat % 2) < 4294967296 := by omega
  simp only [flipIndex, UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_sub_of_le _ _ mask_le, mask_toNat]
  change ((base.toNat * 2 % 4294967296) + (1 - index.toNat % 2)) % 4294967296 = _
  rw [Nat.mod_eq_of_lt product, Nat.mod_eq_of_lt total]
  omega

theorem flipIndex_ne_none {n : Nat} (fits : Fits n) (base : UInt32) (inside : base.toNat < n) (index : UInt32) :
    flipIndex base index ≠ none := by
  intro same
  have numeric := congrArg UInt32.toNat same
  rw [flipIndex_toNat fits base inside index] at numeric
  have limit := fits_bound fits
  change 2 * base.toNat + (1 - index.toNat % 2) = 4294967295 at numeric
  omega

theorem flipIndex_encode {n : Nat} (fits : Fits n) (base : Fin n) (state : State n) :
    flipIndex (UInt32.ofNat base.val) (encode state) = encode (base, !state.2) := by
  have limit := fits_bound fits
  have base_small : base.val < UInt32.size := by have h := base.isLt; change base.val < 4294967296; omega
  have base_value := UInt32.toNat_ofNat_of_lt' base_small
  apply UInt32.toNat.inj
  rw [flipIndex_toNat fits _ (by rw [base_value]; exact base.isLt), base_value, encode_toNat fits,
    encode_toNat fits, TurnEncoding.parity, TurnEncoding.encode_flip]

end PetaProof.TurnEncoding32
