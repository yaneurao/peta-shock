import PetaProof.LocalIndex
import Init.Data.SInt.Lemmas
import Init.Data.UInt.Lemmas

namespace PetaProof.LocalIndex

universe u
variable {V : Type u} [DecidableEq V]

def write32 (table : V → Int32) (vertex : V) (value : Int32) : V → Int32 :=
  fun other => if other = vertex then value else table other

def install32 : List V → Nat → (V → Int32) → (V → Int32)
  | [], _, table => table
  | vertex :: rest, offset, table =>
      install32 rest (offset + 1) (write32 table vertex (Int32.ofInt (offset : Int)))

def clear32 : List V → (V → Int32) → (V → Int32)
  | [], table => table
  | vertex :: rest, table => clear32 rest (write32 table vertex (Int32.ofInt (-1)))

def empty32 : V → Int32 := fun _ => Int32.ofInt (-1)
def registered32 (core : List V) : V → Int32 := install32 core 0 empty32

/-- int32へ書く全番号が非負の表現範囲にあれば、登録ループは数学的整数の登録と一致する。 -/
theorem install32_refines (core : List V) (offset : Nat) (bounded : offset + core.length ≤ 2147483648)
    (table32 : V → Int32) (table : V → Int) (same : ∀ vertex, (table32 vertex).toInt = table vertex) :
    ∀ vertex, (install32 core offset table32 vertex).toInt = install core offset table vertex := by
  induction core generalizing offset table32 table with
  | nil => exact same
  | cons head rest ih =>
    have small : (offset : Int) < 2^31 := by simp only [List.length_cons] at bounded; omega
    have nonnegative : -(2^31 : Int) ≤ (offset : Int) := by omega
    have next_same : ∀ vertex,
        (write32 table32 head (Int32.ofInt (offset : Int)) vertex).toInt = write table head (offset : Int) vertex := by
      intro vertex
      by_cases equal : vertex = head
      · simp only [write32, write, if_pos equal]
        exact Int32.toInt_ofInt_of_le nonnegative small
      · simp only [write32, write, if_neg equal]
        exact same vertex
    exact ih (offset + 1) (by simp only [List.length_cons] at bounded; omega) _ _ next_same

theorem registered32_decodes (core : List V) (bounded : core.length ≤ 2147483648) (vertex : V) :
    (registered32 core vertex).toInt = registered core vertex := by
  exact install32_refines core 0 (by omega) empty32 empty
    (fun _ => by change (Int32.ofInt (-1)).toInt = -1; decide) vertex

theorem clear32_refines (core : List V) (table32 : V → Int32) (table : V → Int)
    (same : ∀ vertex, (table32 vertex).toInt = table vertex) :
    ∀ vertex, (clear32 core table32 vertex).toInt = clear core table vertex := by
  induction core generalizing table32 table with
  | nil => exact same
  | cons head rest ih =>
    apply ih
    intro vertex
    by_cases equal : vertex = head
    · simp only [write32, write, if_pos equal]
      decide
    · simp only [write32, write, if_neg equal]
      exact same vertex

theorem clear32_registered (core : List V) (bounded : core.length ≤ 2147483648) (vertex : V) :
    (clear32 core (registered32 core) vertex).toInt = -1 := by
  rw [clear32_refines core (registered32 core) (registered core) (registered32_decodes core bounded), clear_registered]
  rfl

theorem reuse32_after_clear (first second : List V) (first_bound : first.length ≤ 2147483648)
    (second_bound : second.length ≤ 2147483648) (vertex : V) :
    (install32 second 0 (clear32 first (registered32 first)) vertex).toInt = registered second vertex := by
  exact install32_refines second 0 (by omega) _ empty (clear32_registered first first_bound) vertex

omit [DecidableEq V] in
theorem nonnegative32_cast (index : Int32) (nonnegative : 0 ≤ index.toInt) :
    index.toUInt32.toNat = index.toInt.toNat := by
  have signed : (0 : Int32) ≤ index := by
    rw [Int32.le_iff_toInt_le]
    exact nonnegative
  rw [Int32.toNat_toUInt32_of_le signed]
  rfl

omit [DecidableEq V] in
theorem signed32_guard (index : Int32) : ((0 : Int32) ≤ index) ↔ 0 ≤ index.toInt := by
  rw [Int32.le_iff_toInt_le]
  rfl

/-- 符号付き番号をチェックしてからuint32のIndexへ変換して局所フラグを読む。 -/
def localFlag32 (core : List V) (flags : V → Bool) (vertex : V) : Bool :=
  decide (0 ≤ (registered32 core vertex).toInt) &&
    ((core.map flags)[(registered32 core vertex).toUInt32.toNat]?).getD false

theorem localFlag32_iff (core : List V) (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (flags : V → Bool) (vertex : V) :
    localFlag32 core flags vertex = true ↔ vertex ∈ core ∧ flags vertex = true := by
  by_cases member : vertex ∈ core
  · have index_bound := List.idxOf_lt_length member
    have nonnegative : 0 ≤ (registered32 core vertex).toInt := by
      rw [registered32_decodes core bounded, registered_member core unique vertex member]
      omega
    have lookup : (core.map flags)[core.idxOf vertex]? = some (flags vertex) := by
      rw [List.getElem?_map, get_idxOf core vertex member]
      rfl
    simp only [localFlag32, nonnegative32_cast _ nonnegative, registered32_decodes core bounded,
      registered_member core unique vertex member, Int.ofNat_zero_le, decide_true, Bool.true_and,
      Int.toNat_ofNat, lookup, Option.getD_some]
    simp [member]
  · have absent := registered_absent core vertex member
    simp [localFlag32, registered32_decodes core bounded, absent, member]

/-- int32の登録番号が非負なら、uint32変換後も配列範囲内であり、元の局面を指す。 -/
theorem localIndex32_access (core : List V) (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (vertex : V) (nonnegative : 0 ≤ (registered32 core vertex).toInt) :
    let index := (registered32 core vertex).toUInt32.toNat
    index < core.length ∧ core[index]? = some vertex := by
  simp only [nonnegative32_cast _ nonnegative]
  rw [registered32_decodes core bounded] at nonnegative ⊢
  have member := (registered_range core unique vertex).1.mp nonnegative
  have index_bound := List.idxOf_lt_length member
  simp only [registered_member core unique vertex member, Int.toNat_ofNat]
  exact ⟨index_bound, get_idxOf core vertex member⟩

end PetaProof.LocalIndex
