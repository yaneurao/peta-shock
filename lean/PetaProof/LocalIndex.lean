import PetaProof.SafetyInitializedRun

namespace PetaProof.LocalIndex

universe u
variable {V : Type u} [DecidableEq V]

def write (table : V → Int) (vertex : V) (value : Int) : V → Int :=
  fun other => if other = vertex then value else table other

/-- coreの列挙順に全体IDから局所番号を登録する。won済みかどうかはここでは見ない。 -/
def install : List V → Nat → (V → Int) → (V → Int)
  | [], _, table => table
  | vertex :: rest, offset, table => install rest (offset + 1) (write table vertex (offset : Int))

def clear : List V → (V → Int) → (V → Int)
  | [], table => table
  | vertex :: rest, table => clear rest (write table vertex (-1))

def empty : V → Int := fun _ => -1
def registered (core : List V) : V → Int := install core 0 empty

theorem install_absent (core : List V) (offset : Nat) (table : V → Int) (vertex : V)
    (absent : vertex ∉ core) : install core offset table vertex = table vertex := by
  induction core generalizing offset table with
  | nil => rfl
  | cons head rest ih =>
    have different : vertex ≠ head := by intro same; subst vertex; exact absent (by simp)
    have tail : vertex ∉ rest := by intro member; exact absent (by simp [member])
    rw [install, ih (offset + 1) _ tail]
    simp [write, different]

/-- 親ID列が一意なら、各登録値はその出現位置に正確に一致する。 -/
theorem install_spec (core : List V) (unique : core.Nodup) (offset : Nat) (table : V → Int) (vertex : V) :
    install core offset table vertex = if vertex ∈ core then ((offset + core.idxOf vertex : Nat) : Int) else table vertex := by
  induction core generalizing offset table with
  | nil => simp [install]
  | cons head rest ih =>
    have nodup := List.nodup_cons.mp unique
    by_cases same : vertex = head
    · subst vertex
      rw [install, install_absent rest (offset + 1) _ head nodup.1]
      simp [write]
    · rw [install, ih nodup.2]
      by_cases member : vertex ∈ rest
      · simp [member, same, Ne.symm same, List.idxOf_cons, cond_eq_if, beq_iff_eq,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [member, same, write]

theorem clear_spec (core : List V) (table : V → Int) (vertex : V) :
    clear core table vertex = if vertex ∈ core then -1 else table vertex := by
  induction core generalizing table with
  | nil => simp [clear]
  | cons head rest ih =>
    rw [clear, ih]
    by_cases member : vertex ∈ rest <;> by_cases same : vertex = head <;> simp [member, same, write]

theorem registered_member (core : List V) (unique : core.Nodup) (vertex : V) (member : vertex ∈ core) :
    registered core vertex = (core.idxOf vertex : Int) := by
  simp [registered, install_spec core unique, member]

theorem registered_absent (core : List V) (vertex : V) (absent : vertex ∉ core) :
    registered core vertex = -1 := install_absent core 0 empty vertex absent

theorem registered_range (core : List V) (unique : core.Nodup) (vertex : V) :
    (0 ≤ registered core vertex ↔ vertex ∈ core) ∧
    (vertex ∈ core → registered core vertex < (core.length : Int)) := by
  by_cases member : vertex ∈ core
  · rw [registered_member core unique vertex member]
    have bound := List.idxOf_lt_length member
    constructor
    · simp [member]
    · intro _; omega
  · rw [registered_absent core vertex member]
    simp [member]

theorem get_idxOf (core : List V) (vertex : V) (member : vertex ∈ core) :
    core[core.idxOf vertex]? = some vertex := by
  induction core with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : vertex = head
    · subst vertex; simp
    · have tail : vertex ∈ rest := (List.mem_cons.mp member).resolve_left same
      simpa [List.idxOf_cons, cond_eq_if, beq_iff_eq, Ne.symm same] using ih tail

theorem idxOf_get_unique (core : List V) (unique : core.Nodup) (index : Nat) (vertex : V)
    (found : core[index]? = some vertex) : core.idxOf vertex = index := by
  induction core generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    have nodup := List.nodup_cons.mp unique
    cases index with
    | zero => have same : head = vertex := Option.some.inj found; subst vertex; simp
    | succ index =>
      have tail : rest[index]? = some vertex := by simpa using found
      have member : vertex ∈ rest := List.mem_of_getElem? tail
      have different : head ≠ vertex := by intro same; subst head; exact nodup.1 member
      simp [List.idxOf_cons, cond_eq_if, beq_iff_eq, different, ih nodup.2 index tail]

/-- 符号チェック通過後の局所番号でcoreを参照すると、元の全体IDを得る。 -/
theorem lookup_inverse (core : List V) (unique : core.Nodup) (vertex : V)
    (nonnegative : 0 ≤ registered core vertex) :
    core[(registered core vertex).toNat]? = some vertex := by
  have member := (registered_range core unique vertex).1.mp nonnegative
  rw [registered_member core unique vertex member]
  simpa using get_idxOf core vertex member

theorem installed_get (core : List V) (unique : core.Nodup) (index : Nat) (vertex : V)
    (found : core[index]? = some vertex) : registered core vertex = (index : Int) := by
  have member := List.mem_of_getElem? found
  rw [registered_member core unique vertex member, idxOf_get_unique core unique index vertex found]

theorem clear_registered (core : List V) : clear core (registered core) = empty := by
  funext vertex
  rw [clear_spec]
  by_cases member : vertex ∈ core
  · simp [member, empty]
  · simp [member, registered_absent core vertex member, empty]

/-- 前のcoreと次のcoreが重なっていても、cleanup後の新規登録は初回と同じ。 -/
theorem reuse_after_clear (first second : List V) :
    install second 0 (clear first (registered first)) = registered second := by
  rw [clear_registered]
  rfl

def localFlag (core : List V) (flags : V → Bool) (vertex : V) : Bool :=
  decide (0 ≤ registered core vertex) && ((core.map flags)[(registered core vertex).toNat]?).getD false

theorem localFlag_iff (core : List V) (unique : core.Nodup) (flags : V → Bool) (vertex : V) :
    localFlag core flags vertex = true ↔ vertex ∈ core ∧ flags vertex = true := by
  by_cases member : vertex ∈ core
  · have nonnegative := (registered_range core unique vertex).1.mpr member
    have lookup := lookup_inverse core unique vertex nonnegative
    simp [localFlag, nonnegative, List.getElem?_map, lookup, member]
  · have negative : ¬ 0 ≤ registered core vertex := by simpa only [(registered_range core unique vertex).1] using member
    simp [localFlag, negative, member]

def writeFlag (flags : V → Bool) (vertex : V) (value : Bool) : V → Bool :=
  fun other => if other = vertex then value else flags other

theorem map_flag_absent (core : List V) (flags : V → Bool) (vertex : V) (value : Bool)
    (absent : vertex ∉ core) : core.map (writeFlag flags vertex value) = core.map flags := by
  induction core with
  | nil => rfl
  | cons head rest ih =>
    have different : head ≠ vertex := by intro same; subst head; exact absent (by simp)
    have tail : vertex ∉ rest := by intro member; exact absent (by simp [member])
    simp [writeFlag, different, ih tail]

/-- aliveの一要素更新は、全体IDのフラグを更新してからcore順に詰め直した配列と一致する。 -/
theorem packed_flag_update (core : List V) (unique : core.Nodup) (flags : V → Bool)
    (vertex : V) (value : Bool) (member : vertex ∈ core) :
    core.map (writeFlag flags vertex value) = (core.map flags).set (core.idxOf vertex) value := by
  induction core with
  | nil => cases member
  | cons head rest ih =>
    have nodup := List.nodup_cons.mp unique
    by_cases same : vertex = head
    · subst vertex
      simp [writeFlag, map_flag_absent rest flags head value nodup.1]
    · have tail : vertex ∈ rest := (List.mem_cons.mp member).resolve_left same
      simp [writeFlag, Ne.symm same, List.idxOf_cons, cond_eq_if, beq_iff_eq, ih nodup.2 tail]

end PetaProof.LocalIndex
