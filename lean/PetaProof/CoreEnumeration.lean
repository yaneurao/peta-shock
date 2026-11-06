import PetaProof.LocalSafetyIndex
import Init.Data.List.FinRange

namespace PetaProof.CoreEnumeration

universe u
variable {V : Type u}

/-- 頂点を順に一度ずつ見て、フラグが真のIDだけを末尾へ積む。 -/
def collect (keep : V → Bool) : List V → List V → List V
  | [], result => result
  | vertex :: rest, result => collect keep rest (if keep vertex then result ++ [vertex] else result)

theorem collect_spec (keep : V → Bool) (vertices result : List V) :
    collect keep vertices result = result ++ vertices.filter keep := by
  induction vertices generalizing result with
  | nil => simp [collect]
  | cons vertex rest ih =>
    cases flag : keep vertex <;> simp [collect, ih, flag, List.append_assoc]

def core (keep : V → Bool) (vertices : List V) : List V := collect keep vertices []

theorem mem_core (keep : V → Bool) (vertices : List V) (vertex : V) :
    vertex ∈ core keep vertices ↔ vertex ∈ vertices ∧ keep vertex = true := by
  simp [core, collect_spec]

theorem core_unique (keep : V → Bool) (vertices : List V) (unique : vertices.Nodup) :
    (core keep vertices).Nodup := by
  simpa only [core, collect_spec, List.nil_append] using unique.filter keep

theorem core_length (keep : V → Bool) (vertices : List V) : (core keep vertices).length ≤ vertices.length := by
  simpa only [core, collect_spec, List.nil_append] using List.length_filter_le keep vertices

theorem finRange_unique (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨vertex, _, same⟩ := List.mem_map.mp member
      have equal := congrArg Fin.val same
      change vertex.val + 1 = 0 at equal
      omega
    · exact ih.map Fin.succ (by intro a b different same; exact different (Fin.succ_inj.mp same))

theorem finRange_covers (n : Nat) (vertex : Fin n) : vertex ∈ List.finRange n := by
  simp [List.finRange, List.mem_ofFn]

/-- 有効な全体IDの0..n-1走査からcoreを構築する。 -/
def finiteCore (n : Nat) (keep : Fin n → Bool) : List (Fin n) := core keep (List.finRange n)

theorem finiteCore_mem (n : Nat) (keep : Fin n → Bool) (vertex : Fin n) :
    vertex ∈ finiteCore n keep ↔ keep vertex = true := by
  simp only [finiteCore, mem_core, finRange_covers, true_and]

theorem finiteCore_unique (n : Nat) (keep : Fin n → Bool) : (finiteCore n keep).Nodup :=
  core_unique keep (List.finRange n) (finRange_unique n)

theorem finiteCore_length (n : Nat) (keep : Fin n → Bool) : (finiteCore n keep).length ≤ n := by
  simpa only [finiteCore, List.length_finRange] using core_length keep (List.finRange n)

/-- 全体頂点数がint32登録の上界内なら、core長の上界は抽出処理から導ける。 -/
theorem finiteCore_local_access (n : Nat) (bounded : n ≤ 2147483648) (keep : Fin n → Bool)
    (vertex : Fin n) (selected : keep vertex = true) :
    let c := finiteCore n keep
    let index := (LocalIndex.registered32 c vertex).toUInt32.toNat
    index < c.length ∧ c[index]? = some vertex := by
  have length_bound : (finiteCore n keep).length ≤ 2147483648 := Nat.le_trans (finiteCore_length n keep) bounded
  have member := (finiteCore_mem n keep vertex).mpr selected
  apply LocalIndex.localIndex32_access _ (finiteCore_unique n keep) length_bound
  rw [LocalIndex.registered32_decodes _ length_bound,
    LocalIndex.registered_member _ (finiteCore_unique n keep) vertex member]
  omega

/-- 有効な全体IDをuint32に書いても、nが範囲内なら元の番号に戻る。 -/
theorem global_uint32_roundtrip (n : Nat) (bounded : n ≤ 4294967296) (vertex : Fin n) :
    (UInt32.ofNat vertex.val).toNat = vertex.val := by
  apply UInt32.toNat_ofNat_of_lt'
  change vertex.val < 4294967296
  omega

end PetaProof.CoreEnumeration
