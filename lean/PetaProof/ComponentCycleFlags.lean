import PetaProof.CoreEnumeration
import PetaProof.Scc

namespace PetaProof.ComponentCycleFlags

universe u
variable {V : Type u} [DecidableEq V] {R : V → V → Prop}

def members (vertices : List V) (component : V → Nat) (id : Nat) : List V :=
  vertices.filter (fun vertex => component vertex == id)

omit [DecidableEq V] in
theorem mem_members (vertices : List V) (component : V → Nat) (id : Nat) (vertex : V) :
    vertex ∈ members vertices component id ↔ vertex ∈ vertices ∧ component vertex = id := by
  simp [members]

theorem length_gt_one_iff_other (vertices : List V) (unique : vertices.Nodup) (vertex : V)
    (member : vertex ∈ vertices) : 1 < vertices.length ↔ ∃ other ∈ vertices, other ≠ vertex := by
  cases vertices with
  | nil => cases member
  | cons head rest =>
    have nodup := List.nodup_cons.mp unique
    by_cases same : vertex = head
    · subst vertex
      constructor
      · intro two
        obtain ⟨other, present⟩ := List.exists_mem_of_length_pos (show 0 < rest.length by simpa using two)
        refine ⟨other, by simp [present], ?_⟩
        intro equal
        subst other
        exact nodup.1 present
      · rintro ⟨other, present, different⟩
        have in_rest : other ∈ rest := (List.mem_cons.mp present).resolve_left different
        have positive := List.length_pos_of_mem in_rest
        simp only [List.length_cons]
        omega
    · have in_rest : vertex ∈ rest := (List.mem_cons.mp member).resolve_left same
      have positive := List.length_pos_of_mem in_rest
      constructor
      · intro _; exact ⟨head, by simp, Ne.symm same⟩
      · intro _; simp only [List.length_cons]; omega

/-- C++のcount>1 || self_loopに対応する成分フラグ。自己ループ判定は各頂点で与える。 -/
def flag (vertices : List V) (component : V → Nat) (selfLoop : V → Bool) (id : Nat) : Bool :=
  decide (1 < (members vertices component id).length) || (members vertices component id).any selfLoop

/-- 正しいSCC分割と一意な頂点列から、成分サイズと自己ループのフラグの意味を導く。 -/
theorem flag_iff_cyclic (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (partition : SccPartition R) (selfLoop : V → Bool) (self_correct : ∀ vertex, selfLoop vertex = true ↔ R vertex vertex)
    (vertex : V) : flag vertices partition.component selfLoop (partition.component vertex) = true ↔ CyclicVertex R vertex := by
  have self_member : vertex ∈ members vertices partition.component (partition.component vertex) := by
    simp [mem_members, covered vertex]
  have other_iff : 1 < (members vertices partition.component (partition.component vertex)).length ↔
      ∃ other ∈ members vertices partition.component (partition.component vertex), other ≠ vertex :=
    length_gt_one_iff_other _ (unique.filter _) vertex self_member
  rw [flag, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, other_iff, partition.cyclic_iff vertex]
  constructor
  · rintro (⟨other, present, different⟩ | ⟨other, present, self⟩)
    · exact Or.inr ⟨other, different, ((mem_members _ _ _ other).mp present).2.symm⟩
    · by_cases same : other = vertex
      · subst other; exact Or.inl ((self_correct vertex).mp self)
      · exact Or.inr ⟨other, same, ((mem_members _ _ _ other).mp present).2.symm⟩
  · rintro (self | ⟨other, different, same⟩)
    · exact Or.inr ⟨vertex, self_member, (self_correct vertex).mpr self⟩
    · exact Or.inl ⟨other, (mem_members _ _ _ other).mpr ⟨covered other, same.symm⟩, different⟩

def table (vertices : List V) (component : V → Nat) (selfLoop : V → Bool) : List Bool :=
  (List.range vertices.length).map (flag vertices component selfLoop)

def keep (vertices : List V) (component : V → Nat) (selfLoop : V → Bool) (vertex : V) : Bool :=
  (table vertices component selfLoop)[component vertex]?.getD false

omit [DecidableEq V] in
theorem table_lookup (vertices : List V) (component : V → Nat) (selfLoop : V → Bool) (vertex : V)
    (bounded : component vertex < vertices.length) :
    (table vertices component selfLoop)[component vertex]? = some (flag vertices component selfLoop (component vertex)) := by
  simp [table, List.getElem?_map, List.getElem?_range, bounded]

theorem keep_iff_cyclic (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (partition : SccPartition R) (ids_bounded : ∀ vertex, partition.component vertex < vertices.length)
    (selfLoop : V → Bool) (self_correct : ∀ vertex, selfLoop vertex = true ↔ R vertex vertex) (vertex : V) :
    keep vertices partition.component selfLoop vertex = true ↔ CyclicVertex R vertex := by
  simp only [keep, table_lookup vertices partition.component selfLoop vertex (ids_bounded vertex), Option.getD_some]
  exact flag_iff_cyclic vertices unique covered partition selfLoop self_correct vertex

theorem extracted_core_iff (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (partition : SccPartition R) (ids_bounded : ∀ vertex, partition.component vertex < vertices.length)
    (selfLoop : V → Bool) (self_correct : ∀ vertex, selfLoop vertex = true ↔ R vertex vertex) (vertex : V) :
    vertex ∈ CoreEnumeration.core (keep vertices partition.component selfLoop) vertices ↔ CyclicVertex R vertex := by
  rw [CoreEnumeration.mem_core]
  simp only [covered vertex, true_and]
  exact keep_iff_cyclic vertices unique covered partition ids_bounded selfLoop self_correct vertex

end PetaProof.ComponentCycleFlags
