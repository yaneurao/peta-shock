import PetaProof.CsrOffsets

/-!
cursorによるCSR格納。memoryはNat番地の論理メモリであり、ListやC++配列の実装ではない。
有効な各書込の番地範囲・非衝突と、完成した区間の読み出しを証明する。
-/
namespace PetaProof.Csr

universe u
variable {E : Type u}

structure State (E : Type u) where
  cursor : Nat → Nat
  memory : Nat → Option E

def initial (counts : Nat → Nat) : State E := ⟨offset counts, fun _ => none⟩

def put (target : E → Nat) (edge : E) (state : State E) : State E where
  cursor := increment state.cursor (target edge)
  memory := fun address => if address = state.cursor (target edge) then some edge else state.memory address

def fill (target : E → Nat) : List E → State E → State E
  | [], state => state
  | edge :: rest, state => fill target rest (put target edge state)

structure Valid (target : E → Nat) (all done : List E) (state : State E) : Prop where
  cursor : ∀ vertex, state.cursor vertex = offset (degrees target all) vertex + (bucket target done vertex).length
  stored : ∀ vertex index, index < (bucket target done vertex).length →
    state.memory (offset (degrees target all) vertex + index) = (bucket target done vertex)[index]?

theorem initial_valid (target : E → Nat) (all : List E) : Valid target all [] (initial (degrees target all)) := by
  constructor
  · intro vertex; simp [initial, bucket]
  · intro vertex index inside; simp [bucket] at inside

theorem bucket_snoc (target : E → Nat) (done : List E) (edge : E) (vertex : Nat) :
    bucket target (done ++ [edge]) vertex =
      if target edge = vertex then bucket target done vertex ++ [edge] else bucket target done vertex := by
  by_cases same : target edge = vertex <;> simp [bucket, same]

theorem prefix_bound (target : E → Nat) (done rest : List E) (vertex : Nat) :
    (bucket target done vertex).length ≤ degrees target (done ++ rest) vertex := by
  simp [degrees_spec, bucket]

theorem next_room (target : E → Nat) (done rest : List E) (edge : E) :
    (bucket target done (target edge)).length < degrees target (done ++ edge :: rest) (target edge) := by
  simp [degrees_spec, bucket]

/-- 次の辺のcursorは必ずその子の区間内にあり、満杯区間の末尾へは書かない。 -/
theorem next_address (target : E → Nat) (all done rest : List E) (edge : E)
    (split : all = done ++ edge :: rest) (state : State E) (valid : Valid target all done state) :
    offset (degrees target all) (target edge) ≤ state.cursor (target edge) ∧
      state.cursor (target edge) < offset (degrees target all) (target edge + 1) := by
  have room := next_room target done rest edge
  rw [← split] at room
  rw [valid.cursor]
  simp only [offset]
  omega

/-- 同じ子の旧スロットとも、別の子の既存区間とも、次の格納位置は一致しない。 -/
theorem next_not_stored (target : E → Nat) (all done rest : List E) (edge : E)
    (split : all = done ++ edge :: rest) (state : State E) (valid : Valid target all done state)
    (vertex index : Nat) (inside : index < (bucket target done vertex).length) :
    offset (degrees target all) vertex + index ≠ state.cursor (target edge) := by
  rw [valid.cursor]
  by_cases same : vertex = target edge
  · subst vertex
    omega
  · have fit : (bucket target done vertex).length ≤ degrees target all vertex := by
      rw [split]
      exact prefix_bound target done (edge :: rest) vertex
    have room := next_room target done rest edge
    rw [← split] at room
    exact intervals_disjoint _ vertex (target edge) index (bucket target done (target edge)).length same (by omega) room

theorem put_valid (target : E → Nat) (all done rest : List E) (edge : E)
    (split : all = done ++ edge :: rest) (state : State E) (valid : Valid target all done state) :
    Valid target all (done ++ [edge]) (put target edge state) := by
  constructor
  · intro vertex
    rw [bucket_snoc]
    by_cases same : target edge = vertex
    · simp [put, increment, same, valid.cursor, Nat.add_assoc]
    · simp [put, increment, same, Ne.symm same, valid.cursor]
  · intro vertex index inside
    rw [bucket_snoc] at inside ⊢
    by_cases same : target edge = vertex
    · rw [if_pos same] at inside ⊢
      by_cases old : index < (bucket target done vertex).length
      · have different := next_not_stored target all done rest edge split state valid vertex index old
        change (if offset (degrees target all) vertex + index = state.cursor (target edge) then _ else _) = _
        rw [if_neg different, valid.stored vertex index old, List.getElem?_append_left old]
      · have last : index = (bucket target done vertex).length := by simp only [List.length_append, List.length_singleton] at inside; omega
        subst index
        have address : offset (degrees target all) vertex + (bucket target done vertex).length = state.cursor (target edge) := by
          rw [same, valid.cursor]
        change (if offset (degrees target all) vertex + (bucket target done vertex).length = state.cursor (target edge) then _ else _) = _
        rw [if_pos address]
        simp
    · rw [if_neg same] at inside ⊢
      have different := next_not_stored target all done rest edge split state valid vertex index inside
      change (if offset (degrees target all) vertex + index = state.cursor (target edge) then _ else _) = _
      rw [if_neg different]
      exact valid.stored vertex index inside

theorem fill_valid (target : E → Nat) (all done rest : List E) (split : all = done ++ rest)
    (state : State E) (valid : Valid target all done state) :
    Valid target all (done ++ rest) (fill target rest state) := by
  induction rest generalizing done state with
  | nil => simpa [fill] using valid
  | cons edge rest ih =>
    have next := put_valid target all done rest edge split state valid
    have same : all = (done ++ [edge]) ++ rest := by simpa [List.append_assoc] using split
    simpa [fill, List.append_assoc] using ih (done ++ [edge]) same (put target edge state) next

def built (target : E → Nat) (edges : List E) : State E := fill target edges (initial (degrees target edges))

theorem built_valid (target : E → Nat) (edges : List E) : Valid target edges edges (built target edges) := by
  simpa [built] using fill_valid target edges [] edges (by simp) _ (initial_valid target edges)

theorem final_cursor (target : E → Nat) (edges : List E) (vertex : Nat) :
    (built target edges).cursor vertex = offset (degrees target edges) (vertex + 1) := by
  rw [(built_valid target edges).cursor, ← degrees_spec]
  rfl

/-- n頂点用に末尾offset個を確保すれば、次の格納は必ず容量未満である。 -/
theorem next_within_capacity (target : E → Nat) (all done rest : List E) (n : Nat) (edge : E)
    (bounded : ∀ edge ∈ all, target edge < n) (split : all = done ++ edge :: rest)
    (state : State E) (valid : Valid target all done state) : state.cursor (target edge) < all.length := by
  have present : edge ∈ all := by rw [split]; simp
  have bound := bounded edge present
  have address := (next_address target all done rest edge split state valid).2
  have capacity := total_capacity target all n bounded
  have end_bound := offset_mono (degrees target all) (target edge + 1) n (by omega)
  omega

/-- 格納ループの各反復が容量内へ書く、という実行全体の条件。 -/
def WritesWithin (capacity : Nat) (target : E → Nat) : List E → State E → Prop
  | [], _ => True
  | edge :: rest, state => state.cursor (target edge) < capacity ∧ WritesWithin capacity target rest (put target edge state)

theorem fill_within_capacity (target : E → Nat) (all done rest : List E) (n : Nat)
    (bounded : ∀ edge ∈ all, target edge < n) (split : all = done ++ rest)
    (state : State E) (valid : Valid target all done state) : WritesWithin all.length target rest state := by
  induction rest generalizing done state with
  | nil => trivial
  | cons edge rest ih =>
    refine ⟨next_within_capacity target all done rest n edge bounded split state valid, ?_⟩
    have next := put_valid target all done rest edge split state valid
    have same : all = (done ++ [edge]) ++ rest := by simpa [List.append_assoc] using split
    exact ih (done ++ [edge]) same _ next

theorem built_writes_within (target : E → Nat) (edges : List E) (n : Nat)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    WritesWithin edges.length target edges (initial (degrees target edges)) :=
  fill_within_capacity target edges [] edges n bounded (by simp) _ (initial_valid target edges)

theorem fill_outside_unchanged (capacity : Nat) (target : E → Nat) (edges : List E) (state : State E)
    (safe : WritesWithin capacity target edges state) (address : Nat) (outside : capacity ≤ address) :
    (fill target edges state).memory address = state.memory address := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    rw [fill, ih _ safe.2]
    have different : address ≠ state.cursor (target edge) := by have inside := safe.1; omega
    simp [put, different]

/-- 論理メモリでも、確保容量以降へ余分な値を書いていない。 -/
theorem built_outside_empty (target : E → Nat) (edges : List E) (n : Nat)
    (bounded : ∀ edge ∈ edges, target edge < n) (address : Nat) (outside : edges.length ≤ address) :
    (built target edges).memory address = none :=
  fill_outside_unchanged edges.length target edges _ (built_writes_within target edges n bounded) address outside

def readOptions (memory : Nat → Option E) (start count : Nat) : List (Option E) :=
  (List.range count).map (fun index => memory (start + index))

theorem readOptions_exact (target : E → Nat) (edges : List E) (vertex : Nat) :
    readOptions (built target edges).memory (offset (degrees target edges) vertex) (degrees target edges vertex) =
      (bucket target edges vertex).map some := by
  apply List.ext_getElem
  · simp [readOptions, degrees_spec]
  · intro index left right
    have inside : index < (bucket target edges vertex).length := by simpa [readOptions, degrees_spec] using left
    have stored := (built_valid target edges).stored vertex index inside
    simpa [readOptions, List.getElem?_eq_getElem inside] using stored

def row (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  (readOptions (built target edges).memory (offset (degrees target edges) vertex) (degrees target edges vertex)).filterMap id

/-- 次のoffsetとの差で読む半開区間は、入次数を長さにした読出しと等しい。 -/
theorem row_interval (target : E → Nat) (edges : List E) (vertex : Nat) :
    row target edges vertex =
      (readOptions (built target edges).memory (offset (degrees target edges) vertex)
        (offset (degrees target edges) (vertex + 1) - offset (degrees target edges) vertex)).filterMap id := by
  rw [offset_gap]
  rfl

/-- 完成区間に未初期化スロットはなく、順序と重複回数まで論理バケットと一致する。 -/
theorem row_exact (target : E → Nat) (edges : List E) (vertex : Nat) :
    row target edges vertex = bucket target edges vertex := by
  rw [row, readOptions_exact]
  simp [List.filterMap_map, Function.comp_def]

end PetaProof.Csr
