import PetaProof.ReverseDfsLabels

/-!
第二DFSの外側の根走査と連番割当。rootsは各探索の開始頂点を記録する証明用の列。
順序が正しいSCCを作ることは仮定せず、番号の範囲と全頂点の割当を証明する。
-/
namespace PetaProof.ComponentNumbering

universe u
variable {V : Type u} [DecidableEq V]

structure State (V : Type u) where
  result : V → Option Nat
  roots : List V

def initial : State V := ⟨fun _ => none, []⟩

def descend (fuel : Nat) (parents : V → List V) (state : State V) (root : V) :
    ReverseDfsStack.State V :=
  ReverseDfsStack.walk state.roots.length parents fuel
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)

/-- 未割当の根のときだけ第二DFSを開始し、成分番号を一つ進める。 -/
def step (fuel : Nat) (parents : V → List V) (state : State V) (root : V) : State V :=
  if state.result root = none then
    ⟨(descend fuel parents state root).result, state.roots ++ [root]⟩
  else state

def pass (fuel : Nat) (parents : V → List V) : List V → State V → State V
  | [], state => state
  | root :: rest, state => pass fuel parents rest (step fuel parents state root)

structure Invariant (state : State V) : Prop where
  unique : state.roots.Nodup
  labeled : ∀ root ∈ state.roots, ∃ id, state.result root = some id
  bounded : ∀ vertex id, state.result vertex = some id → id < state.roots.length
  inhabited : ∀ id, id < state.roots.length → ∃ root ∈ state.roots, state.result root = some id

omit [DecidableEq V] in
theorem initial_invariant : Invariant (initial : State V) := by
  constructor <;> simp [initial]

theorem descend_run (fuel : Nat) (parents : V → List V) (state : State V) (root : V) :
    ReverseDfsStack.Run state.roots.length (ReverseDfsStack.initial state.result)
      (descend fuel parents state root) :=
  (ReverseDfsStack.Run.push (.refl _) root).trans (ReverseDfsStack.walk_run _ _ _ _)

theorem descend_root (fuel : Nat) (parents : V → List V) (state : State V) (root : V)
    (fresh : state.result root = none) :
    (descend fuel parents state root).result root = some state.roots.length := by
  apply (ReverseDfsStack.walk_run _ _ _ _).label_stable root state.roots.length
  simp [ReverseDfsStack.push, ReverseDfsStack.initial, fresh]

theorem descend_invariant (fuel : Nat) (parents : V → List V) (state : State V)
    (valid : Invariant state) (root : V) :
    ReverseDfsStack.Invariant state.roots.length (descend fuel parents state root) := by
  apply (descend_run fuel parents state root).preserves
  apply ReverseDfsStack.initial_invariant
  intro vertex same
  have bad := valid.bounded vertex state.roots.length same
  omega

theorem step_label_stable (fuel : Nat) (parents : V → List V) (state : State V)
    (root vertex : V) (id : Nat) (assigned : state.result vertex = some id) :
    (step fuel parents state root).result vertex = some id := by
  by_cases fresh : state.result root = none
  · simpa only [step, if_pos fresh] using
      (descend_run fuel parents state root).label_stable vertex id assigned
  · simpa [step, fresh] using assigned

theorem step_root_assigned (fuel : Nat) (parents : V → List V) (state : State V) (root : V) :
    ∃ id, (step fuel parents state root).result root = some id := by
  cases found : state.result root with
  | none => exact ⟨state.roots.length, by simpa [step, found] using descend_root fuel parents state root found⟩
  | some id => exact ⟨id, by simp [step, found]⟩

theorem step_preserves (fuel : Nat) (parents : V → List V) (state : State V)
    (valid : Invariant state) (root : V) : Invariant (step fuel parents state root) := by
  by_cases fresh : state.result root = none
  · have not_root : root ∉ state.roots := by
      intro member
      obtain ⟨id, assigned⟩ := valid.labeled root member
      rw [fresh] at assigned
      cases assigned
    have stable := (descend_run fuel parents state root).label_stable
    have new_root := descend_root fuel parents state root fresh
    rw [step, if_pos fresh]
    refine ⟨nodup_append_fresh _ valid.unique root not_root, ?_, ?_, ?_⟩
    · intro vertex member
      rcases List.mem_append.mp member with old | last
      · obtain ⟨id, assigned⟩ := valid.labeled vertex old
        exact ⟨id, stable vertex id assigned⟩
      · have same : vertex = root := by simpa using last
        subst vertex
        exact ⟨state.roots.length, new_root⟩
    · intro vertex id assigned
      have cases_id := (descend_run fuel parents state root).label_cases vertex
      rcases cases_id with old | current
      · have previous : state.result vertex = some id := old.symm.trans assigned
        have bound := valid.bounded vertex id previous
        simp only [List.length_append, List.length_singleton]
        omega
      · have equal : id = state.roots.length := Option.some.inj (assigned.symm.trans current)
        simp [equal]
    · intro id bound
      change id < (state.roots ++ [root]).length at bound
      simp only [List.length_append, List.length_singleton] at bound
      by_cases old : id < state.roots.length
      · obtain ⟨vertex, member, assigned⟩ := valid.inhabited id old
        exact ⟨vertex, List.mem_append_left _ member, stable vertex id assigned⟩
      · have equal : id = state.roots.length := by omega
        exact ⟨root, by simp, equal ▸ new_root⟩
  · simpa [step, fresh] using valid

theorem pass_preserves (fuel : Nat) (parents : V → List V) (order : List V) (state : State V)
    (valid : Invariant state) : Invariant (pass fuel parents order state) := by
  induction order generalizing state with
  | nil => exact valid
  | cons root rest ih => exact ih _ (step_preserves fuel parents state valid root)

theorem pass_label_stable (fuel : Nat) (parents : V → List V) (order : List V) (state : State V)
    (vertex : V) (id : Nat) (assigned : state.result vertex = some id) :
    (pass fuel parents order state).result vertex = some id := by
  induction order generalizing state with
  | nil => exact assigned
  | cons root rest ih => exact ih _ (step_label_stable fuel parents state root vertex id assigned)

theorem pass_member_assigned (fuel : Nat) (parents : V → List V) (order : List V) (state : State V)
    (vertex : V) (member : vertex ∈ order) :
    ∃ id, (pass fuel parents order state).result vertex = some id := by
  induction order generalizing state with
  | nil => cases member
  | cons root rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst vertex
      obtain ⟨id, assigned⟩ := step_root_assigned fuel parents state root
      exact ⟨id, pass_label_stable fuel parents rest _ root id assigned⟩
    · exact ih _ later

theorem roots_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (state : State V) (valid : Invariant state) :
    state.roots.length ≤ vertices.length := by
  have same : ∀ vertex, vertex ∈ state.roots ↔
      vertex ∈ vertices.filter (fun vertex => decide (vertex ∈ state.roots)) := by
    intro vertex
    simp [covered vertex]
  have perm := ReverseDfsStack.nodup_perm_of_mem _ _ valid.unique (unique.filter _) same
  rw [perm.length_eq]
  exact List.length_filter_le _ _

/-- 第一DFSの逆終了順を入力する箇所。範囲と全割当だけなら任意の網羅列でよい。 -/
def finish (vertices order : List V) (parents : V → List V) : State V :=
  pass vertices.length parents order initial

theorem finish_invariant (vertices order : List V) (parents : V → List V) :
    Invariant (finish vertices order parents) :=
  pass_preserves vertices.length parents order initial initial_invariant

theorem finish_assigned (vertices order : List V) (parents : V → List V)
    (covered : ∀ vertex, vertex ∈ order) (vertex : V) :
    ∃ id, (finish vertices order parents).result vertex = some id :=
  pass_member_assigned vertices.length parents order initial vertex (covered vertex)

theorem finish_id_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V) (parents : V → List V)
    (vertex : V) (id : Nat) (assigned : (finish vertices order parents).result vertex = some id) :
    id < vertices.length := by
  have valid := finish_invariant vertices order parents
  have lower := valid.bounded vertex id assigned
  have upper := roots_bound vertices unique covered _ valid
  omega

/-- 本番のwhileを終えてから次の根へ進むための条件。fuel=Nなら実際に空になる。 -/
theorem descend_drains (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : State V) (valid : Invariant state) (root : V) :
    (descend vertices.length parents state root).pending = [] := by
  apply ReverseDfsStack.walk_drains vertices unique covered state.roots.length parents
    vertices.length (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)
  · apply ReverseDfsStack.push_preserves
    apply ReverseDfsStack.initial_invariant
    intro vertex same
    have bad := valid.bounded vertex state.roots.length same
    omega
  · cases found : state.result root <;>
      simp [ReverseDfsStack.push, ReverseDfsStack.initial, found]

theorem descend_count (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : State V) (valid : Invariant state) (root : V) :
    let result := descend vertices.length parents state root
    result.count = (ReverseDfsStack.members vertices state.roots.length result).length :=
  ReverseDfsStack.drained_count vertices unique covered state.roots.length _
    (descend_invariant vertices.length parents state valid root)
    (descend_drains vertices unique covered parents state valid root)

/-- 未割当はないと証明した後、Optionを通常の成分番号へ戻す。 -/
def component (vertices order : List V) (parents : V → List V) (vertex : V) : Nat :=
  ((finish vertices order parents).result vertex).getD 0

theorem finish_result (vertices order : List V) (parents : V → List V)
    (covered : ∀ vertex, vertex ∈ order) (vertex : V) :
    (finish vertices order parents).result vertex = some (component vertices order parents vertex) := by
  obtain ⟨id, assigned⟩ := finish_assigned vertices order parents covered vertex
  simp [component, assigned]

theorem component_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V)
    (order_covers : ∀ vertex, vertex ∈ order) (parents : V → List V) (vertex : V) :
    component vertices order parents vertex < vertices.length :=
  finish_id_bound vertices unique covered order parents vertex _
    (finish_result vertices order parents order_covers vertex)

theorem cycle_table_lookup (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V)
    (order_covers : ∀ vertex, vertex ∈ order) (parents : V → List V)
    (selfLoop : V → Bool) (vertex : V) :
    (ComponentCycleFlags.table vertices (component vertices order parents) selfLoop)[component vertices order parents vertex]? =
    some (ComponentCycleFlags.flag vertices (component vertices order parents) selfLoop
      (component vertices order parents vertex)) :=
  ComponentCycleFlags.table_lookup vertices _ selfLoop vertex
    (component_bound vertices unique covered order order_covers parents vertex)

/-- None=uint32最大値と有効な成分番号は衝突しない。固定幅の全演算の証明ではない。 -/
theorem component_uint32 (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V)
    (order_covers : ∀ vertex, vertex ∈ order) (parents : V → List V)
    (bounded : vertices.length ≤ 4294967295) (vertex : V) :
    let id := component vertices order parents vertex
    (UInt32.ofNat id).toNat = id ∧ UInt32.ofNat id ≠ UInt32.ofNat 4294967295 := by
  have range := component_bound vertices unique covered order order_covers parents vertex
  have roundtrip : (UInt32.ofNat (component vertices order parents vertex)).toNat =
      component vertices order parents vertex := by
    apply UInt32.toNat_ofNat_of_lt'
    change component vertices order parents vertex < 4294967296
    omega
  refine ⟨roundtrip, ?_⟩
  intro same
  have equal := congrArg UInt32.toNat same
  have sentinel : (UInt32.ofNat 4294967295).toNat = 4294967295 := by decide
  rw [roundtrip, sentinel] at equal
  omega

/-- 成分番号の値域は実走査から導く。SCCの二条件は別の証明義務として明示する。 -/
theorem extracted_core_correct {R : V → V → Prop}
    (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (order : List V) (order_covers : ∀ vertex, vertex ∈ order) (parents : V → List V)
    (ordered : ∀ a b, R a b → component vertices order parents a ≤ component vertices order parents b)
    (connected : ∀ a b, component vertices order parents a = component vertices order parents b →
      Nonempty (Walk R a b))
    (selfLoop : V → Bool) (self_correct : ∀ vertex, selfLoop vertex = true ↔ R vertex vertex)
    (vertex : V) :
    vertex ∈ CoreEnumeration.core
      (ComponentCycleFlags.keep vertices (component vertices order parents) selfLoop) vertices ↔
    CyclicVertex R vertex := by
  let partition : SccPartition R := ⟨component vertices order parents, ordered, connected⟩
  exact ComponentCycleFlags.extracted_core_iff vertices unique covered partition
    (component_bound vertices unique covered order order_covers parents) selfLoop self_correct vertex

end PetaProof.ComponentNumbering
