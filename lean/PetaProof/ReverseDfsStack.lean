import PetaProof.AdmissionQueue
import PetaProof.ComponentCycleFlags

/-!
Kosaraju第二DFSの、割当時ガード付きLIFOスタックと実count。
poppedは証明用の履歴で、本番に履歴配列を追加しない。
辺の走査順・SCC分割の正しさとは独立した会計上の不変条件を扱う。
-/
namespace PetaProof.ReverseDfsStack

universe u
variable {V : Type u} [DecidableEq V]

structure State (V : Type u) where
  result : V → Option Nat
  pending : List V
  popped : List V
  count : Nat

def State.total (state : State V) : List V := state.popped ++ state.pending

open State

def initial (previous : V → Option Nat) : State V := ⟨previous, [], [], 0⟩

/-- resultを先に書いてからpushする。本番のstack.back()をリストの先頭で表す。 -/
def push (id : Nat) (state : State V) (vertex : V) : State V :=
  match state.result vertex with
  | some _ => state
  | none => { state with
      result := fun other => if other = vertex then some id else state.result other
      pending := vertex :: state.pending }

/-- 空でなければ一度だけcountを増やす。空のpopは何もしない。 -/
def pop (state : State V) : State V :=
  match state.pending with
  | [] => state
  | vertex :: rest => { state with
      pending := rest
      popped := state.popped ++ [vertex]
      count := state.count + 1 }

structure Invariant (id : Nat) (state : State V) : Prop where
  unique : state.total.Nodup
  assigned : ∀ vertex, state.result vertex = some id ↔ vertex ∈ state.total
  counted : state.count = state.popped.length

omit [DecidableEq V] in
theorem initial_invariant (previous : V → Option Nat) (id : Nat)
    (unused : ∀ vertex, previous vertex ≠ some id) : Invariant id (initial previous) := by
  refine ⟨by simp [initial, total], ?_, rfl⟩
  intro vertex
  simp [initial, total, unused vertex]

theorem push_preserves (id : Nat) (state : State V) (valid : Invariant id state)
    (vertex : V) : Invariant id (push id state vertex) := by
  cases assigned : state.result vertex with
  | some old => simpa [push, assigned] using valid
  | none =>
    have fresh : vertex ∉ state.total := by
      intro member
      have found := (valid.assigned vertex).mpr member
      simp [assigned] at found
    have unique : (vertex :: state.total).Nodup := List.nodup_cons.mpr ⟨fresh, valid.unique⟩
    refine ⟨?_, ?_, ?_⟩
    · change (push id state vertex).total.Nodup
      simpa only [push, assigned, total] using (List.perm_middle.nodup_iff).mpr unique
    · intro other
      by_cases same : other = vertex
      · subst other
        simp [push, assigned, total]
      · simpa [push, assigned, total, same] using valid.assigned other
    · simpa [push, assigned] using valid.counted

omit [DecidableEq V] in
theorem pop_total (state : State V) : (pop state).total = state.total := by
  cases pending : state.pending <;> simp [pop, pending, total, List.append_assoc]

omit [DecidableEq V] in
theorem pop_preserves (id : Nat) (state : State V) (valid : Invariant id state) :
    Invariant id (pop state) := by
  cases pending : state.pending with
  | nil => simpa [pop, pending] using valid
  | cons vertex rest =>
    refine ⟨?_, ?_, ?_⟩
    · rw [pop_total]; exact valid.unique
    · intro other
      rw [pop_total]
      simpa [pop, pending] using valid.assigned other
    · simpa [pop, pending] using valid.counted

theorem cannot_repush (id : Nat) (state : State V) (valid : Invariant id state)
    (vertex : V) (member : vertex ∈ state.total) : push id state vertex = state := by
  simp [push, (valid.assigned vertex).mpr member]

/-- 重複辺・再合流・自己辺でpushを何度試しても、履歴を含む一意性を保つ。 -/
inductive Run (id : Nat) : State V → State V → Prop
  | refl (state : State V) : Run id state state
  | push {start state : State V} : Run id start state → (vertex : V) →
      Run id start (ReverseDfsStack.push id state vertex)
  | pop {start state : State V} : Run id start state → Run id start (ReverseDfsStack.pop state)

theorem Run.preserves {id : Nat} {start state : State V} (run : Run id start state)
    (valid : Invariant id start) : Invariant id state := by
  induction run with
  | refl => exact valid
  | push _ vertex ih => exact push_preserves _ _ ih vertex
  | pop _ ih => exact pop_preserves _ _ ih

theorem Run.trans {id : Nat} {start middle last : State V}
    (first : Run id start middle) (second : Run id middle last) : Run id start last := by
  induction second with
  | refl => exact first
  | push _ vertex ih => exact .push ih vertex
  | pop _ ih => exact .pop ih

omit [DecidableEq V] in
theorem popped_unique (id : Nat) (state : State V) (valid : Invariant id state) :
    state.popped.Nodup := (List.pairwise_append.mp valid.unique).1

omit [DecidableEq V] in
theorem drained_members (id : Nat) (state : State V) (valid : Invariant id state)
    (empty : state.pending = []) (vertex : V) :
    state.result vertex = some id ↔ vertex ∈ state.popped := by
  simpa [total, empty] using valid.assigned vertex

/-- 全頂点列のfilterは証明用仕様。本番で成分ごとに全頂点を再走査しない。 -/
def members (vertices : List V) (id : Nat) (state : State V) : List V :=
  vertices.filter (fun vertex => state.result vertex == some id)

theorem nodup_count (vertices : List V) (unique : vertices.Nodup) (vertex : V) :
    vertices.count vertex = if vertex ∈ vertices then 1 else 0 := by
  induction vertices with
  | nil => simp
  | cons head rest ih =>
    have pair := List.nodup_cons.mp unique
    by_cases same : vertex = head
    · subst vertex
      simp [List.count_cons, pair.1, List.count_eq_zero_of_not_mem pair.1]
    · simp [List.count_cons, same, Ne.symm same, ih pair.2]

theorem nodup_perm_of_mem (left right : List V) (left_unique : left.Nodup)
    (right_unique : right.Nodup) (same : ∀ vertex, vertex ∈ left ↔ vertex ∈ right) :
    left.Perm right := by
  apply List.perm_iff_count.mpr
  intro vertex
  simp only [nodup_count left left_unique, nodup_count right right_unique, same vertex]

/-- 逆辺callbackを一つずつ実行する。parentsはallow済みの親ID列で、重複を許す。 -/
def scan (id : Nat) : List V → State V → State V
  | [], state => state
  | vertex :: rest, state => scan id rest (push id state vertex)

theorem scan_run (id : Nat) (parents : List V) (state : State V) :
    Run id state (scan id parents state) := by
  induction parents generalizing state with
  | nil => exact .refl state
  | cons vertex rest ih =>
    have first : Run id state (push id state vertex) := .push (.refl state) vertex
    exact first.trans (ih (push id state vertex))

theorem scan_count (id : Nat) (parents : List V) (state : State V) :
    (scan id parents state).count = state.count := by
  induction parents generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [scan, ih]
    cases found : state.result vertex <;> simp [push, found]

theorem total_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (state : State V)
    (valid : Invariant id state) : state.total.length ≤ vertices.length := by
  have same : ∀ vertex, vertex ∈ state.total ↔ vertex ∈ members vertices id state := by
    intro vertex
    simp only [members, List.mem_filter, beq_iff_eq]
    rw [valid.assigned vertex]
    simp [covered vertex]
  have perm := nodup_perm_of_mem _ _ valid.unique (unique.filter _) same
  rw [perm.length_eq]
  exact List.length_filter_le _ _

/-- 一回のpopと全逆辺callback。fuelは証明上の停止上界で、本番の引数ではない。 -/
def visit (id : Nat) (parents : V → List V) (state : State V) : State V :=
  match state.pending with
  | [] => state
  | vertex :: _ => scan id (parents vertex) (pop state)

def walk (id : Nat) (parents : V → List V) : Nat → State V → State V
  | 0, state => state
  | fuel + 1, state => walk id parents fuel (visit id parents state)

theorem visit_preserves (id : Nat) (parents : V → List V) (state : State V)
    (valid : Invariant id state) : Invariant id (visit id parents state) := by
  cases pending : state.pending with
  | nil => simpa [visit, pending] using valid
  | cons vertex rest =>
    simpa only [visit, pending] using (scan_run id (parents vertex) (pop state)).preserves
      (pop_preserves id state valid)

theorem walk_preserves (id : Nat) (parents : V → List V) (fuel : Nat) (state : State V)
    (valid : Invariant id state) : Invariant id (walk id parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih _ (visit_preserves id parents state valid)

theorem walk_empty (id : Nat) (parents : V → List V) (fuel : Nat) (state : State V)
    (empty : state.pending = []) : walk id parents fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [walk, visit, empty] using ih

/-- 高々N回のpopで終了する。再合流する経路数ではなく頂点数で上界を付ける。 -/
theorem walk_drains (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (parents : V → List V)
    (fuel : Nat) (state : State V) (valid : Invariant id state)
    (enough : vertices.length ≤ state.count + fuel) :
    (walk id parents fuel state).pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := total_bound vertices unique covered id state valid
    have counted := valid.counted
    simp only [State.total, List.length_append] at bound
    have empty : state.pending.length = 0 := by omega
    exact List.length_eq_zero_iff.mp empty
  | succ fuel ih =>
    cases pending : state.pending with
    | nil => rw [walk_empty id parents (fuel + 1) state pending]; exact pending
    | cons vertex rest =>
      apply ih _ (visit_preserves id parents state valid)
      have advanced : (visit id parents state).count = state.count + 1 := by
        simp [visit, pending, scan_count, pop]
      rw [advanced]
      omega

theorem drained_count (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (state : State V)
    (valid : Invariant id state) (empty : state.pending = []) :
    state.count = (members vertices id state).length := by
  have same : ∀ vertex, vertex ∈ state.popped ↔ vertex ∈ members vertices id state := by
    intro vertex
    simp only [members, List.mem_filter, beq_iff_eq]
    rw [drained_members id state valid empty]
    simp [covered vertex]
  have perm := nodup_perm_of_mem _ _ (popped_unique id state valid) (unique.filter _) same
  exact valid.counted.trans perm.length_eq

theorem drained_count_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (state : State V)
    (valid : Invariant id state) (empty : state.pending = []) :
    state.count ≤ vertices.length := by
  rw [drained_count vertices unique covered id state valid empty]
  exact List.length_filter_le _ _

/-- 実count>1を、成分内に別の頂点が存在する条件へ接続する。 -/
theorem drained_multiple_iff (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (state : State V)
    (valid : Invariant id state) (empty : state.pending = [])
    (vertex : V) (assigned : state.result vertex = some id) :
    1 < state.count ↔ ∃ other, other ≠ vertex ∧ state.result other = some id := by
  have present : vertex ∈ members vertices id state := by
    simp [members, covered vertex, assigned]
  rw [drained_count vertices unique covered id state valid empty]
  have two : 1 < (members vertices id state).length ↔
      ∃ other ∈ members vertices id state, other ≠ vertex :=
    ComponentCycleFlags.length_gt_one_iff_other _ (unique.filter _) vertex present
  rw [two]
  simp only [members, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨other, ⟨_, found⟩, different⟩
    exact ⟨other, different, found⟩
  · rintro ⟨other, different, found⟩
    exact ⟨other, ⟨covered other, found⟩, different⟩

end PetaProof.ReverseDfsStack
