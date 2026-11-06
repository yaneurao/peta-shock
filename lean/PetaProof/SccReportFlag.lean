import PetaProof.SccParentCallback
import PetaProof.MoveRowsCsr64

/-!
第二DFSの実count/self_loopから、部分的な成分割当のフラグ仕様を導く。
membersによる全頂点filterは証明用であり、本番で成分ごとに再走査しない。
-/
namespace PetaProof.SccReportFlag

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

def members (vertices : List V) (result : V → Option Nat) (id : Nat) : List V :=
  vertices.filter (fun vertex => result vertex == some id)

omit [DecidableEq V] in
theorem mem_members (vertices : List V) (result : V → Option Nat) (id : Nat) (vertex : V) :
    vertex ∈ members vertices result id ↔ vertex ∈ vertices ∧ result vertex = some id := by
  simp [members]

def flag (vertices : List V) (result : V → Option Nat) (selfLoop : V → Bool) (id : Nat) : Bool :=
  decide (1 < (members vertices result id).length) || (members vertices result id).any selfLoop

def reportFlag (report : SccParentCallback.State V) : Bool := decide (1 < report.1.count) || report.2

omit [DecidableEq V] in
theorem complete_flag (vertices : List V) (result : V → Option Nat) (component : V → Nat)
    (complete : ∀ vertex, result vertex = some (component vertex)) (selfLoop : V → Bool) (id : Nat) :
    flag vertices result selfLoop id = ComponentCycleFlags.flag vertices component selfLoop id := by
  have same : members vertices result id = ComponentCycleFlags.members vertices component id := by
    unfold members ComponentCycleFlags.members
    apply List.filter_congr
    intro vertex _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, complete, Option.some.injEq]
  rw [flag, same]
  rfl

theorem report_exact (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    let report := SccParentCallback.explore view vertices allow state.result state.roots.length root
    reportFlag report = flag vertices report.1.result (SccIndexedView.selfLoop view vertices allow) state.roots.length := by
  let report := SccParentCallback.explore view vertices allow state.result state.roots.length root
  have graph : report.1 = ComponentNumbering.descend vertices.length (SccIndexedView.parents view vertices allow) state root :=
    SccParentCallback.explore_graph view vertices allow state.result state.roots.length root
  have inv : ReverseDfsStack.Invariant state.roots.length report.1 := by
    rw [graph]
    exact ComponentNumbering.descend_invariant _ _ state valid root
  have drained : report.1.pending = [] := by
    rw [graph]
    exact ComponentNumbering.descend_drains vertices unique covered _ state valid root
  have count : report.1.count = (members vertices report.1.result state.roots.length).length :=
    ReverseDfsStack.drained_count vertices unique covered _ _ inv drained
  have loops : report.2 = (members vertices report.1.result state.roots.length).any (SccIndexedView.selfLoop view vertices allow) := by
    rw [SccParentCallback.explore_flag]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨vertex, present, self⟩
      exact ⟨vertex, (mem_members _ _ _ vertex).mpr
        ⟨covered vertex, (ReverseDfsStack.drained_members _ _ inv drained vertex).mpr present⟩, self⟩
    · rintro ⟨vertex, present, self⟩
      exact ⟨vertex, (ReverseDfsStack.drained_members _ _ inv drained vertex).mp
        ((mem_members _ _ _ vertex).mp present).2, self⟩
  change reportFlag report = _
  simp only [reportFlag, flag, count, loops]
  rfl

theorem old_members_stable (view : SccIndexedView.View V E) (vertices : List V) (allow : E → Bool)
    (state : ComponentNumbering.State V) (root : V) (id : Nat) (old : id < state.roots.length) :
    members vertices (SccParentCallback.explore view vertices allow state.result state.roots.length root).1.result id =
      members vertices state.result id := by
  have graph := SccParentCallback.explore_graph view vertices allow state.result state.roots.length root
  have run := ComponentNumbering.descend_run vertices.length (SccIndexedView.parents view vertices allow) state root
  rw [graph]
  unfold members
  apply List.filter_congr
  intro vertex _
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro assigned
    rcases run.label_cases vertex with same | current
    · exact same.symm.trans assigned
    · have impossible := Option.some.inj (current.symm.trans assigned)
      omega
  · exact run.label_stable vertex id

theorem report_count32 (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V)
    (fits : vertices.length < UInt32.size) :
    let count := (SccParentCallback.explore view vertices allow state.result state.roots.length root).1.count
    (UInt32.ofNat count).toNat = count ∧ decide ((1 : UInt32) < UInt32.ofNat count) = decide (1 < count) := by
  let report := SccParentCallback.explore view vertices allow state.result state.roots.length root
  have graph : report.1 = ComponentNumbering.descend vertices.length (SccIndexedView.parents view vertices allow) state root :=
    SccParentCallback.explore_graph view vertices allow state.result state.roots.length root
  have bound : report.1.count ≤ vertices.length := by
    rw [graph]
    exact ReverseDfsStack.drained_count_bound vertices unique covered _ _
      (ComponentNumbering.descend_invariant _ _ state valid root)
      (ComponentNumbering.descend_drains vertices unique covered _ state valid root)
  have exact_count := UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound fits)
  change (UInt32.ofNat report.1.count).toNat = report.1.count ∧
    decide ((1 : UInt32) < UInt32.ofNat report.1.count) = decide (1 < report.1.count)
  refine ⟨exact_count, ?_⟩
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
  change 1 < (UInt32.ofNat report.1.count).toNat ↔ 1 < report.1.count
  rw [exact_count]

end PetaProof.SccReportFlag
