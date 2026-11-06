import PetaProof.SccCycleArray
import PetaProof.ReverseDfsCounter32

/-! 実際の根走査が書いたUInt8配列から、頂点ごとの循環判定を導く。 -/
namespace PetaProof.SccCycleArray

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

/-- UInt32のpopカウンターの実行列からも、配列へ書く同じ0/1が得られる。 -/
theorem report_flag32 (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V)
    (fits : vertices.length < UInt32.size) :
    let report := SccParentCallback.explore view vertices allow state.result state.roots.length root
    ∃ counter, ReverseDfsCounter32.Trace state.roots.length (ReverseDfsStack.initial state.result, 0) (report.1, counter) ∧
      byte (decide ((1 : UInt32) < counter) || report.2) = byte (SccReportFlag.reportFlag report) := by
  let report := SccParentCallback.explore view vertices allow state.result state.roots.length root
  have graph : report.1 = ComponentNumbering.descend vertices.length (SccIndexedView.parents view vertices allow) state root :=
    SccParentCallback.explore_graph view vertices allow state.result state.roots.length root
  obtain ⟨counter, trace, same⟩ := ReverseDfsCounter32.descend vertices unique covered fits
    (SccIndexedView.parents view vertices allow) state valid root
  rw [← graph] at trace same
  refine ⟨counter, trace, ?_⟩
  have comparison : decide ((1 : UInt32) < counter) = decide (1 < report.1.count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
    change 1 < counter.toNat ↔ 1 < report.1.count
    rw [same]
  change byte (decide ((1 : UInt32) < counter) || report.2) = byte (SccReportFlag.reportFlag report)
  simp only [comparison, SccReportFlag.reportFlag]

theorem component_exact (view : SccIndexedView.View V E) (vertices order : List V) (allow : E → Bool) :
    component (finish view vertices order allow) =
      ComponentNumbering.component vertices order (SccIndexedView.parents view vertices allow) := by
  funext vertex
  simp only [component, finish_number, ComponentNumbering.component]

/-- 全割当後のidは実際に書いた成分数未満。配列サイズ未満という条件だけに頼らない。 -/
theorem read_written (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V) (order_cover : ∀ vertex, vertex ∈ order)
    (allow : E → Bool) (vertex : V) :
    let state := finish view vertices order allow
    component state vertex < state.number.roots.length ∧
      component state vertex < state.flags.size ∧
      state.flags[component state vertex]? = some (byte (ComponentCycleFlags.flag vertices
        (ComponentNumbering.component vertices order (SccIndexedView.parents view vertices allow))
        (SccIndexedView.selfLoop view vertices allow) (component state vertex))) := by
  let state := finish view vertices order allow
  have inv := finish_invariant view vertices unique covered order allow
  have complete : ∀ v, state.number.result v = some (component state v) := by
    intro v
    change (finish view vertices order allow).number.result v = _
    rw [finish_number, component_exact]
    exact ComponentNumbering.finish_result vertices order _ order_cover v
  have assigned := complete vertex
  have bound := inv.numbering.bounded vertex (component state vertex) assigned
  have roots_bound := ComponentNumbering.roots_bound vertices unique covered state.number inv.numbering
  have slot := inv.written (component state vertex) bound
  have all_full : ∀ v, state.number.result v =
      some (ComponentNumbering.component vertices order (SccIndexedView.parents view vertices allow) v) := by
    intro v
    simpa only [state, component_exact] using complete v
  rw [SccReportFlag.complete_flag vertices state.number.result _ all_full] at slot
  change component state vertex < state.number.roots.length ∧ component state vertex < state.flags.size ∧ _
  exact ⟨bound, by rw [inv.size]; exact Nat.lt_of_lt_of_le bound roots_bound, slot⟩

theorem keep_exact (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (order : List V) (order_cover : ∀ vertex, vertex ∈ order)
    (allow : E → Bool) (vertex : V) :
    keep (finish view vertices order allow) vertex =
      ComponentCycleFlags.keep vertices
        (ComponentNumbering.component vertices order (SccIndexedView.parents view vertices allow))
        (SccIndexedView.selfLoop view vertices allow) vertex := by
  have written := read_written view vertices unique covered order order_cover allow vertex
  have bound := ComponentNumbering.component_bound vertices unique covered order order_cover
    (SccIndexedView.parents view vertices allow) vertex
  rw [keep, written.2.2, Option.getD_some, byte_nonzero, component_exact]
  unfold ComponentCycleFlags.keep
  rw [ComponentCycleFlags.table_lookup vertices _ _ vertex bound]
  rfl

def core (view : SccIndexedView.View V E) (vertices roots : List V) (allow : E → Bool) : List V :=
  CoreEnumeration.core (keep (finish view vertices (ForwardDfs.order vertices roots (SccIndexedView.outgoing view allow)) allow)) vertices

theorem core_exact (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) (allow : E → Bool) :
    core view vertices roots allow = SccIndexedView.core view vertices roots allow := by
  have order_cover := ForwardDfs.order_covers vertices unique covered roots roots_cover (SccIndexedView.outgoing view allow)
  simp only [core, SccIndexedView.core, CoreEnumeration.core, CoreEnumeration.collect_spec, List.nil_append]
  apply List.filter_congr
  intro vertex _
  exact keep_exact view vertices unique covered _ order_cover allow vertex

theorem core_correct (view : SccIndexedView.View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots)
    (allow : E → Bool) (vertex : V) :
    vertex ∈ core view vertices roots allow ↔ CyclicVertex (SccIndexedView.relation view allow) vertex := by
  rw [core_exact view vertices unique covered roots roots_cover allow]
  exact SccIndexedView.core_relation_correct view vertices unique covered roots roots_cover allow vertex

/-- 二状態の機械式グラフへも適用する。訪問状態・番号表自体の有限配列化は未接続。 -/
theorem book_core_correct {n : Nat} (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    state ∈ core (TurnSharedGraph.expanded (IndexedMoveRows.view (MoveRows32.rows book)))
      (TurnEncoding.vertices n) (TurnEncoding.vertices n)
      (MoveRowsScc.allowAt (MoveRows32.rows book) (MoveRows32.allowNat allow)) ↔
        CyclicVertex (MoveRows32.relation book allow) state := by
  have same : MoveRows32.relation book allow = SccIndexedView.relation
      (TurnSharedGraph.expanded (IndexedMoveRows.view (MoveRows32.rows book)))
      (MoveRowsScc.allowAt (MoveRows32.rows book) (MoveRows32.allowNat allow)) := by
    funext a b
    exact propext (MoveRows32.relation_exact fits book valid allow a b)
  rw [same]
  exact core_correct _ _ (TurnEncoding.vertices_unique n) (TurnEncoding.vertices_cover n) _ (TurnEncoding.vertices_cover n) _ state

end PetaProof.SccCycleArray
