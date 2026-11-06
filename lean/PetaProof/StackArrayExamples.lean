import PetaProof.ComponentStackArray
import PetaProof.SccIndexedExamples

/-! 抽象グラフで、末尾LIFO・再合流・旧ラベル・範囲検査・循環coreを検査する。 -/
namespace PetaProof.StackArrayExamples

open SccIndexedView.Examples (view allow)

def start : ReverseDfsStackArray.State 3 := ReverseDfsStackArray.initial (ComponentLabels32.empty 3)
def first := ReverseDfsStackArray.push 0 start 0
def second := ReverseDfsStackArray.push 0 first 1

theorem stack_order : second.pending = #[0, 1] ∧ (ReverseDfsStackArray.unpack second).pending = [1, 0] := by decide
theorem back_is_next : ReverseDfsStackArray.top second = some 1 := by decide
theorem pop_back : (ReverseDfsStackArray.pop second).pending = #[0] ∧
    (ReverseDfsStackArray.pop second).count = 1 ∧ (ReverseDfsStackArray.pop second).popped = [1] := by decide
theorem marked_before_push : first.result = #[0, 4294967295, 4294967295] ∧ first.pending = #[0] := by decide
theorem duplicate_is_noop : ReverseDfsStackArray.push 0 first 0 = first :=
  ReverseDfsStackArray.push_assigned 0 first 0 (by decide)
theorem reconvergent_parents : (ReverseDfsStackArray.scan 0 [0, 1, 0, 1] start).pending = #[0, 1] := by decide
theorem old_label_preserved : ReverseDfsStackArray.push 1 first 0 = first :=
  ReverseDfsStackArray.push_assigned 1 first 0 (by decide)
theorem empty_pop : ReverseDfsStackArray.pop start = start := rfl
theorem all_decoded : (#[0, 1] : Array UInt32).toList.reverse.map (VertexStack32.decode 3) =
    (VertexStack32.model 3 #[0, 1]).map some := by decide

-- 不正な要素を落とす全域化関数に依存して証明していないことを検査する。
theorem corrupt_stack_is_excluded : ¬ VertexStack32.Valid 3 #[0, 3] := by
  unfold VertexStack32.Valid
  decide
theorem maximum_vertex_word : (VertexStack32.encode (⟨4294967295, by decide⟩ : Fin 4294967296)).toNat = 4294967295 := by decide

def vertices := List.finRange 3
def parents := SccIndexedView.parents view vertices allow
def order := ForwardDfs.order vertices vertices (SccIndexedView.outgoing view allow)
def finished := ComponentStackArray.finish parents order
def report := ReverseDfsStackArray.explore 1 #[4294967295, 4294967295, 0] parents 0
def flags := (SccCycleArray.finish view vertices order allow).flags

theorem complete_labels : finished.result = #[1, 1, 0] := by decide
theorem root_order : finished.roots = [2, 0] := by decide
theorem previous_component_kept : report.result = #[1, 1, 0] := by decide
theorem drained_array : report.pending = #[] ∧ report.count = 2 := by decide
theorem no_duplicate_pop : report.popped = [0, 1] := by decide
theorem repeated_roots : (ComponentStackArray.finish parents [2, 2, 0, 1, 0]).result = #[1, 1, 0] := by decide
theorem all_core : ComponentResultArray.extract finished flags = [0, 1, 2] := by decide

theorem actual_scc (a b : Fin 3) : ComponentResultArray.component finished a = ComponentResultArray.component finished b ↔
    ForwardDfs.Mutual (SccIndexedView.outgoing view allow) a b :=
  ComponentStackArray.computed_component_iff (by decide) _ parents
    (SccIndexedView.parents_transpose view vertices (CoreEnumeration.finRange_covers 3) allow) a b

theorem actual_core (vertex : Fin 3) : vertex ∈ ComponentResultArray.extract finished flags ↔
    CyclicVertex (SccIndexedView.relation view allow) vertex :=
  ComponentStackArray.extract_correct (by decide) view allow vertex

theorem empty_graph : (ComponentStackArray.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).result = #[] := by decide
theorem isolated_vertex : (ComponentStackArray.finish (fun _ : Fin 1 => []) [0]).result = #[0] := by decide

end PetaProof.StackArrayExamples
