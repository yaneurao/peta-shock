import PetaProof.ComponentResultArrayCore
import PetaProof.SccIndexedExamples

/-! 範囲内ラベル・番兵・重複push・割当済みラベル保存の抽象グラフによる回帰例。 -/
namespace PetaProof.ResultArrayExamples

open SccIndexedView.Examples (view allow)

theorem largest_label : ComponentLabels32.decode 4294967294 = some 4294967294 := by decide
theorem sentinel_is_unassigned : ComponentLabels32.decode 4294967295 = none := by decide
theorem unchecked_cast_wraps : ComponentLabels32.decode (UInt32.ofNat 4294967296) = some 0 := by decide

def start : ReverseDfsResultArray.State 3 := ReverseDfsResultArray.initial (ComponentLabels32.empty 3)
def first := ReverseDfsResultArray.push 0 start 0

theorem marked_before_next_push : first.result = #[0, 4294967295, 4294967295] ∧ first.pending = [0] := by decide
theorem repeated_push_is_ignored : (ReverseDfsResultArray.push 0 first 0).pending = [0] := by decide
theorem other_component_does_not_overwrite :
    (ReverseDfsResultArray.push 1 first 0).result = #[0, 4294967295, 4294967295] := by decide
theorem reconvergent_parents : (ReverseDfsResultArray.scan 0 [0, 1, 0, 1] start).pending = [1, 0] := by decide
theorem pop_keeps_label : (ReverseDfsResultArray.pop first).result = first.result := by decide

-- 番兵を成分番号に許すと、ラベルが未割当のままになり二重pushされる。
theorem sentinel_must_not_be_an_id :
    (ReverseDfsResultArray.push 4294967295 (ReverseDfsResultArray.push 4294967295 start 0) 0).pending = [0, 0] := by decide

def vertices := List.finRange 3
def parents := SccIndexedView.parents view vertices allow
def order := ForwardDfs.order vertices vertices (SccIndexedView.outgoing view allow)
def finished := ComponentResultArray.finish parents order

theorem full_result_array : finished.result = #[1, 1, 0] := by decide
theorem component_roots : finished.roots = [2, 0] := by decide
theorem result_array_size : finished.result.size = 3 := by decide
theorem preserves_previous_component :
    (ReverseDfsResultArray.explore 1 #[4294967295, 4294967295, 0] parents 0).result = #[1, 1, 0] := by decide
theorem component_count :
    (ReverseDfsResultArray.explore 1 #[4294967295, 4294967295, 0] parents 0).count = 2 := by decide
theorem stack_drained :
    (ReverseDfsResultArray.explore 1 #[4294967295, 4294967295, 0] parents 0).pending = [] := by decide
theorem repeated_roots : (ComponentResultArray.finish parents [2, 2, 0, 1, 0]).result = #[1, 1, 0] := by decide

def flags := (SccCycleArray.finish view vertices order allow).flags
theorem stored_word_reads_flags : vertices.map (ComponentResultArray.keepWithFlags finished flags) = [true, true, true] := by decide
theorem extracted_core : ComponentResultArray.extract finished flags = [0, 1, 2] := by decide

theorem array_components_mean_scc (a b : Fin 3) :
    ComponentResultArray.component finished a = ComponentResultArray.component finished b ↔
      ForwardDfs.Mutual (SccIndexedView.outgoing view allow) a b :=
  ComponentResultArray.computed_component_iff (by decide) _ parents
    (SccIndexedView.parents_transpose view vertices (CoreEnumeration.finRange_covers 3) allow) a b

theorem actual_core_meaning (vertex : Fin 3) :
    vertex ∈ ComponentResultArray.extract finished flags ↔ CyclicVertex (SccIndexedView.relation view allow) vertex :=
  ComponentResultArray.extract_correct (by decide) view allow vertex

theorem zero_vertices : (ComponentResultArray.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).result = #[] := by decide
theorem isolated_vertex : (ComponentResultArray.finish (fun _ : Fin 1 => []) [0]).result = #[0] := by decide

end PetaProof.ResultArrayExamples
