import PetaProof.ReverseOrderArray
import PetaProof.ForwardDfsExamples
import PetaProof.SccIndexedExamples

/-! 終了列の保存順と、生配列からの逆順走査を検査する抽象グラフ例。 -/
namespace PetaProof.OrderArrayExamples

open ForwardDfs.Examples (outgoing rawSlots)

def start : ForwardDfsOrderArray.State 4 := ForwardDfsOrderArray.initial 4
def first := ForwardDfsOrderArray.discover outgoing start 0
def done := ForwardDfsOrderArray.finish outgoing (List.finRange 4)

theorem discovery_does_not_append : first.finished = #[] := by decide
theorem first_tick_does_not_append : (ForwardDfsOrderArray.tick outgoing first).finished = #[] := by decide
theorem unfinished_walk : (ForwardDfsOrderArray.walk outgoing 2 first).finished = #[] := by decide
theorem array_finishing_order : done.finished = #[3, 1, 2, 0] := by decide
theorem decoded_order : FinishingArray32.model 4 done.finished = [3, 1, 2, 0] := by decide
theorem reverse_order : VertexStack32.model 4 done.finished = [0, 2, 1, 3] := by decide
theorem complete_length : done.finished.size = 4 := ForwardDfsOrderArray.finish_size (by decide) outgoing _ (CoreEnumeration.finRange_covers 4)
theorem raw_words_unique : done.finished.toList.Nodup := ForwardDfsOrderArray.finish_words_unique (by decide) outgoing _
theorem visited_bytes : done.seen = #[1, 1, 1, 1] := by decide
theorem repeated_roots : (ForwardDfsOrderArray.finish outgoing [0, 0, 1, 2, 3, 0]).finished = done.finished := by decide
theorem leaf_duplicates_isolated : (ForwardDfsOrderArray.finish rawSlots [0, 0, 1, 2, 2]).finished = #[1, 0, 2] := by decide
theorem missing_root_partial : (ForwardDfsOrderArray.finish rawSlots [0]).finished = #[1, 0] := by decide
theorem self_loop_once : (ForwardDfsOrderArray.finish (fun _ : Fin 1 => [some 0]) [0]).finished = #[0] := by decide
theorem zero_vertices : (ForwardDfsOrderArray.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).finished = #[] := by decide

open ForwardDfs.Examples (oneWay oneWayParents)

-- この一方向辺の例は、順方向に根を走査すると誤って二頂点を併合する。
theorem backward_roots_separate :
    (ReverseOrderArray.run #[1, 0] oneWayParents (ComponentResultArray.initial 2)).result = #[0, 1] := by decide
theorem wrong_direction_merges : (ComponentStackArray.finish oneWayParents [1, 0]).result = #[0, 0] := by decide
theorem complete_one_way : (ReverseOrderArray.labels oneWay oneWayParents).result = #[0, 1] := by decide
theorem empty_reverse_loop : (ReverseOrderArray.run #[] oneWayParents (ComponentResultArray.initial 2)).roots = [] := by decide
theorem direct_prefix : (ReverseOrderArray.loop #[1, 0] oneWayParents 1 (ComponentResultArray.initial 2)).result = #[0, 0] := by decide

open SccIndexedView.Examples (view allow)
def parents := SccIndexedView.parents view (List.finRange 3) allow
def report := ForwardDfsOrderArray.finish (SccIndexedView.outgoing view allow) (List.finRange 3)
def result := ReverseOrderArray.labels (SccIndexedView.outgoing view allow) parents
def flags := (SccCycleArray.finish view (List.finRange 3) (VertexStack32.model 3 report.finished) allow).flags

theorem label_array : result.result = #[1, 1, 0] := by decide
theorem component_roots : result.roots = [2, 0] := by decide
theorem all_core : ComponentResultArray.extract result flags = [0, 1, 2] := by decide
theorem actual_scc (a b : Fin 3) : ComponentResultArray.component result a = ComponentResultArray.component result b ↔
    ForwardDfs.Mutual (SccIndexedView.outgoing view allow) a b :=
  ReverseOrderArray.computed_component_iff (by decide) _ parents
    (SccIndexedView.parents_transpose view (List.finRange 3) (CoreEnumeration.finRange_covers 3) allow) a b
theorem actual_core (vertex : Fin 3) : vertex ∈ ComponentResultArray.extract result flags ↔
    CyclicVertex (SccIndexedView.relation view allow) vertex := ReverseOrderArray.core_correct (by decide) view allow vertex

end PetaProof.OrderArrayExamples
