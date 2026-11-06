import PetaProof.FrameArrayScc
import PetaProof.ForwardDfsExamples
import PetaProof.SccIndexedExamples

/-! 配列末尾の子フレームと親の未走査部分を区別する抽象グラフ例。 -/
namespace PetaProof.FrameArrayExamples

open ForwardDfs.Examples (outgoing rawSlots)
def start : ForwardDfsFrameArray.State 4 := ForwardDfsFrameArray.initial 4
def first := ForwardDfsFrameArray.discover outgoing start 0
def afterTick := ForwardDfsFrameArray.tick outgoing first
def done := ForwardDfsFrameArray.finish outgoing (List.finRange 4)

theorem bottom_to_top : afterTick.stack.map ForwardDfs.Frame.vertex = #[0, 1] := by decide
theorem list_model_top_first : (ArrayLifo.model afterTick.stack).map ForwardDfs.Frame.vertex = [1, 0] := by decide
theorem top_child : afterTick.stack.back?.map ForwardDfs.Frame.vertex = some 1 := by decide
theorem parent_todo_kept : (afterTick.stack[0]?).map ForwardDfs.Frame.todo = some [some 2] := by decide
theorem seen_before_child : afterTick.seen = #[1, 1, 0, 0] := by decide
theorem no_early_finish : (ForwardDfsFrameArray.walk outgoing 2 first).finished = #[] := by decide
theorem skip_back_edge : (ForwardDfsFrameArray.walk outgoing 3 first).stack.map ForwardDfs.Frame.vertex = #[0, 1, 3] := by decide
theorem retire_top_only : (ForwardDfsFrameArray.walk outgoing 4 first).stack.map ForwardDfs.Frame.vertex = #[0, 1] ∧
    (ForwardDfsFrameArray.walk outgoing 4 first).finished = #[3] := by decide
theorem final_order : done.finished = #[3, 1, 2, 0] := by decide
theorem final_seen : done.seen = #[1, 1, 1, 1] := by decide
theorem final_empty : done.stack = #[] := ForwardDfsFrameArray.finish_stack_empty (by decide) outgoing _
theorem repeated_roots : (ForwardDfsFrameArray.finish outgoing [0, 0, 1, 2, 3, 0]).finished = done.finished := by decide
theorem duplicate_leaf_isolated : (ForwardDfsFrameArray.finish rawSlots [0, 0, 1, 2, 2]).finished = #[1, 0, 2] := by decide
theorem self_loop_once : (ForwardDfsFrameArray.finish (fun _ : Fin 1 => [some 0, none]) [0]).finished = #[0] := by decide
theorem empty_graph : (ForwardDfsFrameArray.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).finished = #[] := by decide

theorem all_intermediate_lengths (fuel : Nat) : (ForwardDfsFrameArray.walk outgoing fuel first).stack.size ≤ 4 :=
  ForwardDfsFrameArray.seeded_walk_bound (by decide) outgoing fuel start
    (ForwardDfsFrameArray.initial_valid 4) (ForwardDfsFrameArray.initial_invariant 4) 0

-- 末尾以外の書換えや、子を積んでからの末尾更新は異なる処理になる。
theorem replacing_parent_would_change_todo :
    ((afterTick.stack.setIfInBounds 0 ⟨0, []⟩)[0]?).map ForwardDfs.Frame.todo = some [] ∧
      (afterTick.stack[0]?).map ForwardDfs.Frame.todo = some [some 2] := by decide
theorem replacing_after_push_targets_child :
    (ArrayLifo.replaceBack afterTick.stack ⟨1, []⟩).back?.map ForwardDfs.Frame.todo = some [] ∧
      (afterTick.stack[0]?).map ForwardDfs.Frame.todo = some [some 2] := by decide

open SccIndexedView.Examples (view allow)
def parents := SccIndexedView.parents view (List.finRange 3) allow
def report := ForwardDfsFrameArray.finish (SccIndexedView.outgoing view allow) (List.finRange 3)
def result := FrameArrayScc.labels (SccIndexedView.outgoing view allow) parents
def flags := (SccCycleArray.finish view (List.finRange 3) (VertexStack32.model 3 report.finished) allow).flags
theorem label_array : result.result = #[1, 1, 0] := by decide
theorem component_roots : result.roots = [2, 0] := by decide
theorem all_core : ComponentResultArray.extract result flags = [0, 1, 2] := by decide
theorem actual_scc (a b : Fin 3) : ComponentResultArray.component result a = ComponentResultArray.component result b ↔
    ForwardDfs.Mutual (SccIndexedView.outgoing view allow) a b :=
  FrameArrayScc.computed_component_iff (by decide) _ parents
    (SccIndexedView.parents_transpose view (List.finRange 3) (CoreEnumeration.finRange_covers 3) allow) a b
theorem actual_core (vertex : Fin 3) : vertex ∈ ComponentResultArray.extract result flags ↔
    CyclicVertex (SccIndexedView.relation view allow) vertex := FrameArrayScc.core_correct (by decide) view allow vertex

end PetaProof.FrameArrayExamples
