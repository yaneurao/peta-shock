import PetaProof.SeenArrayScc
import PetaProof.ForwardDfsExamples
import PetaProof.SccIndexedExamples

/-! 有限な抽象グラフによる訪問表の回帰例。特定の合法棋譜の主張ではない。 -/
namespace PetaProof.SeenArrayExamples

open ForwardDfs.Examples (outgoing rawSlots)

def start : ForwardDfsSeenArray.State 4 := ForwardDfsSeenArray.initial 4
def first := ForwardDfsSeenArray.discover outgoing start 0
def afterTick := ForwardDfsSeenArray.tick outgoing first
def done := ForwardDfsSeenArray.finish outgoing (List.finRange 4)

theorem initial_bytes : start.seen = #[0, 0, 0, 0] := by decide
theorem mark_before_frame : first.seen = #[1, 0, 0, 0] ∧ first.stack.map ForwardDfs.Frame.vertex = [0] := by decide
theorem visited_discovery_is_noop : ForwardDfsSeenArray.discover outgoing first 0 = first :=
  ForwardDfsSeenArray.discover_visited outgoing first 0 (by decide)
theorem parent_cursor_kept : afterTick.seen = #[1, 1, 0, 0] ∧
    afterTick.stack.map ForwardDfs.Frame.vertex = [1, 0] ∧
    (afterTick.stack[1]?).map ForwardDfs.Frame.todo = some [some 2] := by decide
theorem completed_bytes : done.seen = #[1, 1, 1, 1] := by decide
theorem finishing_order : done.finished = [3, 1, 2, 0] := by decide
theorem reverse_order : ForwardDfsSeenArray.order outgoing (List.finRange 4) = [0, 2, 1, 3] := by decide
theorem empty_finished_stack : done.stack = [] := ForwardDfsSeenArray.finish_stack_empty outgoing _
theorem length_preserved : done.seen.size = 4 := by decide
theorem completed_root_is_noop : ForwardDfsSeenArray.root outgoing done 0 = done :=
  ForwardDfsSeenArray.root_visited_noop outgoing done empty_finished_stack 0 (by decide)
theorem canonical_bytes : SeenArray8.Binary done.seen := (ForwardDfsSeenArray.finish_valid outgoing _).binary
theorem duplicates_leaf_isolated :
    (ForwardDfsSeenArray.finish rawSlots [0, 0, 1, 2, 2]).seen = #[1, 1, 1] ∧
    (ForwardDfsSeenArray.finish rawSlots [0, 0, 1, 2, 2]).finished = [1, 0, 2] := by decide
theorem partial_roots_not_all_seen : (ForwardDfsSeenArray.finish rawSlots [0]).seen = #[1, 1, 0] := by decide
theorem self_loop_once :
    (ForwardDfsSeenArray.finish (fun _ : Fin 1 => [some 0, none]) [0]).seen = #[1] ∧
    (ForwardDfsSeenArray.finish (fun _ : Fin 1 => [some 0, none]) [0]).finished = [0] := by decide
theorem zero_vertices : (ForwardDfsSeenArray.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).seen = #[] := by decide

-- 非零判定そのものは255でも真だが、通常の実行では0/1以外の値を作らない。
theorem noncanonical_still_nonzero : SeenArray8.model #[255] (0 : Fin 1) = true := by decide
theorem noncanonical_excluded : ¬ SeenArray8.Binary #[255] := by
  unfold SeenArray8.Binary
  decide

theorem wrong_size_excluded : ¬ ForwardDfsSeenArray.Valid (⟨#[], [], []⟩ : ForwardDfsSeenArray.State 1) := by
  intro valid
  have size := valid.size
  change 0 = 1 at size
  omega

open SccIndexedView.Examples (view allow)
def parents := SccIndexedView.parents view (List.finRange 3) allow
def result := SeenArrayScc.labels (SccIndexedView.outgoing view allow) parents

theorem full_label_array : result.result = #[1, 1, 0] := by decide
theorem root_order : result.roots = [2, 0] := by decide
theorem flag_array : SeenArrayScc.flags view allow = #[1, 1, 0] := by decide
theorem full_core : SeenArrayScc.core view allow = [0, 1, 2] := by decide
theorem actual_scc (a b : Fin 3) : ComponentResultArray.component result a = ComponentResultArray.component result b ↔
    ForwardDfs.Mutual (SccIndexedView.outgoing view allow) a b :=
  SeenArrayScc.computed_component_iff (by decide) _ parents
    (SccIndexedView.parents_transpose view (List.finRange 3) (CoreEnumeration.finRange_covers 3) allow) a b
theorem actual_core (vertex : Fin 3) : vertex ∈ SeenArrayScc.core view allow ↔
    CyclicVertex (SccIndexedView.relation view allow) vertex := SeenArrayScc.core_correct (by decide) view allow vertex

end PetaProof.SeenArrayExamples
