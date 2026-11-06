import PetaProof.RawFrameScc32
import PetaProof.FrameCursorExamples

/-! 生フレームを含む第一DFS全体と、その終了配列を使ったSCCの回帰例。 -/
namespace PetaProof.RawFrameExamples32

open FrameCursorExamples (rows counts)
def start : ForwardDfsRaw32.State 4 := ForwardDfsRaw32.initial 4
def first := ForwardDfsRaw32.discover rows start 0
def done := ForwardDfsRaw32.finish rows (List.finRange 4)

theorem raw_initial_frame : first.stack = #[(0, 0)] := by decide
theorem none_slot_increments : (ForwardDfsRaw32.walk rows 1 first).stack = #[(0, 1)] := by decide
theorem parent_increment_before_push : (ForwardDfsRaw32.walk rows 2 first).stack = #[(0, 2), (1, 0)] := by decide
theorem grandchild_frame : (ForwardDfsRaw32.walk rows 3 first).stack = #[(0, 2), (1, 1), (3, 0)] := by decide
theorem back_edge_no_push : (ForwardDfsRaw32.walk rows 4 first).stack = #[(0, 2), (1, 1), (3, 1)] := by decide
theorem retire_top : (ForwardDfsRaw32.walk rows 5 first).stack = #[(0, 2), (1, 1)] ∧
    (ForwardDfsRaw32.walk rows 5 first).finished = #[3] := by decide
theorem duplicate_slot_no_push : (ForwardDfsRaw32.walk rows 7 first).stack = #[(0, 3)] := by decide
theorem second_branch : (ForwardDfsRaw32.walk rows 8 first).stack = #[(0, 4), (2, 0)] := by decide
theorem finished_order : done.finished = #[3, 1, 2, 0] := by decide
theorem seen_bytes : done.seen = #[1, 1, 1, 1] := by decide
theorem stack_empty : done.stack = #[] := ForwardDfsRaw32.finish_stack_empty (by decide) rows counts _
theorem eleven_ticks : (ForwardDfsRaw32.walk rows 11 first).finished = done.finished ∧
    (ForwardDfsRaw32.walk rows 11 first).stack = #[] := by decide
theorem repeated_roots : (ForwardDfsRaw32.finish rows [0, 0, 1, 2, 3, 0]).finished = done.finished := by decide

theorem all_intermediate_valid (fuel : Nat) : ForwardDfsRaw32.Valid rows (ForwardDfsRaw32.walk rows fuel first) :=
  ForwardDfsRaw32.walk_valid (by decide) rows counts fuel first
    (ForwardDfsRaw32.discover_valid (by decide) rows start (ForwardDfsRaw32.initial_valid rows) 0)
theorem all_intermediate_lengths (fuel : Nat) : (ForwardDfsRaw32.walk rows fuel first).stack.size ≤ 4 :=
  ForwardDfsRaw32.seeded_walk_bound (by decide) rows counts fuel start
    (ForwardDfsRaw32.initial_valid rows) (ForwardDfsRaw32.initial_invariant rows) 0
theorem no_frame_dropped (fuel : Nat) :
    (RawFrameStack32.model rows (ForwardDfsRaw32.walk rows fuel first).stack).size =
      (ForwardDfsRaw32.walk rows fuel first).stack.size :=
  RawFrameStack32.model_size rows _ (all_intermediate_valid fuel).stack

theorem invalid_vertex_excluded : ¬ RawFrameStack32.Valid rows #[(4, 0)] := by
  intro valid
  have bound := (valid (4, 0) (by simp)).vertex
  change 4 < 4 at bound
  omega
theorem invalid_cursor_excluded : ¬ RawFrameStack32.Valid rows #[(0, 5)] := by
  intro valid
  exact FrameCursorExamples.overshoot_excluded (valid (0, 5) (by simp))
theorem zero_vertices : (ForwardDfsRaw32.finish (fun vertex : Fin 0 => Fin.elim0 vertex) []).stack = #[] := by decide
theorem isolated_vertex : (ForwardDfsRaw32.finish (fun _ : Fin 1 => #[]) [0]).finished = #[0] := by decide
theorem self_loop_once : (ForwardDfsRaw32.finish (fun _ : Fin 1 => #[some 0]) [0]).finished = #[0] := by decide

theorem labels : (RawFrameScc32.labels rows (RawFrameScc32.parents rows)).result = #[0, 0, 0, 0] := by decide
theorem cyclic_flags : RawFrameScc32.flags rows = #[1, 0, 0, 0] := by decide
theorem cyclic_core : RawFrameScc32.core rows = [0, 1, 2, 3] := by decide
theorem actual_scc (a b : Fin 4) :
    ComponentResultArray.component (RawFrameScc32.labels rows (RawFrameScc32.parents rows)) a =
      ComponentResultArray.component (RawFrameScc32.labels rows (RawFrameScc32.parents rows)) b ↔
        ForwardDfs.Mutual (ForwardDfsRaw32.outgoing rows) a b :=
  RawFrameScc32.computed_component_iff (by decide) rows counts _ (RawFrameScc32.parents_transpose rows) a b
theorem actual_core (vertex : Fin 4) : vertex ∈ RawFrameScc32.core rows ↔
    CyclicVertex (ForwardDfs.Edge (ForwardDfsRaw32.outgoing rows)) vertex :=
  RawFrameScc32.core_correct (by decide) rows counts vertex

end PetaProof.RawFrameExamples32
