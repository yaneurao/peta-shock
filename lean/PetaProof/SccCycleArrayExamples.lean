import PetaProof.SccCycleArrayCore
import PetaProof.SccIndexedExamples
import PetaProof.MoveRows32Examples

/-! 抽象グラフでの書込・読出しの回帰例。合法な棋譜だとは主張しない。 -/
namespace PetaProof.SccCycleArrayExamples

open SccIndexedView.Examples (view allow)
open SccCycleArray

def vertices := List.finRange 3
def order := ForwardDfs.order vertices vertices (SccIndexedView.outgoing view allow)
def finished := finish view vertices order allow

theorem one_self_loop_report :
    let report := SccParentCallback.explore view vertices allow (fun _ => none) 0 2
    report.1.count = 1 ∧ report.2 = true := by decide
theorem two_vertices_report :
    let report := SccParentCallback.explore view vertices allow (fun _ => none) 0 0
    report.1.count = 2 ∧ report.2 = false := by decide
theorem component_roots : finished.number.roots = [2, 0] := by decide
theorem byte_table : finished.flags = #[1, 1, 0] := by decide
theorem component_numbers : vertices.map (component finished) = [1, 1, 0] := by decide
theorem all_cyclic : core view vertices vertices allow = [0, 1, 2] := by decide

def withoutSelf (edge : Fin 7) : Bool := allow edge && edge != 4
def noSelfOrder := ForwardDfs.order vertices vertices (SccIndexedView.outgoing view withoutSelf)
def noSelfFinished := finish view vertices noSelfOrder withoutSelf

theorem false_written_and_unused_zero : noSelfFinished.flags = #[0, 1, 0] := by decide
theorem singleton_read_is_false : keep noSelfFinished 2 = false := by decide
theorem singleton_slot_was_written : component noSelfFinished 2 < noSelfFinished.number.roots.length := by decide
theorem only_two_cycle_vertices : core view vertices vertices withoutSelf = [0, 1] := by decide

def repeated := finish view vertices [2, 2, 0, 1, 0] allow
theorem repeated_roots_do_not_write_more : repeated.number.roots = [2, 0] ∧ repeated.flags = #[1, 1, 0] := by decide
theorem assigned_root_skips : step view vertices allow finished 0 = finished :=
  skip_assigned view vertices allow finished 0 (by decide)

theorem all_writes_in_bounds : WritesSafe view vertices allow order (initial 3) :=
  finish_writes_safe view vertices (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3) order allow

theorem actual_core_meaning (vertex : Fin 3) :
    vertex ∈ core view vertices vertices allow ↔ CyclicVertex (SccIndexedView.relation view allow) vertex :=
  core_correct view vertices (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    vertices (CoreEnumeration.finRange_covers 3) allow vertex

theorem self_loop_count32 :
    let count := (SccParentCallback.explore view vertices allow (initial 3 : State (Fin 3)).number.result 0 2).1.count
    (UInt32.ofNat count).toNat = count ∧ decide ((1 : UInt32) < UInt32.ofNat count) = decide (1 < count) :=
  SccReportFlag.report_count32 view vertices (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    allow ComponentNumbering.initial ComponentNumbering.initial_invariant 2 (by decide)

theorem counter_trace_to_byte :
    let report := SccParentCallback.explore view vertices allow (fun _ => none) 0 2
    ∃ counter, ReverseDfsCounter32.Trace 0 (ReverseDfsStack.initial (fun _ => none), 0) (report.1, counter) ∧
      byte (decide ((1 : UInt32) < counter) || report.2) = byte (SccReportFlag.reportFlag report) :=
  report_flag32 view vertices (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    allow ComponentNumbering.initial ComponentNumbering.initial_invariant 2 (by decide)

def emptyView : SccIndexedView.View (Fin 0) (Fin 0) where
  outgoing := Fin.elim0
  source := Fin.elim0
  child := Fin.elim0
  at_source := fun edge => Fin.elim0 edge
  source_of_mem := fun vertex => Fin.elim0 vertex

theorem empty_table : (finish emptyView [] [] (fun _ => true)).flags = #[] := by decide
theorem empty_core : core emptyView [] [] (fun _ => true) = [] := by decide

set_option maxRecDepth 8192 in
theorem book_array_core :
    (core (TurnSharedGraph.expanded (IndexedMoveRows.view (MoveRows32.rows MoveRows32Examples.book)))
      (TurnEncoding.vertices 3) (TurnEncoding.vertices 3)
      (MoveRowsScc.allowAt _ (MoveRows32.allowNat MoveRows32Examples.selective))).map
        (fun state => (TurnEncoding32.encode state).toNat) = [2, 3, 4, 5] := by decide

end PetaProof.SccCycleArrayExamples
