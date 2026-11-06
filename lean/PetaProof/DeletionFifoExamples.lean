import PetaProof.DeletionFifoRanks
import PetaProof.FiniteDeletionExamples

/-! 三頂点の分岐と再合流を、共有目標と五本の辺で表す実FIFOの回帰例。 -/
namespace PetaProof.DeletionFifoExamples

open HistoryArena HistoryArena.DeletionInput FiniteDeletionExamples

def child (e : Fin 5) : Option (Fin 3) := if e = 0 then some 1 else if e = 1 then some 2 else none
def source (e : Fin 5) : Option (Fin 3) :=
  if e.val < 2 then some 0 else if e = 2 then some 1 else if e = 3 then some 2 else none

def incoming : Option (Fin 3) → List (Fin 5)
  | none => [2, 3, 4]
  | some v => if v = 0 then [] else if v = 1 then [0] else [1]

def outgoing : Option (Fin 3) → List (Fin 5)
  | none => [4]
  | some v => if v = 0 then [0, 1] else if v = 1 then [2] else [3]

def indexed : EscapePropagation.Input (Option (Fin 3)) (Fin 5) where
  child := child
  source := source
  incoming := incoming
  outgoing := outgoing
  incoming_correct := by
    intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide
  incoming_unique := by
    intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide
  outgoing_correct := by
    intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide
  outgoing_unique := by
    intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide
  outgoing_nonempty := by
    intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide
  own := fun vertex => match vertex with | none => true | some v => v != 0

theorem matching : EscapePropagation.ArenaMatch indexed input.reachArena := by
  constructor
  · intro vertex next
    change next ∈ input.reachNext vertex ↔ ∃ edge : Fin 5, edge ∈ indexed.outgoing vertex ∧ indexed.child edge = next
    cases vertex with
    | none =>
      cases next with
      | none => decide
      | some w => revert w; decide
    | some v =>
      cases next with
      | none => revert v; decide
      | some w => revert v w; decide
  · intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide

theorem redirected_edges : input.reachNext (some 1) = [none] ∧ input.reachNext (some 2) = [none] := by decide
theorem four_vertices : (reachVertices (n := 3)).length = 4 := by decide
theorem original_rows_preserved (v : Fin 3) : (input.reachNext (some v)).length = (input.next v).length :=
  input.reachNext_length v
theorem fifo_labels : fifoTable indexed = #[some 2, some 1, some 1] := by decide
theorem fifo_numeric_ranks : fifoRanks (fifoTable indexed) = #[2, 1, 1] := by decide
theorem fifo_success : (input.fifoCheckedCounter indexed matching).isSome = true := by decide
theorem same_success : (input.fifoCheckedCounter indexed matching).isSome = input.checkedCounter.isSome :=
  input.fifoCheckedCounter_agrees indexed matching

theorem same_numeric_rank (v : Fin 3) : rankAt (fifoRanks (fifoTable indexed)) v = rankAt (input.run 3).ranks v :=
  input.fifoRanks_reference indexed matching 3
    (HistoryArena.DeletionInput.empty_at_size ((input.checkedCounter_iff).mp checked_success)) v

theorem shared_goal_not_path_copies : (input.reachNext (some 1)).head? = some none ∧
    (input.reachNext (some 2)).head? = some none := by decide

namespace Safe

def indexed : EscapePropagation.Input (Option (Fin 1)) (Option (Fin 1)) where
  child := id
  source := id
  incoming := fun vertex => [vertex]
  outgoing := fun vertex => [vertex]
  incoming_correct := by intro vertex edge; simp
  incoming_unique := by intro vertex; simp
  outgoing_correct := by intro vertex edge; simp
  outgoing_unique := by intro vertex; simp
  outgoing_nonempty := by intro vertex; simp
  own := fun vertex => match vertex with | none => true | some _ => false

theorem matching : EscapePropagation.ArenaMatch indexed safeInput.reachArena := by
  constructor
  · intro vertex next
    change next ∈ safeInput.reachNext vertex ↔
      ∃ edge : Option (Fin 1), edge ∈ indexed.outgoing vertex ∧ indexed.child edge = next
    cases vertex with
    | none =>
      cases next with
      | none => decide
      | some w => revert w; decide
    | some v =>
      cases next with
      | none => revert v; decide
      | some w => revert v w; decide
  · intro vertex
    cases vertex with
    | none => decide
    | some v => revert v; decide

theorem unresolved : fifoTable indexed = #[none] := by decide
theorem rejected : (safeInput.fifoCheckedCounter indexed matching).isSome = false := by decide
theorem agrees : (safeInput.fifoCheckedCounter indexed matching).isSome = safeInput.checkedCounter.isSome :=
  safeInput.fifoCheckedCounter_agrees indexed matching

end Safe

end PetaProof.DeletionFifoExamples
