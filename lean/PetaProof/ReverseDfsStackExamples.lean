import PetaProof.ReverseDfsStack

namespace PetaProof.ReverseDfsStack.Examples

def parents (vertex : Fin 4) : List (Fin 4) :=
  match vertex.val with
  | 0 => [1, 1, 2, 2]
  | 1 => [3]
  | 2 => [3]
  | _ => [0]

def start : State (Fin 4) := push 0 (initial (fun _ => none)) 0
def finish : State (Fin 4) := walk 0 parents 4 start

theorem start_valid : Invariant 0 start :=
  push_preserves 0 _ (initial_invariant _ 0 (by simp)) 0

theorem finish_valid : Invariant 0 finish := walk_preserves 0 parents 4 start start_valid

/-- 重複辺と再合流・循環を含めても、実際のLIFO順で四頂点を各一回取り出す。 -/
theorem lifo_and_count : finish.popped = [0, 2, 3, 1] ∧ finish.count = 4 := by decide

theorem assigned_once : finish.popped.Nodup := popped_unique 0 finish finish_valid

theorem drained : finish.pending = [] :=
  walk_drains (List.finRange 4) (CoreEnumeration.finRange_unique 4)
    (CoreEnumeration.finRange_covers 4) 0 parents 4 start start_valid (by decide)

theorem exact_count : finish.count = (members (List.finRange 4) 0 finish).length :=
  drained_count _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    0 finish finish_valid drained

theorem bound : finish.count ≤ 4 := by
  simpa using drained_count_bound _ (CoreEnumeration.finRange_unique 4)
    (CoreEnumeration.finRange_covers 4) 0 finish finish_valid drained

def previous (vertex : Fin 4) : Option Nat := if vertex = 3 then some 7 else none
def withPrevious : State (Fin 4) := walk 8 parents 4 (push 8 (initial previous) 0)

/-- 前の成分に割当済みの頂点は、新しい成分のcountにもスタックにも加わらない。 -/
theorem earlier_component_is_skipped :
    withPrevious.popped = [0, 2, 1] ∧ withPrevious.count = 3 ∧
    withPrevious.result 3 = some 7 := by decide

theorem initial_must_use_fresh_id : ¬Invariant 7 (initial previous) := by
  intro valid
  have bad := (valid.assigned 3).mp (by decide)
  exact List.not_mem_nil bad

theorem empty_stack_is_idle :
    walk 0 parents 4 (initial (fun _ => none)) = initial (fun _ => none) :=
  walk_empty 0 parents 4 _ rfl

theorem no_repush_after_pop : push 0 finish 0 = finish :=
  cannot_repush 0 finish finish_valid (0 : Fin 4) (by decide)

end PetaProof.ReverseDfsStack.Examples
