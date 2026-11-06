import PetaProof.ForwardDfsForest

namespace PetaProof.ForwardDfs.Examples

def outgoing (vertex : Fin 4) : List (Option (Fin 4)) :=
  match vertex.val with
  | 0 => [some 1, some 2]
  | 1 => [some 3]
  | 2 => [some 3]
  | _ => [some 0]

def done : State (Fin 4) := finish (List.finRange 4) (List.finRange 4) outgoing

theorem finishing_not_discovery_order : done.finished = [3, 1, 2, 0] := by decide

theorem frames_retain_parent_cursor :
    (tick outgoing (discover outgoing initial 0)).stack.map Frame.vertex = [1, 0] ∧
    ((tick outgoing (discover outgoing initial 0)).stack[1]?).map Frame.todo = some [some 2] ∧
    (tick outgoing (discover outgoing initial 0)).finished = [] := by decide

theorem early_fuel_does_not_finish :
    (walk outgoing 2 (discover outgoing initial 0)).stack ≠ [] ∧
    (walk outgoing 2 (discover outgoing initial 0)).finished = [] := by
  constructor
  · intro empty
    have size := congrArg List.length empty
    change 3 = 0 at size
    omega
  · decide

theorem finishing_unique : done.finished.Nodup := finish_unique _ _ outgoing

theorem finishing_is_permutation : done.finished.Perm (List.finRange 4) :=
  finish_perm _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) outgoing

theorem nine_ticks :
    ForestRun (List.finRange 4) outgoing (List.finRange 4) initial 9 done := by
  have run := finish_work (List.finRange 4) (CoreEnumeration.finRange_unique 4)
    (CoreEnumeration.finRange_covers 4) (List.finRange 4) (CoreEnumeration.finRange_covers 4) outgoing
  change ForestRun (List.finRange 4) outgoing (List.finRange 4) initial 9 done at run
  exact run

def rawSlots (vertex : Fin 3) : List (Option (Fin 3)) :=
  match vertex.val with
  | 0 => [none, some 1, some 1, none]
  | 1 => [some 0]
  | _ => []

theorem duplicates_none_and_isolated :
    (finish (List.finRange 3) [0, 0, 1, 2, 2] rawSlots).finished = [1, 0, 2] ∧
    capacity (List.finRange 3) rawSlots = 8 := by decide

theorem missing_roots_miss_isolated :
    (2 : Fin 3) ∉ (finish (List.finRange 3) [0] rawSlots).finished := by decide

theorem self_loop_finishes_once :
    (finish (List.finRange 1) [0] (fun _ => [some (0 : Fin 1), none])).finished = [0] := by decide

theorem empty_graph :
    (finish ([] : List (Fin 0)) [] (fun _ => [])).finished = [] := rfl

def oneWay (vertex : Fin 2) : List (Option (Fin 2)) := if vertex = 0 then [some 1] else []
def oneWayParents (vertex : Fin 2) : List (Fin 2) := if vertex = 1 then [0] else []

theorem generated_reverse_order : order (List.finRange 2) (List.finRange 2) oneWay = [0, 1] := by decide

theorem generated_second_pass_separates :
    (List.finRange 2).map (ComponentNumbering.component (List.finRange 2)
      (order (List.finRange 2) (List.finRange 2) oneWay) oneWayParents) = [0, 1] := by decide

theorem generated_second_pass_bounds (vertex : Fin 2) :
    ComponentNumbering.component (List.finRange 2)
      (order (List.finRange 2) (List.finRange 2) oneWay) oneWayParents vertex < 2 := by
  simpa using second_pass_id_bound (List.finRange 2) (CoreEnumeration.finRange_unique 2)
    (CoreEnumeration.finRange_covers 2) (List.finRange 2) (CoreEnumeration.finRange_covers 2)
    oneWay oneWayParents vertex

end PetaProof.ForwardDfs.Examples
