import PetaProof.SccParentCallback

namespace PetaProof.SccIndexedView.Examples

def edges (vertex : Fin 3) : List (Fin 7) :=
  match vertex.val with
  | 0 => [0, 1, 5]
  | 1 => [2, 3]
  | _ => [4, 6]

def source (edge : Fin 7) : Fin 3 :=
  if edge.val = 0 ∨ edge.val = 1 ∨ edge.val = 5 then 0
  else if edge.val = 2 ∨ edge.val = 3 then 1 else 2

def child (edge : Fin 7) : Option (Fin 3) :=
  match edge.val with
  | 0 | 1 | 3 => some 1
  | 2 => some 0
  | 4 => some 2
  | _ => none

def allow (edge : Fin 7) : Bool := !(edge == 1 || edge == 3 || edge == 6)

theorem fin3_cases (vertex : Fin 3) : vertex = 0 ∨ vertex = 1 ∨ vertex = 2 := by
  have bound := vertex.isLt
  have values : vertex.val = 0 ∨ vertex.val = 1 ∨ vertex.val = 2 := by omega
  rcases values with same | same | same
  · exact Or.inl (Fin.ext same)
  · exact Or.inr (Or.inl (Fin.ext same))
  · exact Or.inr (Or.inr (Fin.ext same))

theorem fin7_cases (edge : Fin 7) :
    edge = 0 ∨ edge = 1 ∨ edge = 2 ∨ edge = 3 ∨ edge = 4 ∨ edge = 5 ∨ edge = 6 := by
  have bound := edge.isLt
  have values : edge.val = 0 ∨ edge.val = 1 ∨ edge.val = 2 ∨ edge.val = 3 ∨ edge.val = 4 ∨ edge.val = 5 ∨ edge.val = 6 := by omega
  rcases values with same | same | same | same | same | same | same
  · exact Or.inl (Fin.ext same)
  · exact Or.inr (Or.inl (Fin.ext same))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext same)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext same))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext same)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext same))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext same))))))

def view : View (Fin 3) (Fin 7) where
  outgoing := edges
  source := source
  child := child
  at_source := by
    intro edge
    rcases fin7_cases edge with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  source_of_mem := by
    intro vertex edge member
    rcases fin3_cases vertex with rfl | rfl | rfl <;>
      rcases fin7_cases edge with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | simp [edges] at member

theorem raw_ids_preserved :
    (List.finRange 3).map (incoming view (List.finRange 3)) = [[2], [0, 1, 3], [4]] := by decide

theorem original_edge_allow_used :
    (List.finRange 3).map (parents view (List.finRange 3) allow) = [[1], [0], [2]] := by decide

theorem self_loops_filtered :
    (List.finRange 3).map (selfLoop view (List.finRange 3) allow) = [false, false, true] := by decide

theorem constructed_transpose (a b : Fin 3) :
    a ∈ parents view (List.finRange 3) allow b ↔ ForwardDfs.Edge (outgoing view allow) a b :=
  parents_transpose view _ (CoreEnumeration.finRange_covers 3) allow b a

theorem all_three_cyclic : core view (List.finRange 3) (List.finRange 3) allow = [0, 1, 2] := by decide

def restricted (edge : Fin 7) : Bool := edge == 0 || edge == 4

theorem removing_return_edge_breaks_cycle : core view (List.finRange 3) (List.finRange 3) restricted = [2] := by decide

theorem constructed_core_exact (vertex : Fin 3) :
    vertex ∈ core view (List.finRange 3) (List.finRange 3) allow ↔ CyclicVertex (relation view allow) vertex :=
  core_relation_correct view _ (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    _ (CoreEnumeration.finRange_covers 3) allow vertex

def seeded : SccParentCallback.State (Fin 3) :=
  (ReverseDfsStack.push 7 (ReverseDfsStack.initial (fun _ => none)) 2, false)

/-- 根の番号は既に付いていても、自己辺を見たらフラグを立てる。 -/
theorem assigned_self_edge_still_detected :
    (SccParentCallback.callback 7 view allow 2 4 seeded).1 = seeded.1 ∧
    (SccParentCallback.callback 7 view allow 2 4 seeded).2 = true := by
  constructor
  · rfl
  · decide

theorem allowed_two_vertex_cycle_has_no_self_loop :
    let report := SccParentCallback.explore view (List.finRange 3) allow (fun _ => none) 0 0
    report.1.count = 2 ∧ report.2 = false := by decide

theorem singleton_self_loop_report :
    let report := SccParentCallback.explore view (List.finRange 3) allow (fun _ => none) 0 2
    report.1.count = 1 ∧ report.2 = true := by decide

theorem general_flag_applies (root : Fin 3) :
    (SccParentCallback.explore view (List.finRange 3) allow (fun _ => none) 0 root).2 = true ↔
      ∃ vertex, (SccParentCallback.explore view (List.finRange 3) allow (fun _ => none) 0 root).1.result vertex = some 0 ∧
        ForwardDfs.Edge (outgoing view allow) vertex vertex :=
  SccParentCallback.explore_flag_exact view _ (CoreEnumeration.finRange_unique 3)
    (CoreEnumeration.finRange_covers 3) allow (fun _ => none) 0 (by intro v; simp) root rfl

def last := ForwardDfs.finish (List.finRange 3) (List.finRange 3) (outgoing view allow)

theorem listed (vertex : Fin 3) : vertex ∈ last.finished :=
  ForwardDfs.finish_covers _ (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    _ (CoreEnumeration.finRange_covers 3) _ vertex

theorem highest_root : KosarajuStep.Highest last.finished
    (ComponentNumbering.initial : ComponentNumbering.State (Fin 3)).result 2 := by
  intro vertex _
  have bound := List.idxOf_lt_length (listed vertex)
  change last.finished.idxOf vertex < 3 at bound
  change last.finished.idxOf vertex ≤ 2
  omega

/-- countと逐次フラグを組み合わせる一般定理を、実際の第一成分に適用する。 -/
theorem first_component_cycle_exact :
    let report := SccParentCallback.explore view (List.finRange 3) allow (fun _ => none) 0 2
    (decide (1 < report.1.count) || report.2) = true ↔
      CyclicVertex (ForwardDfs.Edge (outgoing view allow)) 2 :=
  SccParentCallback.descend_cycle_iff view _ (CoreEnumeration.finRange_unique 3)
    (CoreEnumeration.finRange_covers 3) allow last
    (ForwardDfs.finish_timeline _ (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3) _ _)
    rfl listed ComponentNumbering.initial ComponentNumbering.initial_invariant
    (by intro a b same; rfl) 2 rfl highest_root

end PetaProof.SccIndexedView.Examples
