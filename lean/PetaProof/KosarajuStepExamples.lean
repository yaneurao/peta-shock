import PetaProof.KosarajuStep
import PetaProof.ForwardDfsFinishRankExamples

namespace PetaProof.KosarajuStep.Examples

def outgoing := ForwardDfs.FinishRankExamples.twoComponents
def last := ForwardDfs.FinishRankExamples.twoLast
def parents (vertex : Fin 4) : List (Fin 4) :=
  match vertex.val with
  | 0 => [1]
  | 1 => [0]
  | 2 => [1, 3]
  | _ => [2]

theorem fin4_cases (vertex : Fin 4) : vertex = 0 ∨ vertex = 1 ∨ vertex = 2 ∨ vertex = 3 := by
  have bound := vertex.isLt
  have values : vertex.val = 0 ∨ vertex.val = 1 ∨ vertex.val = 2 ∨ vertex.val = 3 := by omega
  rcases values with same | same | same | same
  · exact Or.inl (Fin.ext same)
  · exact Or.inr (Or.inl (Fin.ext same))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext same)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext same)))

theorem parents_correct (source target : Fin 4) : target ∈ parents source ↔ ForwardDfs.Edge outgoing target source := by
  change target ∈ parents source ↔ some source ∈ outgoing target
  rcases fin4_cases source with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases target with rfl | rfl | rfl | rfl <;> decide

theorem timeline : ForwardDfs.Timeline outgoing ForwardDfs.initial last :=
  ForwardDfs.finish_timeline _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4) outgoing _

theorem listed (vertex : Fin 4) : vertex ∈ last.finished :=
  ForwardDfs.finish_covers _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) outgoing vertex

theorem initial_whole : Saturated outgoing (ComponentNumbering.initial : ComponentNumbering.State (Fin 4)).result := by
  intro a b _
  simp [ComponentNumbering.initial]

theorem highest_first : Highest last.finished (ComponentNumbering.initial : ComponentNumbering.State (Fin 4)).result 0 := by
  intro vertex _
  have bound := List.idxOf_lt_length (listed vertex)
  change last.finished.idxOf vertex < 4 at bound
  change last.finished.idxOf vertex ≤ 3
  omega

def first : ComponentNumbering.State (Fin 4) := ComponentNumbering.step 4 parents ComponentNumbering.initial 0
def second : ComponentNumbering.State (Fin 4) := ComponentNumbering.step 4 parents first 2

theorem first_is_whole : Saturated outgoing first.result :=
  step_preserves_saturated _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing parents parents_correct last timeline rfl listed ComponentNumbering.initial ComponentNumbering.initial_invariant
    initial_whole 0 (fun _ => highest_first)

theorem first_labels : (List.finRange 4).map first.result = [some 0, some 0, none, none] := by decide

theorem highest_second : Highest last.finished first.result 2 := by
  intro vertex fresh
  rcases fin4_cases vertex with rfl | rfl | rfl | rfl
  · change some 0 = none at fresh; cases fresh
  · change some 0 = none at fresh; cases fresh
  · decide
  · decide

theorem first_valid : ComponentNumbering.Invariant first :=
  ComponentNumbering.step_preserves 4 parents ComponentNumbering.initial ComponentNumbering.initial_invariant 0

theorem second_component_exact (vertex : Fin 4) :
    (ComponentNumbering.descend 4 parents first 2).result vertex = some 1 ↔ ForwardDfs.Mutual outgoing 2 vertex :=
  descend_one_component _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing parents parents_correct last timeline rfl listed first first_valid first_is_whole 2 (by decide) highest_second vertex

theorem second_is_whole : Saturated outgoing second.result :=
  step_preserves_saturated _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing parents parents_correct last timeline rfl listed first first_valid first_is_whole 2 (fun _ => highest_second)

theorem old_component_not_overwritten :
    (List.finRange 4).map second.result = [some 0, some 0, some 1, some 1] := by decide

theorem assigned_root_is_skipped : ComponentNumbering.step 4 parents first 1 = first := by
  have assigned : first.result 1 ≠ none := by decide
  simp [ComponentNumbering.step, assigned]

theorem concrete_two_pass_output :
    (List.finRange 4).map (ComponentNumbering.finish (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) (List.finRange 4) outgoing) parents).result =
      [some 0, some 0, some 1, some 1] := by decide

def blocked (vertex : Fin 4) : Option Nat := if vertex = 1 then some 7 else none
def lineParents (vertex : Fin 4) : List (Fin 4) :=
  match vertex.val with
  | 0 => [1, 1]
  | 1 => [2]
  | 2 => [3]
  | _ => []

theorem blocked_vertex_stops_the_path :
    (List.finRange 4).map (ReverseDfsStack.explore (List.finRange 4) 8 blocked lineParents 0).result =
      [some 8, some 7, none, none] := by decide

def partlyAssigned (vertex : Fin 4) : Option Nat := if vertex = 0 then some 7 else none

theorem partial_component_is_rejected : ¬Saturated outgoing partlyAssigned := by
  intro whole
  have same : ForwardDfs.Mutual outgoing (0 : Fin 4) 1 :=
    ⟨⟨.cons (by change some (1 : Fin 4) ∈ outgoing 0; decide) (.nil 1)⟩,
     ⟨.cons (by change some (0 : Fin 4) ∈ outgoing 1; decide) (.nil 0)⟩⟩
  have impossible := (whole 0 1 same).mpr (by decide)
  change some 7 = none at impossible
  cases impossible

end PetaProof.KosarajuStep.Examples
