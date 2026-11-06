import PetaProof.ForwardDfsActivePath

namespace PetaProof.ForwardDfs.ReachExamples

def outgoing (vertex : Fin 4) : List (Option (Fin 4)) :=
  match vertex.val with
  | 0 => [some 1, none]
  | 1 => [some 2]
  | 2 => [some 1]
  | _ => []

def partialState : State (Fin 4) := finish (List.finRange 4) [0] outgoing

theorem partial_members : partialState.finished = [2, 1, 0] ∧ partialState.seen 3 = false := by decide

theorem partial_scanned : ScanInvariant outgoing partialState :=
  forest_scanned _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing [0] initial (initial_scanned outgoing) rfl

theorem partial_empty : partialState.stack = [] :=
  forest_drains _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing [0] initial rfl

theorem partial_exact (vertex : Fin 4) : vertex ∈ partialState.finished ↔ Reach outgoing 0 vertex := by
  simpa using finish_finished_exact _ (CoreEnumeration.finRange_unique 4)
    (CoreEnumeration.finRange_covers 4) [0] outgoing vertex

theorem old_region_cannot_reach_next_root : ¬Reach outgoing (0 : Fin 4) 3 :=
  no_path_to_unseen outgoing partialState partial_scanned partial_empty 0 3 (by decide) (by decide)

theorem next_root_exact (vertex : Fin 4) :
    (root (List.finRange 4) outgoing partialState 3).seen vertex = true ↔
    partialState.seen vertex = true ∨ Reach outgoing 3 vertex :=
  root_exact _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    outgoing partialState partial_scanned partial_empty 3 vertex

theorem old_vertices_survive_next_root :
    (List.finRange 4).map (root (List.finRange 4) outgoing partialState 3).seen = [true, true, true, true] := by decide

def twoCycle (vertex : Fin 3) : List (Option (Fin 3)) :=
  match vertex.val with
  | 0 => [some 1]
  | 1 => [some 0]
  | _ => []

def middle : State (Fin 3) := walk twoCycle 3 (discover twoCycle initial 0)

theorem middle_scanned : ScanInvariant twoCycle middle :=
  walk_scanned twoCycle 3 _ (discover_scanned twoCycle initial (initial_scanned twoCycle) 0)

/-- 子Bの終了時に祖先Aはまだ活動中。終了した頂点集合だけの閉性は途中では成り立たない。 -/
theorem finished_can_reach_active_ancestor :
    middle.finished = [1] ∧ middle.active = [0] ∧
    (0 : Fin 3) ∉ middle.finished ∧ middle.seen 0 = true := by decide

theorem backward_edge_is_real : Reach twoCycle (1 : Fin 3) 0 :=
  ⟨.cons (by change some (0 : Fin 3) ∈ twoCycle 1; decide) (.nil 0)⟩

def beforeBack : State (Fin 3) := walk twoCycle 1 (discover twoCycle initial 0)

theorem before_back_active_path : ActivePath twoCycle beforeBack := by
  apply walk_active_path twoCycle 1 _ (discover_scanned twoCycle initial (initial_scanned twoCycle) 0)
  apply discover_active_path twoCycle initial (initial_active_path twoCycle) 0
  intro ancestor member
  simp [State.active, initial] at member

theorem active_back_edge_connects_both_directions : Reach twoCycle (1 : Fin 3) 0 ∧ Reach twoCycle 0 1 :=
  active_back_edge_mutual twoCycle beforeBack before_back_active_path
    ⟨1, [some 0]⟩ [⟨0, []⟩] rfl 0 (by simp) (by change some (0 : Fin 3) ∈ twoCycle 1; decide)

def skippedChild : State (Fin 3) := ⟨fun vertex => vertex == 0, [⟨0, []⟩], []⟩

theorem cannot_finish_before_visiting_child : ¬ScanInvariant twoCycle skippedChild := by
  intro valid
  obtain ⟨prior, same, visited⟩ := valid.cursor (⟨0, []⟩ : Frame (Fin 3)) (by simp [skippedChild])
  have member : some (1 : Fin 3) ∈ prior := by
    have actual : some (1 : Fin 3) ∈ twoCycle 0 := by decide
    simpa [same] using actual
  have impossible := visited 1 member
  change false = true at impossible
  cases impossible

theorem invented_cursor_is_rejected :
    ¬Scanned twoCycle (fun _ => true) (⟨0, [some 2]⟩ : Frame (Fin 3)) := by
  rintro ⟨prior, same, _⟩
  have fake : some (2 : Fin 3) ∈ twoCycle 0 := by
    rw [same]
    simp
  have absent : some (2 : Fin 3) ∉ twoCycle 0 := by decide
  exact absent fake

end PetaProof.ForwardDfs.ReachExamples
