import PetaProof.ForwardDfsSccOrder

namespace PetaProof.ForwardDfs.FinishRankExamples

def outgoing (vertex : Fin 2) : List (Option (Fin 2)) := if vertex = 0 then [some 1] else []
def last : State (Fin 2) := finish (List.finRange 2) (List.finRange 2) outgoing
def beforeChild : State (Fin 2) := tick outgoing (discover outgoing initial 0)

theorem actual_order : last.finished = [1, 0] := by decide

theorem full_timeline : Timeline outgoing initial last :=
  finish_timeline _ (CoreEnumeration.finRange_unique 2) (CoreEnumeration.finRange_covers 2) outgoing _

theorem child_tail : Timeline outgoing (tick outgoing beforeChild) last := by
  have run := walk_timeline outgoing 3 (tick outgoing beforeChild)
  change Timeline outgoing (tick outgoing beforeChild) last at run
  exact run

theorem before_valid : Invariant beforeChild :=
  tick_preserves outgoing _ (discover_preserves outgoing initial initial_invariant 0)

theorem last_valid : Invariant last :=
  forest_preserves _ outgoing _ initial initial_invariant

theorem child_finishes_before_ancestor : last.finished.idxOf (1 : Fin 2) < last.finished.idxOf (0 : Fin 2) :=
  retirement_ancestor_later outgoing beforeChild last before_valid last_valid rfl
    ⟨1, []⟩ [⟨0, []⟩] rfl rfl child_tail 0 (by simp)

theorem child_retirement_rank : last.finished.idxOf (1 : Fin 2) = beforeChild.finished.length :=
  retirement_rank outgoing beforeChild last before_valid ⟨1, []⟩ [⟨0, []⟩] rfl rfl child_tail

theorem each_vertex_has_retirement (vertex : Fin 2) :
    ∃ state, Timeline outgoing initial state ∧ Retiring state vertex ∧ Timeline outgoing (tick outgoing state) last :=
  full_timeline.retirement_witness vertex
    (finish_covers _ (CoreEnumeration.finRange_unique 2) (CoreEnumeration.finRange_covers 2)
      _ (CoreEnumeration.finRange_covers 2) outgoing vertex) (by simp [initial])

theorem edge_shape (source target : Fin 2) (edge : Edge outgoing source target) : source = 0 ∧ target = 1 := by
  by_cases same : source = 0
  · subst source
    exact ⟨rfl, by simpa [Edge, outgoing] using edge⟩
  · simp [Edge, outgoing, same] at edge

theorem no_return : ¬Reach outgoing (1 : Fin 2) 0 := by
  intro reachable
  obtain ⟨path⟩ : Nonempty (Walk (Edge outgoing) (1 : Fin 2) 0) := reachable
  have bound := path.nat_monotone Fin.val (by
    intro source target edge
    obtain ⟨rfl, rfl⟩ := edge_shape source target edge
    decide)
  change 1 ≤ 0 at bound
  omega

theorem source_is_latest : Latest outgoing last (0 : Fin 2) := by
  intro other connected
  by_cases same : other = 0
  · simp [same]
  · have other_one : other = 1 := by
      apply Fin.ext
      have small := other.isLt
      have nonzero : other.val ≠ 0 := by intro eq; exact same (Fin.ext eq)
      omega
    subst other
    exact False.elim (no_return connected.2)

theorem computed_scc_order : last.finished.idxOf (1 : Fin 2) < last.finished.idxOf (0 : Fin 2) :=
  finish_scc_order _ (CoreEnumeration.finRange_unique 2) (CoreEnumeration.finRange_covers 2)
    _ (CoreEnumeration.finRange_covers 2) outgoing 0 1 source_is_latest
    ⟨.cons (by change some (1 : Fin 2) ∈ outgoing 0; decide) (.nil 1)⟩ no_return

theorem representative_exists (vertex : Fin 2) :
    ∃ representative, Mutual outgoing vertex representative ∧ Latest outgoing last representative :=
  finish_latest_exists _ (CoreEnumeration.finRange_unique 2) (CoreEnumeration.finRange_covers 2)
    _ (CoreEnumeration.finRange_covers 2) outgoing vertex

def cycle (vertex : Fin 2) : List (Option (Fin 2)) := if vertex = 0 then [some 1] else [some 0]
def cycleLast : State (Fin 2) := finish (List.finRange 2) (List.finRange 2) cycle

/-- 同じSCCでも先に終了した頂点は、最大終了順位の代表としては使えない。 -/
theorem nonlatest_cycle_vertex_rejected : ¬Latest cycle cycleLast (1 : Fin 2) := by
  intro latest
  have connected : Mutual cycle (1 : Fin 2) 0 :=
    ⟨⟨.cons (by change some (0 : Fin 2) ∈ cycle 1; decide) (.nil 0)⟩,
     ⟨.cons (by change some (1 : Fin 2) ∈ cycle 0; decide) (.nil 1)⟩⟩
  have bad := latest 0 connected
  change 1 ≤ 0 at bad
  omega

def twoComponents (vertex : Fin 4) : List (Option (Fin 4)) :=
  match vertex.val with
  | 0 => [some 1]
  | 1 => [some 0, some 2]
  | 2 => [some 3]
  | _ => [some 2]

def twoLast : State (Fin 4) := finish (List.finRange 4) (List.finRange 4) twoComponents
def secondOnly : State (Fin 4) := finish (List.finRange 4) [2] twoComponents

theorem two_components_finishing_order : twoLast.finished = [3, 2, 1, 0] := by decide

theorem first_representative_latest : Latest twoComponents twoLast (0 : Fin 4) := by
  intro other _
  have present := finish_covers _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) twoComponents other
  have bounded := List.idxOf_lt_length present
  change twoLast.finished.idxOf other < 4 at bounded
  change twoLast.finished.idxOf other ≤ 3
  omega

theorem no_return_between_components : ¬Reach twoComponents (2 : Fin 4) 1 :=
  no_path_to_unseen twoComponents secondOnly
    (forest_scanned _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
      twoComponents [2] initial (initial_scanned twoComponents) rfl)
    (forest_drains _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
      twoComponents [2] initial rfl) 2 1 (by decide) (by decide)

theorem second_representative_latest : Latest twoComponents twoLast (2 : Fin 4) := by
  intro other connected
  have inside := (finish_finished_exact _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    [2] twoComponents other).mpr ⟨2, by simp, connected.1⟩
  change other ∈ [3, 2] at inside
  have options : other = 3 ∨ other = 2 := by simpa using inside
  rcases options with rfl | rfl <;> decide

theorem two_component_maxima_order : twoLast.finished.idxOf (2 : Fin 4) < twoLast.finished.idxOf (0 : Fin 4) :=
  finish_scc_edge_order _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) twoComponents 1 2 0 2
    (by change some (2 : Fin 4) ∈ twoComponents 1; decide)
    ⟨⟨.cons (by change some (0 : Fin 4) ∈ twoComponents 1; decide) (.nil 0)⟩,
     ⟨.cons (by change some (1 : Fin 4) ∈ twoComponents 0; decide) (.nil 1)⟩⟩
    ⟨⟨.nil 2⟩, ⟨.nil 2⟩⟩ first_representative_latest no_return_between_components

end PetaProof.ForwardDfs.FinishRankExamples
