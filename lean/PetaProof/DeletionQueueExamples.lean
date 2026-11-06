import PetaProof.DeletionQueue

namespace PetaProof.DeletionQueue.Examples

-- false が子、true が親。同じ親へ向かう別々の二本の逆辺を持つ。
def vertices : List Bool := [false, true]
def weight (v : Bool) : Nat := if v then 0 else 2
def start : State Bool := ⟨fun _ => false, [false]⟩
def childRemoved : State Bool := ⟨markSeen (fun _ => false) false, [true, true]⟩
def parentRemoved : State Bool := ⟨markSeen childRemoved.deleted true, [true]⟩
def finished : State Bool := ⟨parentRemoved.deleted, []⟩

theorem duplicate_parents : Step weight start childRemoved := by
  exact Step.remove _ false [] [true, true] rfl (by decide)

theorem parent_once : Step weight childRemoved parentRemoved := by
  exact Step.remove _ true [true] [] (by decide) (by decide)

theorem duplicate_skipped : Step weight parentRemoved finished := by
  exact Step.stale _ true [] (by decide)

theorem three_pops : Run weight start 3 finished :=
  Run.next duplicate_parents (Run.next parent_once (Run.next duplicate_skipped (Run.done _)))

theorem bound_is_tight :
    budget vertices weight start = 3 ∧ budget vertices weight childRemoved = 2 ∧
    budget vertices weight parentRemoved = 1 ∧ budget vertices weight finished = 0 := by decide

theorem duplicate_run_bound : 3 ≤ [false].length + (vertices.map weight).sum := by
  exact initial_bound vertices (by decide) (by intro v; cases v <;> simp [vertices]) weight [false] three_pops

theorem two_edge_scans : ScannedRun weight start 3 2 finished := by
  exact ScannedRun.next duplicate_parents
    (ScannedRun.next parent_once (ScannedRun.next duplicate_skipped (ScannedRun.done _)))

theorem duplicate_scan_bound : 2 ≤ (vertices.map weight).sum :=
  initial_scan_bound vertices (by decide) (by intro v; cases v <;> simp [vertices]) weight [false] two_edge_scans

end PetaProof.DeletionQueue.Examples
