import PetaProof.ForwardDfsReach

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

/-- スタックは先頭が最深部。下にある祖先から上の子孫へ元の辺を辿れる。 -/
def ActivePath (outgoing : V → List (Option V)) (state : State V) : Prop :=
  state.active.Pairwise (fun descendant ancestor => Reach outgoing ancestor descendant)

omit [DecidableEq V] in
theorem initial_active_path (outgoing : V → List (Option V)) : ActivePath outgoing (initial : State V) := by
  simp [ActivePath, State.active, initial]

theorem discover_active_path (outgoing : V → List (Option V)) (state : State V)
    (valid : ActivePath outgoing state) (target : V)
    (reachable : ∀ ancestor ∈ state.active, Reach outgoing ancestor target) :
    ActivePath outgoing (discover outgoing state target) := by
  cases visited : state.seen target with
  | true => simpa [discover, visited] using valid
  | false =>
    change (discover outgoing state target).active.Pairwise _
    simp only [discover, visited, Bool.false_eq_true, ite_false, State.active, List.map_cons]
    exact List.pairwise_cons.mpr ⟨reachable, valid⟩

omit [DecidableEq V] in
theorem trim_active_path (outgoing : V → List (Option V)) (state : State V)
    (valid : ActivePath outgoing state) : ActivePath outgoing (trim state) := by
  change (trim state).active.Pairwise _
  rw [trim_active]
  exact valid

omit [DecidableEq V] in
theorem retire_active_path (outgoing : V → List (Option V)) (state : State V)
    (valid : ActivePath outgoing state) : ActivePath outgoing (retire state) := by
  cases stack : state.stack with
  | nil => simpa [retire, stack] using valid
  | cons frame rest =>
    have expanded : (frame.vertex :: rest.map Frame.vertex).Pairwise
        (fun descendant ancestor => Reach outgoing ancestor descendant) := by
      simpa [ActivePath, State.active, stack] using valid
    simpa [ActivePath, retire, stack, State.active] using (List.pairwise_cons.mp expanded).2

theorem tick_active_path (outgoing : V → List (Option V)) (state : State V)
    (scans : ScanInvariant outgoing state) (valid : ActivePath outgoing state) :
    ActivePath outgoing (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa [tick, stack] using valid
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa [tick, stack, todo] using retire_active_path outgoing state valid
    | cons target remaining =>
      cases target with
      | none => simpa [tick, stack, todo] using trim_active_path outgoing state valid
      | some child =>
        have edge := scanned_edge outgoing state.seen frame (scans.cursor frame (by simp [stack])) child
          (by simp [todo])
        have expanded : (frame.vertex :: rest.map Frame.vertex).Pairwise
            (fun descendant ancestor => Reach outgoing ancestor descendant) := by
          simpa [ActivePath, State.active, stack] using valid
        have from_ancestor : ∀ ancestor ∈ (trim state).active, Reach outgoing ancestor child := by
          intro ancestor member
          rw [trim_active] at member
          have cases_member : ancestor = frame.vertex ∨ ancestor ∈ rest.map Frame.vertex := by
            simpa [State.active, stack] using member
          rcases cases_member with same | below
          · subst ancestor
            exact ⟨.cons edge (.nil child)⟩
          · obtain ⟨path⟩ : Nonempty (Walk (Edge outgoing) ancestor frame.vertex) :=
              (List.pairwise_cons.mp expanded).1 ancestor below
            exact ⟨path.append (.cons edge (.nil child))⟩
        simpa [tick, stack, todo] using discover_active_path outgoing (trim state)
          (trim_active_path outgoing state valid) child from_ancestor

theorem walk_active_path (outgoing : V → List (Option V)) (fuel : Nat) (state : State V)
    (scans : ScanInvariant outgoing state) (valid : ActivePath outgoing state) :
    ActivePath outgoing (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa [walk, stack] using valid
    | cons frame rest =>
      simpa only [walk, stack] using ih _ (tick_scanned outgoing state scans)
        (tick_active_path outgoing state scans valid)

theorem root_active_path (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (scans : ScanInvariant outgoing state) (empty : state.stack = []) (start : V) :
    ActivePath outgoing (root vertices outgoing state start) := by
  have before : ActivePath outgoing state := by simp [ActivePath, State.active, empty]
  have seeded := discover_active_path outgoing state before start (by
    intro ancestor member
    simp [State.active, empty] at member)
  exact walk_active_path outgoing _ _ (discover_scanned outgoing state scans start) seeded

omit [DecidableEq V] in
/-- 最深部から活動中の祖先へ戻る辺があれば、元のグラフで両者は相互到達可能。 -/
theorem active_back_edge_mutual (outgoing : V → List (Option V)) (state : State V)
    (valid : ActivePath outgoing state) (frame : Frame V) (rest : List (Frame V))
    (stack : state.stack = frame :: rest) (ancestor : V) (below : ancestor ∈ rest.map Frame.vertex)
    (back : Edge outgoing frame.vertex ancestor) :
    Reach outgoing frame.vertex ancestor ∧ Reach outgoing ancestor frame.vertex := by
  have expanded : (frame.vertex :: rest.map Frame.vertex).Pairwise
      (fun descendant ancestor => Reach outgoing ancestor descendant) := by
    simpa [ActivePath, State.active, stack] using valid
  exact ⟨⟨.cons back (.nil ancestor)⟩, (List.pairwise_cons.mp expanded).1 ancestor below⟩

end PetaProof.ForwardDfs
