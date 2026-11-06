import PetaProof.ForwardDfsScanned

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

structure Rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (state : State V) : Prop where
  active : ∀ vertex ∈ state.active, Reach outgoing start vertex
  seen : ∀ vertex, state.seen vertex = true → previous vertex = true ∨ Reach outgoing start vertex

omit [DecidableEq V] in
theorem trim_active (state : State V) : (trim state).active = state.active := by
  cases stack : state.stack <;> simp [trim, State.active, stack]

omit [DecidableEq V] in
theorem retire_active_subset (state : State V) (vertex : V) :
    vertex ∈ (retire state).active → vertex ∈ state.active := by
  intro member
  cases stack : state.stack with
  | nil => simpa [retire, stack] using member
  | cons frame rest =>
    have old : vertex ∈ rest.map Frame.vertex := by simpa [retire, stack, State.active] using member
    simp [State.active, stack, old]

omit [DecidableEq V] in
theorem empty_rooted (outgoing : V → List (Option V)) (start : V) (state : State V)
    (empty : state.stack = []) : Rooted outgoing start state.seen state := by
  refine ⟨?_, fun vertex visited => Or.inl visited⟩
  intro vertex member
  simp [State.active, empty] at member

theorem discover_rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (state : State V) (valid : Rooted outgoing start previous state)
    (target : V) (reachable : Reach outgoing start target) :
    Rooted outgoing start previous (discover outgoing state target) := by
  cases visited : state.seen target with
  | true => simpa [discover, visited] using valid
  | false =>
    constructor
    · intro vertex member
      have cases_member : vertex = target ∨ vertex ∈ state.active := by
        simpa [discover, visited, State.active] using member
      rcases cases_member with rfl | old
      · exact reachable
      · exact valid.active vertex old
    · intro vertex seen
      have cases_seen : vertex = target ∨ state.seen vertex = true := by
        simpa [discover, visited, markSeen_true_iff] using seen
      rcases cases_seen with rfl | old
      · exact Or.inr reachable
      · exact valid.seen vertex old

omit [DecidableEq V] in
theorem trim_rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (state : State V) (valid : Rooted outgoing start previous state) :
    Rooted outgoing start previous (trim state) := by
  constructor
  · intro vertex member
    rw [trim_active] at member
    exact valid.active vertex member
  · intro vertex visited
    rw [trim_seen] at visited
    exact valid.seen vertex visited

omit [DecidableEq V] in
theorem retire_rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (state : State V) (valid : Rooted outgoing start previous state) :
    Rooted outgoing start previous (retire state) := by
  constructor
  · intro vertex member
    exact valid.active vertex (retire_active_subset state vertex member)
  · intro vertex visited
    rw [retire_seen] at visited
    exact valid.seen vertex visited

theorem tick_rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (state : State V) (scans : ScanInvariant outgoing state) (valid : Rooted outgoing start previous state) :
    Rooted outgoing start previous (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa [tick, stack] using valid
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa [tick, stack, todo] using retire_rooted outgoing start previous state valid
    | cons target remaining =>
      cases target with
      | none => simpa [tick, stack, todo] using trim_rooted outgoing start previous state valid
      | some child =>
        have parent : Reach outgoing start frame.vertex := valid.active frame.vertex (by simp [State.active, stack])
        have edge := scanned_edge outgoing state.seen frame (scans.cursor frame (by simp [stack])) child
          (by simp [todo])
        obtain ⟨walk⟩ := parent
        have child_path : Reach outgoing start child := ⟨walk.append (.cons edge (.nil child))⟩
        simpa [tick, stack, todo] using discover_rooted outgoing start previous (trim state)
          (trim_rooted outgoing start previous state valid) child child_path

theorem walk_rooted (outgoing : V → List (Option V)) (start : V) (previous : V → Bool)
    (fuel : Nat) (state : State V) (scans : ScanInvariant outgoing state)
    (valid : Rooted outgoing start previous state) :
    Rooted outgoing start previous (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa [walk, stack] using valid
    | cons frame rest =>
      simpa only [walk, stack] using ih _ (tick_scanned outgoing state scans)
        (tick_rooted outgoing start previous state scans valid)

theorem root_scanned (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (valid : ScanInvariant outgoing state) (vertex : V) :
    ScanInvariant outgoing (root vertices outgoing state vertex) :=
  walk_scanned outgoing _ _ (discover_scanned outgoing state valid vertex)

/-- 一つの根の探索で新しく訪問した頂点は、その根から本当に到達できる。 -/
theorem root_reachable (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (scans : ScanInvariant outgoing state) (empty : state.stack = []) (start vertex : V)
    (visited : (root vertices outgoing state start).seen vertex = true) :
    state.seen vertex = true ∨ Reach outgoing start vertex := by
  have seeded := discover_rooted outgoing start state.seen state (empty_rooted outgoing start state empty)
    start (by exact ⟨.nil start⟩)
  have final := walk_rooted outgoing start state.seen (capacity vertices outgoing)
    (discover outgoing state start) (discover_scanned outgoing state scans start) seeded
  exact final.seen vertex visited

/-- 根から到達できる頂点は、既訪問部分を含め、DFSの完了時には訪問済みとなる。 -/
theorem root_exact (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (state : State V)
    (scans : ScanInvariant outgoing state) (empty : state.stack = []) (start vertex : V) :
    (root vertices outgoing state start).seen vertex = true ↔
      state.seen vertex = true ∨ Reach outgoing start vertex := by
  constructor
  · exact root_reachable vertices outgoing state scans empty start vertex
  · intro available
    rcases available with old | reachable
    · exact root_seen_stable vertices outgoing state start vertex old
    · obtain ⟨path⟩ : Nonempty (Walk (Edge outgoing) start vertex) := reachable
      exact seen_reachable outgoing _ (root_scanned vertices outgoing state scans start)
        (root_drains vertices unique covered outgoing state empty start) path
        (root_seen_at vertices outgoing state start)

theorem forest_scanned (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (scans : ScanInvariant outgoing state) (empty : state.stack = []) :
    ScanInvariant outgoing (forest vertices outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact scans
  | cons vertex rest ih =>
    exact ih _ (root_scanned vertices outgoing state scans vertex)
      (root_drains vertices unique covered outgoing state empty vertex)

/-- 全頂点の根列でなくても、各根から到達できる集合を正確に探索する。 -/
theorem forest_exact (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (scans : ScanInvariant outgoing state) (empty : state.stack = []) (vertex : V) :
    (forest vertices outgoing roots state).seen vertex = true ↔
      state.seen vertex = true ∨ ∃ start ∈ roots, Reach outgoing start vertex := by
  induction roots generalizing state with
  | nil => simp [forest]
  | cons start rest ih =>
    rw [forest, ih _ (root_scanned vertices outgoing state scans start)
      (root_drains vertices unique covered outgoing state empty start),
      root_exact vertices unique covered outgoing state scans empty start vertex]
    constructor
    · intro available
      rcases available with first | later
      · rcases first with old | path
        · exact Or.inl old
        · exact Or.inr ⟨start, by simp, path⟩
      · obtain ⟨source, member, path⟩ := later
        exact Or.inr ⟨source, List.mem_cons_of_mem start member, path⟩
    · intro available
      rcases available with old | reached
      · exact Or.inl (Or.inl old)
      · obtain ⟨source, member, path⟩ := reached
        rcases List.mem_cons.mp member with same | later
        · subst source
          exact Or.inl (Or.inr path)
        · exact Or.inr ⟨source, later, path⟩

theorem finish_seen_exact (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (outgoing : V → List (Option V)) (vertex : V) :
    (finish vertices roots outgoing).seen vertex = true ↔
      ∃ start ∈ roots, Reach outgoing start vertex := by
  simpa [finish, initial] using forest_exact vertices unique covered outgoing roots initial
    (initial_scanned outgoing) rfl vertex

theorem finish_finished_exact (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (outgoing : V → List (Option V)) (vertex : V) :
    vertex ∈ (finish vertices roots outgoing).finished ↔
      ∃ start ∈ roots, Reach outgoing start vertex := by
  have scans := forest_scanned vertices unique covered outgoing roots initial (initial_scanned outgoing) rfl
  have empty := forest_drains vertices unique covered outgoing roots initial rfl
  have membership : (finish vertices roots outgoing).seen vertex = true ↔
      vertex ∈ (finish vertices roots outgoing).finished := by
    simpa [finish, State.total, State.active, empty] using scans.base.covers vertex
  exact membership.symm.trans (finish_seen_exact vertices unique covered roots outgoing vertex)

omit [DecidableEq V] in
/-- 完了した根の探索領域から、まだ未訪問の頂点へ至る元グラフの歩道は存在しない。 -/
theorem no_path_to_unseen (outgoing : V → List (Option V)) (state : State V)
    (scans : ScanInvariant outgoing state) (empty : state.stack = [])
    (source target : V) (finished : source ∈ state.finished) (unseen : state.seen target = false) :
    ¬Reach outgoing source target := by
  intro reachable
  obtain ⟨path⟩ : Nonempty (Walk (Edge outgoing) source target) := reachable
  have source_seen : state.seen source = true :=
    (scans.base.covers source).mpr (List.mem_append_left _ finished)
  have target_seen := seen_reachable outgoing state scans empty path source_seen
  rw [unseen] at target_seen
  cases target_seen

theorem finished_reachable_closed (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (outgoing : V → List (Option V)) (source target : V)
    (finished : source ∈ (finish vertices roots outgoing).finished) (reachable : Reach outgoing source target) :
    target ∈ (finish vertices roots outgoing).finished := by
  obtain ⟨start, member, path⟩ := (finish_finished_exact vertices unique covered roots outgoing source).mp finished
  obtain ⟨first⟩ : Nonempty (Walk (Edge outgoing) start source) := path
  obtain ⟨last⟩ : Nonempty (Walk (Edge outgoing) source target) := reachable
  exact (finish_finished_exact vertices unique covered roots outgoing target).mpr ⟨start, member, ⟨first.append last⟩⟩

end PetaProof.ForwardDfs
