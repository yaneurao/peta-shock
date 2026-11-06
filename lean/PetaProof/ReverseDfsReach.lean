import PetaProof.ComponentNumbering

/-!
第二DFSの探索開始時の未割当部分における、実walkの到達集合。
closedは一つのpopと全parents callbackの終了後に保つ。callback途中には要求しない。
-/
namespace PetaProof.ReverseDfsStack

universe u
variable {V : Type u} [DecidableEq V]

def FreshEdge (previous : V → Option Nat) (parents : V → List V) (source target : V) : Prop :=
  target ∈ parents source ∧ previous source = none ∧ previous target = none

def FreshReach (previous : V → Option Nat) (parents : V → List V) (root vertex : V) : Prop :=
  Nonempty (Walk (FreshEdge previous parents) root vertex)

theorem Run.none_was_fresh {id : Nat} {previous : V → Option Nat} {state : State V}
    (run : Run id (initial previous) state) (vertex : V) (fresh : state.result vertex = none) :
    previous vertex = none := by
  rcases run.label_cases vertex with old | current
  · exact old.symm.trans fresh
  · rw [fresh] at current
    cases current

theorem Run.current_was_fresh {id : Nat} {previous : V → Option Nat} {state : State V}
    (run : Run id (initial previous) state) (unused : ∀ vertex, previous vertex ≠ some id)
    (vertex : V) (assigned : state.result vertex = some id) : previous vertex = none := by
  cases old : previous vertex with
  | none => rfl
  | some label =>
    have stable := run.label_stable vertex label old
    have same : label = id := Option.some.inj (stable.symm.trans assigned)
    exact False.elim (unused vertex (same ▸ old))

theorem push_fresh_assigned (id : Nat) (previous : V → Option Nat) (state : State V)
    (run : Run id (initial previous) state) (vertex : V) (fresh : previous vertex = none) :
    (push id state vertex).result vertex = some id := by
  rcases run.label_cases vertex with old | current
  · have now : state.result vertex = none := old.trans fresh
    simp [push, now]
  · simp [push, current]

theorem scan_fresh_assigned (id : Nat) (previous : V → Option Nat) (targets : List V) (state : State V)
    (run : Run id (initial previous) state) (vertex : V) (member : vertex ∈ targets)
    (fresh : previous vertex = none) : (scan id targets state).result vertex = some id := by
  induction targets generalizing state with
  | nil => cases member
  | cons target rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst vertex
      exact (scan_run id rest (push id state target)).label_stable target id
        (push_fresh_assigned id previous state run target fresh)
    · exact ih (push id state target) (.push run target) later

theorem scan_popped (id : Nat) (targets : List V) (state : State V) :
    (scan id targets state).popped = state.popped := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
    rw [scan, ih]
    cases found : state.result target <;> simp [push, found]

theorem push_origin (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (state : State V) (run : Run id (initial previous) state)
    (origin : ∀ vertex, state.result vertex = some id → FreshReach previous parents root vertex)
    (source target : V) (to_source : FreshReach previous parents root source)
    (source_fresh : previous source = none) (edge : target ∈ parents source) :
    ∀ vertex, (push id state target).result vertex = some id → FreshReach previous parents root vertex := by
  cases found : state.result target with
  | some label => simpa [push, found] using origin
  | none =>
    have target_fresh := run.none_was_fresh target found
    intro vertex assigned
    by_cases same : vertex = target
    · subst vertex
      obtain ⟨path⟩ : Nonempty (Walk (FreshEdge previous parents) root source) := to_source
      exact ⟨path.append (.cons ⟨edge, source_fresh, target_fresh⟩ (.nil target))⟩
    · apply origin vertex
      simpa [push, found, same] using assigned

theorem scan_origin (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (targets : List V) (state : State V) (run : Run id (initial previous) state)
    (origin : ∀ vertex, state.result vertex = some id → FreshReach previous parents root vertex)
    (source : V) (to_source : FreshReach previous parents root source) (source_fresh : previous source = none)
    (edges : ∀ target ∈ targets, target ∈ parents source) :
    ∀ vertex, (scan id targets state).result vertex = some id → FreshReach previous parents root vertex := by
  induction targets generalizing state with
  | nil => exact origin
  | cons target rest ih =>
    exact ih _ (.push run target)
      (push_origin id previous parents root state run origin source target to_source source_fresh (edges target (by simp)))
      (fun vertex member => edges vertex (List.mem_cons_of_mem target member))

structure Exploration (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (state : State V) : Prop where
  base : Invariant id state
  history : Run id (initial previous) state
  origin : ∀ vertex, state.result vertex = some id → FreshReach previous parents root vertex
  closed : ∀ vertex ∈ state.popped, ∀ target ∈ parents vertex,
    previous target = none → state.result target = some id

theorem seeded_exploration (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (fresh : previous root = none) :
    Exploration id previous parents root (push id (initial previous) root) := by
  refine ⟨push_preserves id _ (initial_invariant previous id unused) root, .push (.refl _) root, ?_, ?_⟩
  · intro vertex assigned
    by_cases same : vertex = root
    · subst vertex; exact ⟨.nil root⟩
    · have old : previous vertex = some id := by simpa [push, initial, fresh, same] using assigned
      exact False.elim (unused vertex old)
  · simp [push, initial, fresh]

theorem visit_exploration (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (state : State V)
    (valid : Exploration id previous parents root state) : Exploration id previous parents root (visit id parents state) := by
  cases pending : state.pending with
  | nil => simpa [visit, pending] using valid
  | cons source rest =>
    have assigned : state.result source = some id := (valid.base.assigned source).mpr (by
      simp [State.total, pending])
    have source_path := valid.origin source assigned
    have source_fresh := valid.history.current_was_fresh unused source assigned
    have popped_run : Run id (initial previous) (pop state) := .pop valid.history
    have popped_origin : ∀ vertex, (pop state).result vertex = some id → FreshReach previous parents root vertex := by
      simpa only [pop_result] using valid.origin
    refine ⟨visit_preserves id parents state valid.base, valid.history.trans (visit_run id parents state), ?_, ?_⟩
    · simpa only [visit, pending] using scan_origin id previous parents root (parents source) (pop state)
        popped_run popped_origin source source_path source_fresh (fun _ member => member)
    · intro vertex member target edge fresh
      have candidates : vertex ∈ state.popped ∨ vertex = source := by
        simpa [visit, pending, scan_popped, pop] using member
      rcases candidates with old | same
      · exact (visit_run id parents state).label_stable target id (valid.closed vertex old target edge fresh)
      · subst vertex
        simpa only [visit, pending] using scan_fresh_assigned id previous (parents source) (pop state)
          popped_run target edge fresh

theorem walk_exploration (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (fuel : Nat) (state : State V)
    (valid : Exploration id previous parents root state) : Exploration id previous parents root (walk id parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih _ (visit_exploration id previous parents root unused state valid)

def explore (vertices : List V) (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V) : State V :=
  walk id parents vertices.length (push id (initial previous) root)

theorem explore_valid (vertices : List V) (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (fresh : previous root = none) :
    Exploration id previous parents root (explore vertices id previous parents root) :=
  walk_exploration id previous parents root unused vertices.length _ (seeded_exploration id previous parents root unused fresh)

theorem explore_drains (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (fresh : previous root = none) :
    (explore vertices id previous parents root).pending = [] := by
  apply walk_drains vertices unique covered id parents vertices.length _
    (seeded_exploration id previous parents root unused fresh).base
  simp [push, initial, fresh]

theorem explore_exact (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (id : Nat) (previous : V → Option Nat) (parents : V → List V) (root : V)
    (unused : ∀ vertex, previous vertex ≠ some id) (fresh : previous root = none) (vertex : V) :
    (explore vertices id previous parents root).result vertex = some id ↔ FreshReach previous parents root vertex := by
  have valid := explore_valid vertices id previous parents root unused fresh
  have empty := explore_drains vertices unique covered id previous parents root unused fresh
  constructor
  · exact valid.origin vertex
  · intro reachable
    obtain ⟨path⟩ : Nonempty (Walk (FreshEdge previous parents) root vertex) := reachable
    have closed : ∀ {source target : V}, Walk (FreshEdge previous parents) source target →
        (explore vertices id previous parents root).result source = some id →
        (explore vertices id previous parents root).result target = some id := by
      intro source target route
      induction route with
      | nil => exact fun assigned => assigned
      | @cons source next target edge _ ih =>
        intro assigned
        have popped := (drained_members id _ valid.base empty source).mp assigned
        exact ih (valid.closed source popped next edge.1 edge.2.2)
    apply closed path
    exact (walk_run id parents vertices.length _).label_stable root id (by simp [push, initial, fresh])

end PetaProof.ReverseDfsStack

namespace PetaProof.ComponentNumbering

universe u
variable {V : Type u} [DecidableEq V]

/-- 外側の連番割当から、未使用idという第二DFSの入口条件を導く。 -/
theorem descend_reach_exact (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : State V) (valid : Invariant state) (root vertex : V) (fresh : state.result root = none) :
    (descend vertices.length parents state root).result vertex = some state.roots.length ↔
      ReverseDfsStack.FreshReach state.result parents root vertex := by
  apply ReverseDfsStack.explore_exact vertices unique covered state.roots.length state.result parents root
  · intro target same
    have bad := valid.bounded target state.roots.length same
    omega
  · exact fresh

end PetaProof.ComponentNumbering
