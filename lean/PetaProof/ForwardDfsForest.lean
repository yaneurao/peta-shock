import PetaProof.ForwardDfsTermination
import PetaProof.ComponentNumbering

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

def root (vertices : List V) (outgoing : V → List (Option V)) (state : State V) (vertex : V) : State V :=
  walk outgoing (capacity vertices outgoing) (discover outgoing state vertex)

def forest (vertices : List V) (outgoing : V → List (Option V)) : List V → State V → State V
  | [], state => state
  | vertex :: rest, state => forest vertices outgoing rest (root vertices outgoing state vertex)

theorem root_preserves (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (valid : Invariant state) (vertex : V) : Invariant (root vertices outgoing state vertex) :=
  walk_preserves outgoing _ _ (discover_preserves outgoing state valid vertex)

theorem root_drains (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    (state : State V) (empty : state.stack = []) (vertex : V) :
    (root vertices outgoing state vertex).stack = [] := by
  apply walk_drains vertices unique covered outgoing
  rw [discover_budget vertices unique covered outgoing]
  simpa [budget, empty, work, capacity] using
    DeletionQueue.credit_le_total vertices (fun vertex => (outgoing vertex).length + 1) state.seen

theorem root_seen_at (vertices : List V) (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    (root vertices outgoing state vertex).seen vertex = true :=
  walk_seen_stable outgoing _ _ vertex (discover_seen_at outgoing state vertex)

theorem root_seen_stable (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (target vertex : V) (seen : state.seen vertex = true) :
    (root vertices outgoing state target).seen vertex = true :=
  walk_seen_stable outgoing _ _ vertex (discover_seen_stable outgoing state target vertex seen)

theorem forest_preserves (vertices : List V) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (valid : Invariant state) : Invariant (forest vertices outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact valid
  | cons vertex rest ih => exact ih _ (root_preserves vertices outgoing state valid vertex)

theorem forest_drains (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (empty : state.stack = []) : (forest vertices outgoing roots state).stack = [] := by
  induction roots generalizing state with
  | nil => exact empty
  | cons vertex rest ih => exact ih _ (root_drains vertices unique covered outgoing state empty vertex)

theorem forest_seen_stable (vertices : List V) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (vertex : V) (seen : state.seen vertex = true) :
    (forest vertices outgoing roots state).seen vertex = true := by
  induction roots generalizing state with
  | nil => exact seen
  | cons target rest ih => exact ih _ (root_seen_stable vertices outgoing state target vertex seen)

theorem forest_member_seen (vertices : List V) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (vertex : V) (member : vertex ∈ roots) :
    (forest vertices outgoing roots state).seen vertex = true := by
  induction roots generalizing state with
  | nil => cases member
  | cons target rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst vertex
      exact forest_seen_stable vertices outgoing rest _ target (root_seen_at vertices outgoing state target)
    · exact ih _ later

def finish (vertices roots : List V) (outgoing : V → List (Option V)) : State V :=
  forest vertices outgoing roots initial

theorem finish_unique (vertices roots : List V) (outgoing : V → List (Option V)) :
    (finish vertices roots outgoing).finished.Nodup :=
  (List.pairwise_append.mp (forest_preserves vertices outgoing roots initial initial_invariant).unique).1

theorem finish_covers (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V)) (vertex : V) :
    vertex ∈ (finish vertices roots outgoing).finished := by
  have seen := forest_member_seen vertices outgoing roots initial vertex (roots_cover vertex)
  have valid := forest_preserves vertices outgoing roots initial initial_invariant
  have empty := forest_drains vertices unique covered outgoing roots initial rfl
  have member := (valid.covers vertex).mp seen
  simpa [State.total, State.active, empty] using member

theorem finish_perm (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V)) :
    (finish vertices roots outgoing).finished.Perm vertices := by
  apply ReverseDfsStack.nodup_perm_of_mem _ _ (finish_unique vertices roots outgoing) unique
  intro vertex
  simp only [finish_covers vertices unique covered roots roots_cover outgoing vertex, covered vertex]

/-- 第一DFSから得た逆終了順の網羅性を、第二DFSの入口条件へ渡す。 -/
def order (vertices roots : List V) (outgoing : V → List (Option V)) : List V :=
  (finish vertices roots outgoing).finished.reverse

theorem order_covers (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V)) (vertex : V) :
    vertex ∈ order vertices roots outgoing := by
  simpa [order] using finish_covers vertices unique covered roots roots_cover outgoing vertex

theorem second_pass_assigned (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (vertex : V) :
    ∃ id, (ComponentNumbering.finish vertices (order vertices roots outgoing) parents).result vertex = some id :=
  ComponentNumbering.finish_assigned vertices _ parents
    (order_covers vertices unique covered roots roots_cover outgoing) vertex

theorem second_pass_id_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (vertex : V) :
    ComponentNumbering.component vertices (order vertices roots outgoing) parents vertex < vertices.length :=
  ComponentNumbering.component_bound vertices unique covered _
    (order_covers vertices unique covered roots roots_cover outgoing) parents vertex

/-- 根の検査は別に数え、DFS内部の非空tickだけを合計する実行記録。 -/
inductive ForestRun (vertices : List V) (outgoing : V → List (Option V)) :
    List V → State V → Nat → State V → Prop
  | done (state : State V) : ForestRun vertices outgoing [] state 0 state
  | next {state last : State V} {steps restSteps : Nat} {rest : List V} (vertex : V) :
      Run outgoing (discover outgoing state vertex) steps (root vertices outgoing state vertex) →
      ForestRun vertices outgoing rest (root vertices outgoing state vertex) restSteps last →
      ForestRun vertices outgoing (vertex :: rest) state (steps + restSteps) last

theorem forest_run (vertices : List V) (outgoing : V → List (Option V)) (roots : List V) (state : State V) :
    ∃ steps, ForestRun vertices outgoing roots state steps (forest vertices outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact ⟨0, .done state⟩
  | cons vertex rest ih =>
    obtain ⟨steps, first⟩ := walk_run outgoing (capacity vertices outgoing) (discover outgoing state vertex)
    obtain ⟨restSteps, tail⟩ := ih (root vertices outgoing state vertex)
    exact ⟨steps + restSteps, .next vertex first tail⟩

theorem forest_budget (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    {roots : List V} {state last : State V} {steps : Nat}
    (run : ForestRun vertices outgoing roots state steps last) :
    budget vertices outgoing last + steps = budget vertices outgoing state := by
  induction run with
  | done => simp
  | next vertex first _ ih =>
    have spent := run_budget vertices unique covered outgoing first
    rw [discover_budget vertices unique covered outgoing] at spent
    omega

omit [DecidableEq V] in
theorem credit_zero (vertices : List V) (weight : V → Nat) (seen : V → Bool)
    (all_seen : ∀ vertex, seen vertex = true) : DeletionQueue.credit weight seen vertices = 0 := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih => simp [DeletionQueue.credit, all_seen vertex, ih]

omit [DecidableEq V] in
theorem capacity_eq (vertices : List V) (outgoing : V → List (Option V)) :
    capacity vertices outgoing = vertices.length + (vertices.map (fun vertex => (outgoing vertex).length)).sum := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
    simp only [capacity, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- 全頂点を処理した実行の非空tickは、出辺枠数Mと頂点数Nの和に正確に一致する。 -/
theorem finish_work (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V)) :
    ForestRun vertices outgoing roots initial
      (vertices.length + (vertices.map (fun vertex => (outgoing vertex).length)).sum)
      (finish vertices roots outgoing) := by
  obtain ⟨steps, run⟩ := forest_run vertices outgoing roots initial
  have balance := forest_budget vertices unique covered outgoing run
  have empty := forest_drains vertices unique covered outgoing roots initial rfl
  have all_seen : ∀ vertex, (forest vertices outgoing roots initial).seen vertex = true := by
    intro vertex
    exact forest_member_seen vertices outgoing roots initial vertex (roots_cover vertex)
  have final_zero : budget vertices outgoing (forest vertices outgoing roots initial) = 0 := by
    simp [budget, empty, work, credit_zero vertices _ _ all_seen]
  have start : budget vertices outgoing (initial : State V) = capacity vertices outgoing := by
    simp [budget, initial, work, DeletionQueue.initial_credit, capacity]
  rw [final_zero, start, capacity_eq] at balance
  simp only [Nat.zero_add] at balance
  exact balance ▸ run

end PetaProof.ForwardDfs
