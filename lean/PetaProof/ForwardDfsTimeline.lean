import PetaProof.ForwardDfsActivePath

/-!
第一DFSの時間順の証明用実行列。根の投入は空スタックでだけ許す。
途中のfinished列が後のfinished列のprefixであることを実操作へ接続する。
-/
namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

inductive Event (outgoing : V → List (Option V)) : State V → State V → Prop
  | advance (state : State V) : Event outgoing state (tick outgoing state)
  | seed (state : State V) (vertex : V) : state.stack = [] → Event outgoing state (discover outgoing state vertex)

inductive Timeline (outgoing : V → List (Option V)) : State V → State V → Prop
  | done (state : State V) : Timeline outgoing state state
  | next {state middle last : State V} : Event outgoing state middle →
      Timeline outgoing middle last → Timeline outgoing state last

theorem Timeline.trans {outgoing : V → List (Option V)} {state middle last : State V}
    (first : Timeline outgoing state middle) (second : Timeline outgoing middle last) :
    Timeline outgoing state last := by
  induction first with
  | done => exact second
  | next event _ ih => exact .next event (ih second)

theorem Event.scanned {outgoing : V → List (Option V)} {state next : State V}
    (event : Event outgoing state next) (scans : ScanInvariant outgoing state) : ScanInvariant outgoing next := by
  cases event with
  | advance => exact tick_scanned outgoing state scans
  | seed vertex _ => exact discover_scanned outgoing state scans vertex

theorem Event.path {outgoing : V → List (Option V)} {state next : State V}
    (event : Event outgoing state next) (scans : ScanInvariant outgoing state)
    (path : ActivePath outgoing state) : ActivePath outgoing next := by
  cases event with
  | advance => exact tick_active_path outgoing state scans path
  | seed vertex empty =>
    apply discover_active_path outgoing state path vertex
    intro ancestor member
    simp [State.active, empty] at member

theorem Timeline.scanned {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (scans : ScanInvariant outgoing state) : ScanInvariant outgoing last := by
  induction run with
  | done => exact scans
  | next event _ ih => exact ih (event.scanned scans)

theorem Timeline.path {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (scans : ScanInvariant outgoing state)
    (path : ActivePath outgoing state) : ActivePath outgoing last := by
  induction run with
  | done => exact path
  | next event _ ih => exact ih (event.scanned scans) (event.path scans path)

theorem Event.seen_stable {outgoing : V → List (Option V)} {state next : State V}
    (event : Event outgoing state next) (vertex : V) (seen : state.seen vertex = true) : next.seen vertex = true := by
  cases event with
  | advance => exact tick_seen_stable outgoing state vertex seen
  | seed target _ => exact discover_seen_stable outgoing state target vertex seen

theorem Timeline.seen_stable {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (vertex : V) (seen : state.seen vertex = true) : last.seen vertex = true := by
  induction run with
  | done => exact seen
  | next event _ ih => exact ih (event.seen_stable vertex seen)

theorem tick_finished_extends (outgoing : V → List (Option V)) (state : State V) :
    ∃ added, (tick outgoing state).finished = state.finished ++ added := by
  cases stack : state.stack with
  | nil => exact ⟨[], by simp [tick, stack]⟩
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => exact ⟨[frame.vertex], by simp [tick, stack, todo, retire]⟩
    | cons target remaining =>
      cases target with
      | none => exact ⟨[], by simp [tick, stack, todo, trim_finished]⟩
      | some child => exact ⟨[], by simp [tick, stack, todo, discover_finished, trim_finished]⟩

theorem Event.finished_extends {outgoing : V → List (Option V)} {state next : State V}
    (event : Event outgoing state next) : ∃ added, next.finished = state.finished ++ added := by
  cases event with
  | advance => exact tick_finished_extends outgoing state
  | seed target _ => exact ⟨[], by simp [discover_finished]⟩

theorem Timeline.finished_extends {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) : ∃ added, last.finished = state.finished ++ added := by
  induction run with
  | done => exact ⟨[], by simp⟩
  | next event _ ih =>
    obtain ⟨first, first_eq⟩ := event.finished_extends
    obtain ⟨rest, rest_eq⟩ := ih
    exact ⟨first ++ rest, by rw [rest_eq, first_eq, List.append_assoc]⟩

theorem Run.timeline {outgoing : V → List (Option V)} {state last : State V} {steps : Nat}
    (run : Run outgoing state steps last) : Timeline outgoing state last := by
  induction run with
  | done => exact .done _
  | next _ _ ih => exact .next (.advance _) ih

theorem walk_timeline (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    Timeline outgoing state (walk outgoing fuel state) := by
  obtain ⟨_, run⟩ := walk_run outgoing fuel state
  exact run.timeline

theorem root_timeline (vertices : List V) (outgoing : V → List (Option V)) (state : State V)
    (empty : state.stack = []) (vertex : V) : Timeline outgoing state (root vertices outgoing state vertex) :=
  .next (.seed state vertex empty) (walk_timeline outgoing _ _)

theorem forest_timeline (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (state : State V) (empty : state.stack = []) : Timeline outgoing state (forest vertices outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact .done state
  | cons vertex rest ih =>
    exact (root_timeline vertices outgoing state empty vertex).trans
      (ih _ (root_drains vertices unique covered outgoing state empty vertex))

theorem finish_timeline (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V) :
    Timeline outgoing initial (finish vertices roots outgoing) :=
  forest_timeline vertices unique covered outgoing roots initial rfl

end PetaProof.ForwardDfs
