import PetaProof.CheckingRowAccounting

/-! 第一DFSの訪問済み書込と終了順の格納を、実際と同じ分岐で数える。 -/
namespace PetaProof.ForwardDfsStores

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

def discoverStores (state : State V) (vertex : V) : Nat := if state.seen vertex then 0 else 1

theorem discover_balance (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    (discover outgoing state vertex).total.length = state.total.length + discoverStores state vertex ∧
      (discover outgoing state vertex).finished.length = state.finished.length := by
  cases seen : state.seen vertex <;>
    simp [discover, discoverStores, seen, State.total, State.active, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 第1成分が訪問表書込、第2成分が終了順格納。 -/
def tickStores (state : State V) : Nat × Nat :=
  match state.stack with
  | [] => (0, 0)
  | frame :: _ => match frame.todo with
    | [] => (0, 1)
    | none :: _ => (0, 0)
    | some child :: _ => (discoverStores state child, 0)

theorem tick_balance (outgoing : V → List (Option V)) (state : State V) :
    (tick outgoing state).total.length = state.total.length + (tickStores state).1 ∧
      (tick outgoing state).finished.length = state.finished.length + (tickStores state).2 := by
  cases stack : state.stack with
  | nil => simp [tick, tickStores, stack]
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simp [tick, tickStores, stack, todo, retire, State.total, State.active, Nat.add_assoc]
    | cons target remaining =>
      cases target with
      | none => simp [tick, tickStores, stack, todo, trim, State.total, State.active]
      | some child =>
        have next := discover_balance outgoing (trim state) child
        simpa [tick, tickStores, stack, todo, trim, State.total, State.active, discoverStores] using next

def walkStores (outgoing : V → List (Option V)) : Nat → State V → Nat × Nat
  | 0, _ => (0, 0)
  | fuel + 1, state =>
    match state.stack with
    | [] => (0, 0)
    | _ :: _ =>
      let here := tickStores state
      let tail := walkStores outgoing fuel (tick outgoing state)
      (here.1 + tail.1, here.2 + tail.2)

theorem walk_balance (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    (walk outgoing fuel state).total.length = state.total.length + (walkStores outgoing fuel state).1 ∧
      (walk outgoing fuel state).finished.length = state.finished.length + (walkStores outgoing fuel state).2 := by
  induction fuel generalizing state with
  | zero => simp [walk, walkStores]
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp [walk, walkStores, stack]
    | cons frame rest =>
      have first := tick_balance outgoing state
      have tail := ih (tick outgoing state)
      simp only [walk, walkStores, stack]
      constructor <;> omega

def rootStores (vertices : List V) (outgoing : V → List (Option V)) (state : State V) (vertex : V) : Nat × Nat :=
  let inside := walkStores outgoing (capacity vertices outgoing) (discover outgoing state vertex)
  (discoverStores state vertex + inside.1, inside.2)

theorem root_balance (vertices : List V) (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    (root vertices outgoing state vertex).total.length = state.total.length + (rootStores vertices outgoing state vertex).1 ∧
      (root vertices outgoing state vertex).finished.length = state.finished.length + (rootStores vertices outgoing state vertex).2 := by
  have first := discover_balance outgoing state vertex
  have tail := walk_balance outgoing (capacity vertices outgoing) (discover outgoing state vertex)
  simp only [root, rootStores]
  constructor <;> omega

def forestStores (vertices : List V) (outgoing : V → List (Option V)) : List V → State V → Nat × Nat
  | [], _ => (0, 0)
  | vertex :: rest, state =>
    let first := rootStores vertices outgoing state vertex
    let tail := forestStores vertices outgoing rest (root vertices outgoing state vertex)
    (first.1 + tail.1, first.2 + tail.2)

theorem forest_balance (vertices : List V) (outgoing : V → List (Option V)) (roots : List V) (state : State V) :
    (forest vertices outgoing roots state).total.length = state.total.length + (forestStores vertices outgoing roots state).1 ∧
      (forest vertices outgoing roots state).finished.length = state.finished.length + (forestStores vertices outgoing roots state).2 := by
  induction roots generalizing state with
  | nil => simp [forest, forestStores]
  | cons vertex rest ih =>
    have first := root_balance vertices outgoing state vertex
    have tail := ih (root vertices outgoing state vertex)
    simp only [forest, forestStores]
    constructor <;> omega

theorem finish_stores (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) :
    forestStores vertices outgoing roots initial = (vertices.length, vertices.length) := by
  have balance := forest_balance vertices outgoing roots initial
  have length := (finish_perm vertices unique covered roots roots_cover outgoing).length_eq
  have empty := forest_drains vertices unique covered outgoing roots initial rfl
  have total : (forest vertices outgoing roots initial).total.length = vertices.length := by
    simpa only [State.total, State.active, empty, List.map_nil, List.append_nil, finish] using length
  have lengths : (forest vertices outgoing roots initial).finished.length = vertices.length := length
  change (forest vertices outgoing roots initial).total.length = 0 + (forestStores vertices outgoing roots initial).1 ∧
    (forest vertices outgoing roots initial).finished.length = 0 + (forestStores vertices outgoing roots initial).2 at balance
  simp only [Nat.zero_add] at balance
  apply Prod.ext <;> dsimp only <;> omega

end PetaProof.ForwardDfsStores
