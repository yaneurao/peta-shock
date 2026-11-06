import PetaProof.DfsStorageAccounting

/-! 第一DFSの未訪問発見に任意の非負費用を課し、出辺枠生成の再実行を数えない。 -/
namespace PetaProof.ForwardDiscoveryCharge

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

def credit (vertices : List V) (charge : V → Nat) (state : State V) : Nat :=
  DeletionQueue.credit charge state.seen vertices

def discoverCharge (charge : V → Nat) (state : State V) (vertex : V) : Nat :=
  if state.seen vertex then 0 else charge vertex

theorem discover_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    credit vertices charge (discover outgoing state vertex) + discoverCharge charge state vertex =
      credit vertices charge state := by
  cases seen : state.seen vertex with
  | true => simp [discover, discoverCharge, seen]
  | false =>
    have spent := DeletionQueue.credit_mark charge state.seen vertex vertices unique (covered vertex) seen
    simpa only [credit, discover, discoverCharge, seen, Bool.false_eq_true, ite_false] using spent

def tickCharge (charge : V → Nat) (state : State V) : Nat :=
  match state.stack with
  | [] => 0
  | frame :: _ => match frame.todo with
    | some child :: _ => discoverCharge charge state child
    | _ => 0

theorem tick_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (outgoing : V → List (Option V)) (state : State V) :
    credit vertices charge (tick outgoing state) + tickCharge charge state = credit vertices charge state := by
  cases stack : state.stack with
  | nil => simp [tick, tickCharge, stack]
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simp [tick, tickCharge, stack, todo, retire, credit]
    | cons target remaining =>
      cases target with
      | none => simp [tick, tickCharge, stack, todo, trim, credit]
      | some child =>
        have spent := discover_balance vertices unique covered charge outgoing (trim state) child
        simpa only [tick, tickCharge, stack, todo, trim, credit, discoverCharge] using spent

def walkCharge (charge : V → Nat) (outgoing : V → List (Option V)) : Nat → State V → Nat
  | 0, _ => 0
  | fuel + 1, state =>
    match state.stack with
    | [] => 0
    | _ :: _ => tickCharge charge state + walkCharge charge outgoing fuel (tick outgoing state)

theorem walk_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    credit vertices charge (walk outgoing fuel state) + walkCharge charge outgoing fuel state = credit vertices charge state := by
  induction fuel generalizing state with
  | zero => simp [walk, walkCharge]
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp [walk, walkCharge, stack]
    | cons frame rest =>
      have first := tick_balance vertices unique covered charge outgoing state
      have tail := ih (tick outgoing state)
      simp only [walk, walkCharge, stack]
      omega

def rootCharge (vertices : List V) (charge : V → Nat) (outgoing : V → List (Option V)) (state : State V) (vertex : V) : Nat :=
  discoverCharge charge state vertex +
    walkCharge charge outgoing (capacity vertices outgoing) (discover outgoing state vertex)

theorem root_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    credit vertices charge (root vertices outgoing state vertex) + rootCharge vertices charge outgoing state vertex =
      credit vertices charge state := by
  have first := discover_balance vertices unique covered charge outgoing state vertex
  have tail := walk_balance vertices unique covered charge outgoing (capacity vertices outgoing) (discover outgoing state vertex)
  simp only [root, rootCharge]
  omega

def forestCharge (vertices : List V) (charge : V → Nat) (outgoing : V → List (Option V)) : List V → State V → Nat
  | [], _ => 0
  | vertex :: rest, state => rootCharge vertices charge outgoing state vertex +
      forestCharge vertices charge outgoing rest (root vertices outgoing state vertex)

theorem forest_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (outgoing : V → List (Option V)) (roots : List V) (state : State V) :
    credit vertices charge (forest vertices outgoing roots state) + forestCharge vertices charge outgoing roots state =
      credit vertices charge state := by
  induction roots generalizing state with
  | nil => simp [forest, forestCharge]
  | cons vertex rest ih =>
    have first := root_balance vertices unique covered charge outgoing state vertex
    have tail := ih (root vertices outgoing state vertex)
    simp only [forest, forestCharge]
    omega

theorem finish_charge (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat) (outgoing : V → List (Option V))
    (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) :
    forestCharge vertices charge outgoing roots initial = (vertices.map charge).sum := by
  have balance := forest_balance vertices unique covered charge outgoing roots initial
  have all_seen : ∀ vertex, (forest vertices outgoing roots initial).seen vertex = true := by
    intro vertex
    exact forest_member_seen vertices outgoing roots initial vertex (roots_cover vertex)
  have zero := credit_zero vertices charge _ all_seen
  change credit vertices charge (forest vertices outgoing roots initial) = 0 at zero
  have start : credit vertices charge (initial : State V) = (vertices.map charge).sum :=
    DeletionQueue.initial_credit vertices charge
  rw [zero, start] at balance
  omega

end PetaProof.ForwardDiscoveryCharge
