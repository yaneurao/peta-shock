import PetaProof.CheckingSlotGeneration

/-! 第一DFSの実tickを数え、終了popとカーソル更新へ分割してフレーム費用へ接続する。 -/
namespace PetaProof.ForwardFrameAccounting

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

/-- 未走査枠を一つ消費する分岐だけを数える。noneでも一回更新する。 -/
def tickTrim (state : State V) : Nat :=
  match state.stack with
  | [] => 0
  | frame :: _ => if frame.todo.isEmpty then 0 else 1

omit [DecidableEq V] in
theorem tick_partition (state : State V) (active : state.stack ≠ []) :
    tickTrim state + (ForwardDfsStores.tickStores state).2 = 1 := by
  cases stack : state.stack with
  | nil => exact False.elim (active stack)
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simp [tickTrim, ForwardDfsStores.tickStores, stack, todo]
    | cons target remaining =>
      cases target <;> simp [tickTrim, ForwardDfsStores.tickStores, stack, todo]

structure TickOperations where
  topReads : Nat
  remainingTests : Nat
  slotReads : Nat
  cursorWrites : Nat
  pops : Nat
  pushes : Nat

def TickOperations.total (ops : TickOperations) : Nat :=
  ops.topReads + ops.remainingTests + ops.slotReads + ops.cursorWrites + ops.pops + ops.pushes

def tickOperations (state : State V) : TickOperations :=
  match state.stack with
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | frame :: _ => match frame.todo with
    | [] => ⟨1, 1, 0, 0, 1, 0⟩
    | none :: _ => ⟨1, 1, 1, 1, 0, 0⟩
    | some child :: _ => ⟨1, 1, 1, 1, 0, ForwardDfsStores.discoverStores state child⟩

omit [DecidableEq V] in
theorem tick_operations_total (state : State V) (active : state.stack ≠ []) :
    (tickOperations state).total = 2 + 2 * tickTrim state +
      (ForwardDfsStores.tickStores state).1 + (ForwardDfsStores.tickStores state).2 := by
  cases stack : state.stack with
  | nil => exact False.elim (active stack)
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simp [tickOperations, TickOperations.total, tickTrim, ForwardDfsStores.tickStores, stack, todo]
    | cons target remaining =>
      cases target <;> simp [tickOperations, TickOperations.total, tickTrim, ForwardDfsStores.tickStores, stack, todo]

def walkTicks (outgoing : V → List (Option V)) : Nat → State V → Nat
  | 0, _ => 0
  | fuel + 1, state => match state.stack with
    | [] => 0
    | _ :: _ => 1 + walkTicks outgoing fuel (tick outgoing state)

def walkTrims (outgoing : V → List (Option V)) : Nat → State V → Nat
  | 0, _ => 0
  | fuel + 1, state => match state.stack with
    | [] => 0
    | _ :: _ => tickTrim state + walkTrims outgoing fuel (tick outgoing state)

theorem walk_partition (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    walkTrims outgoing fuel state + (ForwardDfsStores.walkStores outgoing fuel state).2 = walkTicks outgoing fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp [walkTrims, walkTicks, ForwardDfsStores.walkStores, stack]
    | cons frame rest =>
      have first := tick_partition state (by simp [stack])
      have tail := ih (tick outgoing state)
      simp only [walkTrims, walkTicks, ForwardDfsStores.walkStores, stack]
      omega

theorem walk_tick_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    budget vertices outgoing (walk outgoing fuel state) + walkTicks outgoing fuel state = budget vertices outgoing state := by
  induction fuel generalizing state with
  | zero => simp [walk, walkTicks]
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp [walk, walkTicks, stack]
    | cons frame rest =>
      have first := tick_budget vertices unique covered outgoing state (by simp [stack])
      have tail := ih (tick outgoing state)
      simp only [walk, walkTicks, stack]
      omega

def forestTicks (vertices : List V) (outgoing : V → List (Option V)) : List V → State V → Nat
  | [], _ => 0
  | vertex :: rest, state =>
    walkTicks outgoing (capacity vertices outgoing) (discover outgoing state vertex) +
      forestTicks vertices outgoing rest (root vertices outgoing state vertex)

def forestTrims (vertices : List V) (outgoing : V → List (Option V)) : List V → State V → Nat
  | [], _ => 0
  | vertex :: rest, state =>
    walkTrims outgoing (capacity vertices outgoing) (discover outgoing state vertex) +
      forestTrims vertices outgoing rest (root vertices outgoing state vertex)

theorem forest_partition (vertices : List V) (outgoing : V → List (Option V)) (roots : List V) (state : State V) :
    forestTrims vertices outgoing roots state + (ForwardDfsStores.forestStores vertices outgoing roots state).2 =
      forestTicks vertices outgoing roots state := by
  induction roots generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    have first := walk_partition outgoing (capacity vertices outgoing) (discover outgoing state vertex)
    have tail := ih (root vertices outgoing state vertex)
    simp only [forestTrims, forestTicks, ForwardDfsStores.forestStores, ForwardDfsStores.rootStores]
    omega

theorem forest_tick_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V) (state : State V) :
    budget vertices outgoing (forest vertices outgoing roots state) + forestTicks vertices outgoing roots state =
      budget vertices outgoing state := by
  induction roots generalizing state with
  | nil => simp [forest, forestTicks]
  | cons vertex rest ih =>
    have first := walk_tick_balance vertices unique covered outgoing (capacity vertices outgoing) (discover outgoing state vertex)
    rw [discover_budget vertices unique covered outgoing] at first
    have tail := ih (root vertices outgoing state vertex)
    change budget vertices outgoing (root vertices outgoing state vertex) + _ = _ at first
    simp only [forest, forestTicks]
    omega

theorem finish_ticks (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) :
    forestTicks vertices outgoing roots initial = vertices.length +
      (vertices.map (fun vertex => (outgoing vertex).length)).sum := by
  have balance := forest_tick_balance vertices unique covered outgoing roots initial
  have empty := forest_drains vertices unique covered outgoing roots initial rfl
  have all_seen : ∀ vertex, (forest vertices outgoing roots initial).seen vertex = true := by
    intro vertex
    exact forest_member_seen vertices outgoing roots initial vertex (roots_cover vertex)
  have zero : budget vertices outgoing (forest vertices outgoing roots initial) = 0 := by
    simp [budget, empty, work, credit_zero vertices _ _ all_seen]
  have start : budget vertices outgoing (initial : State V) = capacity vertices outgoing := by
    simp [budget, initial, work, DeletionQueue.initial_credit, capacity]
  rw [zero, start, capacity_eq] at balance
  omega

theorem finish_trims (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) :
    forestTrims vertices outgoing roots initial = (vertices.map (fun vertex => (outgoing vertex).length)).sum := by
  have partition := forest_partition vertices outgoing roots initial
  rw [ForwardDfsStores.finish_stores vertices unique covered outgoing roots roots_cover,
    finish_ticks vertices unique covered outgoing roots roots_cover] at partition
  dsimp only at partition
  omega

/-- push/pop、非空tickの先頭参照と残列検査、枠読出しとカーソル更新を別イベントとする。 -/
def frameWork (vertices : List V) (outgoing : V → List (Option V)) (roots : List V) : Nat :=
  let stores := ForwardDfsStores.forestStores vertices outgoing roots initial
  stores.1 + stores.2 + 2 * forestTicks vertices outgoing roots initial +
    2 * forestTrims vertices outgoing roots initial

theorem finish_frame_work (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V)) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) :
    frameWork vertices outgoing roots = 4 * vertices.length +
      4 * (vertices.map (fun vertex => (outgoing vertex).length)).sum := by
  unfold frameWork
  rw [ForwardDfsStores.finish_stores vertices unique covered outgoing roots roots_cover,
    finish_ticks vertices unique covered outgoing roots roots_cover,
    finish_trims vertices unique covered outgoing roots roots_cover]
  dsimp only
  omega

end PetaProof.ForwardFrameAccounting
