import PetaProof.ForwardDfs

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

/-- 未走査の出辺枠と、その頂点を終了順へ移す一操作を数える。 -/
def work : List (Frame V) → Nat
  | [] => 0
  | frame :: rest => frame.todo.length + 1 + work rest

def capacity (vertices : List V) (outgoing : V → List (Option V)) : Nat :=
  (vertices.map (fun vertex => (outgoing vertex).length + 1)).sum

def budget (vertices : List V) (outgoing : V → List (Option V)) (state : State V) : Nat :=
  DeletionQueue.credit (fun vertex => (outgoing vertex).length + 1) state.seen vertices + work state.stack

/-- 発見時に未訪問側の予算をスタックへ移すだけなので、総量は変わらない。 -/
theorem discover_budget (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    (state : State V) (vertex : V) :
    budget vertices outgoing (discover outgoing state vertex) = budget vertices outgoing state := by
  cases seen : state.seen vertex with
  | true => simp [discover, seen]
  | false =>
    have moved := DeletionQueue.credit_mark (fun vertex => (outgoing vertex).length + 1)
      state.seen vertex vertices unique (covered vertex) seen
    dsimp only at moved
    simp only [discover, seen, Bool.false_eq_true, ite_false, budget, work]
    omega

theorem tick_budget (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    (state : State V) (active : state.stack ≠ []) :
    budget vertices outgoing (tick outgoing state) + 1 = budget vertices outgoing state := by
  cases stack : state.stack with
  | nil => exact False.elim (active stack)
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simp [tick, stack, todo, retire, budget, work, Nat.add_assoc] <;> omega
    | cons target remaining =>
      have trimmed : budget vertices outgoing (trim state) + 1 = budget vertices outgoing state := by
        simp [trim, stack, budget, work, todo, Nat.add_assoc] <;> omega
      cases target with
      | none => simpa [tick, stack, todo] using trimmed
      | some child =>
        simpa only [tick, stack, todo, discover_budget vertices unique covered outgoing] using trimmed

/-- 空スタックなら直ちに止まる。fuelは停止証明用の上界である。 -/
def walk (outgoing : V → List (Option V)) : Nat → State V → State V
  | 0, state => state
  | fuel + 1, state =>
    match state.stack with
    | [] => state
    | _ :: _ => walk outgoing fuel (tick outgoing state)

theorem walk_preserves (outgoing : V → List (Option V)) (fuel : Nat) (state : State V)
    (valid : Invariant state) : Invariant (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa [walk, stack] using valid
    | cons frame rest => simpa only [walk, stack] using ih _ (tick_preserves outgoing state valid)

theorem walk_seen_stable (outgoing : V → List (Option V)) (fuel : Nat) (state : State V)
    (vertex : V) (seen : state.seen vertex = true) : (walk outgoing fuel state).seen vertex = true := by
  induction fuel generalizing state with
  | zero => exact seen
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa [walk, stack] using seen
    | cons frame rest => simpa only [walk, stack] using ih _ (tick_seen_stable outgoing state vertex seen)

theorem walk_drains (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    (fuel : Nat) (state : State V) (enough : budget vertices outgoing state ≤ fuel) :
    (walk outgoing fuel state).stack = [] := by
  induction fuel generalizing state with
  | zero =>
    change state.stack = []
    by_cases empty : state.stack = []
    · exact empty
    · have decrease := tick_budget vertices unique covered outgoing state empty
      omega
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp [walk, stack]
    | cons frame rest =>
      have decrease := tick_budget vertices unique covered outgoing state (by simp [stack])
      simpa only [walk, stack] using ih (tick outgoing state) (by omega)

/-- 実際に行った非空tickだけを数え、停止後の恒等操作は数えない。 -/
inductive Run (outgoing : V → List (Option V)) : State V → Nat → State V → Prop
  | done (state : State V) : Run outgoing state 0 state
  | next {state last : State V} {steps : Nat} : state.stack ≠ [] →
      Run outgoing (tick outgoing state) steps last → Run outgoing state (steps + 1) last

theorem run_budget (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (outgoing : V → List (Option V))
    {state last : State V} {steps : Nat} (run : Run outgoing state steps last) :
    budget vertices outgoing last + steps = budget vertices outgoing state := by
  induction run with
  | done => simp
  | next active _ ih =>
    have decrease := tick_budget vertices unique covered outgoing _ active
    omega

theorem walk_run (outgoing : V → List (Option V)) (fuel : Nat) (state : State V) :
    ∃ steps, Run outgoing state steps (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact ⟨0, .done state⟩
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => exact ⟨0, by simpa [walk, stack] using Run.done (outgoing := outgoing) state⟩
    | cons frame rest =>
      obtain ⟨steps, run⟩ := ih (tick outgoing state)
      exact ⟨steps + 1, by simpa only [walk, stack] using Run.next (by simp [stack]) run⟩

end PetaProof.ForwardDfs
