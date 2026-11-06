import PetaProof.ComputedCheckingCore

/-! 第二DFSの全成分を通じたpop・逆辺項目の会計。未割当頂点の予算を使い回す。 -/
namespace PetaProof.ReverseDfsWork

universe u
variable {V : Type u} [DecidableEq V]

def weight (parents : V → List V) (vertex : V) : Nat := 1 + (parents vertex).length

def assigned (result : V → Option Nat) (vertex : V) : Bool := (result vertex).isSome

def credit (vertices : List V) (parents : V → List V) (result : V → Option Nat) : Nat :=
  DeletionQueue.credit (weight parents) (assigned result) vertices

def pendingWork (parents : V → List V) (state : ReverseDfsStack.State V) : Nat :=
  (state.pending.map (weight parents)).sum

def potential (vertices : List V) (parents : V → List V) (state : ReverseDfsStack.State V) : Nat :=
  credit vertices parents state.result + pendingWork parents state

theorem push_potential (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (id : Nat) (state : ReverseDfsStack.State V) (vertex : V) :
    potential vertices parents (ReverseDfsStack.push id state vertex) = potential vertices parents state := by
  cases found : state.result vertex with
  | some old => simp [ReverseDfsStack.push, found]
  | none =>
    have seen : assigned (fun other => if other = vertex then some id else state.result other) =
        markSeen (assigned state.result) vertex := by
      funext other
      by_cases same : other = vertex <;> simp [assigned, markSeen, same]
    have moved := DeletionQueue.credit_mark (weight parents) (assigned state.result) vertex vertices
      unique (covered vertex) (by simp [assigned, found])
    simp only [potential, credit, ReverseDfsStack.push, found, seen, pendingWork, List.map_cons, List.sum_cons]
    change DeletionQueue.credit (weight parents) (markSeen (assigned state.result) vertex) vertices +
      (weight parents vertex + (List.map (weight parents) state.pending).sum) = _
    omega

theorem scan_potential (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (id : Nat) (items : List V) (state : ReverseDfsStack.State V) :
    potential vertices parents (ReverseDfsStack.scan id items state) = potential vertices parents state := by
  induction items generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [ReverseDfsStack.scan, ih, push_potential vertices unique covered]

def visitWork (parents : V → List V) (state : ReverseDfsStack.State V) : Nat :=
  match state.pending with
  | [] => 0
  | vertex :: _ => weight parents vertex

theorem visit_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (id : Nat) (state : ReverseDfsStack.State V) :
    potential vertices parents (ReverseDfsStack.visit id parents state) + visitWork parents state =
      potential vertices parents state := by
  cases pending : state.pending with
  | nil => simp [ReverseDfsStack.visit, visitWork, pending]
  | cons vertex rest =>
    simp only [ReverseDfsStack.visit, pending, scan_potential vertices unique covered]
    simp [potential, credit, pendingWork, ReverseDfsStack.pop, pending, visitWork,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 空のvisitは0。同じ状態遷移をたどり、実popとその逆辺項目だけを数える。 -/
def walkWork (id : Nat) (parents : V → List V) : Nat → ReverseDfsStack.State V → Nat
  | 0, _ => 0
  | fuel + 1, state => visitWork parents state + walkWork id parents fuel (ReverseDfsStack.visit id parents state)

theorem walk_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (id fuel : Nat) (state : ReverseDfsStack.State V) :
    potential vertices parents (ReverseDfsStack.walk id parents fuel state) + walkWork id parents fuel state =
      potential vertices parents state := by
  induction fuel generalizing state with
  | zero => simp [ReverseDfsStack.walk, walkWork]
  | succ fuel ih =>
    have next := visit_balance vertices unique covered parents id state
    have tail := ih (ReverseDfsStack.visit id parents state)
    simp only [ReverseDfsStack.walk, walkWork]
    omega

def descendWork (vertices : List V) (parents : V → List V)
    (state : ComponentNumbering.State V) (root : V) : Nat :=
  walkWork state.roots.length parents vertices.length
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)

theorem descend_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    credit vertices parents (ComponentNumbering.descend vertices.length parents state root).result +
      descendWork vertices parents state root = credit vertices parents state.result := by
  have balance := walk_balance vertices unique covered parents state.roots.length vertices.length
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)
  have push := push_potential vertices unique covered parents state.roots.length
    (ReverseDfsStack.initial state.result) root
  have empty := ComponentNumbering.descend_drains vertices unique covered parents state valid root
  change (ComponentNumbering.descend vertices.length parents state root).pending = [] at empty
  change potential vertices parents (ComponentNumbering.descend vertices.length parents state root) +
    descendWork vertices parents state root = _ at balance
  rw [push] at balance
  simpa [potential, pendingWork, empty, ReverseDfsStack.initial] using balance

def stepWork (vertices : List V) (parents : V → List V)
    (state : ComponentNumbering.State V) (root : V) : Nat :=
  if state.result root = none then descendWork vertices parents state root else 0

theorem step_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    credit vertices parents (ComponentNumbering.step vertices.length parents state root).result +
      stepWork vertices parents state root = credit vertices parents state.result := by
  by_cases fresh : state.result root = none
  · simpa only [ComponentNumbering.step, stepWork, if_pos fresh] using
      descend_balance vertices unique covered parents state valid root
  · simp [ComponentNumbering.step, stepWork, fresh]

def passWork (vertices : List V) (parents : V → List V) : List V → ComponentNumbering.State V → Nat
  | [], _ => 0
  | root :: rest, state => stepWork vertices parents state root +
      passWork vertices parents rest (ComponentNumbering.step vertices.length parents state root)

theorem pass_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (roots : List V) (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) :
    credit vertices parents (ComponentNumbering.pass vertices.length parents roots state).result +
      passWork vertices parents roots state = credit vertices parents state.result := by
  induction roots generalizing state with
  | nil => simp [ComponentNumbering.pass, passWork]
  | cons root rest ih =>
    have first := step_balance vertices unique covered parents state valid root
    have tail := ih (ComponentNumbering.step vertices.length parents state root)
      (ComponentNumbering.step_preserves vertices.length parents state valid root)
    simp only [ComponentNumbering.pass, passWork]
    omega

omit [DecidableEq V] in
theorem weight_sum (vertices : List V) (parents : V → List V) :
    (vertices.map (weight parents)).sum =
      vertices.length + (vertices.map (fun vertex => (parents vertex).length)).sum := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, weight] at *
    omega

theorem finish_work (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) :
    passWork vertices parents roots ComponentNumbering.initial =
      vertices.length + (vertices.map (fun vertex => (parents vertex).length)).sum := by
  have balance := pass_balance vertices unique covered parents roots ComponentNumbering.initial
    ComponentNumbering.initial_invariant
  have all_assigned : ∀ vertex, assigned (ComponentNumbering.finish vertices roots parents).result vertex = true := by
    intro vertex
    obtain ⟨id, found⟩ := ComponentNumbering.finish_assigned vertices roots parents roots_cover vertex
    simp [assigned, found]
  have zero := ForwardDfs.credit_zero vertices (weight parents) _ all_assigned
  have start : credit vertices parents ComponentNumbering.initial.result =
      (vertices.map (weight parents)).sum := by
    change DeletionQueue.credit (weight parents) (fun _ => false) vertices = _
    exact DeletionQueue.initial_credit vertices (weight parents)
  change credit vertices parents (ComponentNumbering.finish vertices roots parents).result + _ = _ at balance
  change credit vertices parents (ComponentNumbering.finish vertices roots parents).result = 0 at zero
  rw [zero, start] at balance
  have sumWeight := weight_sum vertices parents
  omega

end PetaProof.ReverseDfsWork
