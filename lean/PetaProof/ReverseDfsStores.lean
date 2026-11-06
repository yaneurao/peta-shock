import PetaProof.ForwardDfsStores

/-! 第二DFSの番号書込と成分代表格納を、それぞれの成功ガードで数える。 -/
namespace PetaProof.ReverseDfsStores

universe u
variable {V : Type u} [DecidableEq V]

def pushStores (state : ReverseDfsStack.State V) (vertex : V) : Nat :=
  if state.result vertex = none then 1 else 0

def unused (vertices : List V) (result : V → Option Nat) : Nat :=
  ReverseVisitCharge.credit vertices (fun _ => 1) result

theorem push_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (state : ReverseDfsStack.State V) (vertex : V) :
    unused vertices (ReverseDfsStack.push id state vertex).result + pushStores state vertex =
      unused vertices state.result := by
  cases found : state.result vertex with
  | some old => simp [ReverseDfsStack.push, pushStores, found]
  | none =>
    have marked : ReverseDfsWork.assigned (fun other => if other = vertex then some id else state.result other) =
        markSeen (ReverseDfsWork.assigned state.result) vertex := by
      funext other
      by_cases same : other = vertex <;> simp [ReverseDfsWork.assigned, markSeen, same]
    have decrease := DeletionQueue.credit_mark (fun _ => 1) (ReverseDfsWork.assigned state.result)
      vertex vertices unique (covered vertex) (by simp [ReverseDfsWork.assigned, found])
    simpa only [unused, ReverseVisitCharge.credit, ReverseDfsStack.push, found, marked,
      pushStores, if_pos rfl] using decrease

def scanStores (id : Nat) : List V → ReverseDfsStack.State V → Nat
  | [], _ => 0
  | vertex :: rest, state => pushStores state vertex + scanStores id rest (ReverseDfsStack.push id state vertex)

theorem scan_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (items : List V) (state : ReverseDfsStack.State V) :
    unused vertices (ReverseDfsStack.scan id items state).result + scanStores id items state = unused vertices state.result := by
  induction items generalizing state with
  | nil => simp [ReverseDfsStack.scan, scanStores]
  | cons vertex rest ih =>
    have first := push_balance vertices unique covered id state vertex
    have tail := ih (ReverseDfsStack.push id state vertex)
    simp only [ReverseDfsStack.scan, scanStores]
    omega

def visitStores (id : Nat) (parents : V → List V) (state : ReverseDfsStack.State V) : Nat :=
  match state.pending with
  | [] => 0
  | vertex :: _ => scanStores id (parents vertex) (ReverseDfsStack.pop state)

theorem visit_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (parents : V → List V) (state : ReverseDfsStack.State V) :
    unused vertices (ReverseDfsStack.visit id parents state).result + visitStores id parents state = unused vertices state.result := by
  cases pending : state.pending with
  | nil => simp [ReverseDfsStack.visit, visitStores, pending]
  | cons vertex rest =>
    have scanned := scan_balance vertices unique covered id (parents vertex) (ReverseDfsStack.pop state)
    simpa only [ReverseDfsStack.visit, visitStores, pending, ReverseDfsStack.pop_result] using scanned

def walkStores (id : Nat) (parents : V → List V) : Nat → ReverseDfsStack.State V → Nat
  | 0, _ => 0
  | fuel + 1, state => visitStores id parents state + walkStores id parents fuel (ReverseDfsStack.visit id parents state)

theorem walk_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (id : Nat) (parents : V → List V) (fuel : Nat) (state : ReverseDfsStack.State V) :
    unused vertices (ReverseDfsStack.walk id parents fuel state).result + walkStores id parents fuel state = unused vertices state.result := by
  induction fuel generalizing state with
  | zero => simp [ReverseDfsStack.walk, walkStores]
  | succ fuel ih =>
    have first := visit_balance vertices unique covered id parents state
    have tail := ih (ReverseDfsStack.visit id parents state)
    simp only [ReverseDfsStack.walk, walkStores]
    omega

def descendStores (vertices : List V) (parents : V → List V) (state : ComponentNumbering.State V) (root : V) : Nat :=
  let before := ReverseDfsStack.initial state.result
  pushStores before root + walkStores state.roots.length parents vertices.length (ReverseDfsStack.push state.roots.length before root)

theorem descend_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V) (state : ComponentNumbering.State V) (root : V) :
    unused vertices (ComponentNumbering.descend vertices.length parents state root).result +
      descendStores vertices parents state root = unused vertices state.result := by
  have first := push_balance vertices unique covered state.roots.length (ReverseDfsStack.initial state.result) root
  have tail := walk_balance vertices unique covered state.roots.length parents vertices.length
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)
  change _ + _ = unused vertices state.result at first
  simp only [ComponentNumbering.descend, descendStores]
  omega

/-- 第1成分は番号書込、第2成分は新しい成分代表の格納。 -/
def stepStores (vertices : List V) (parents : V → List V) (state : ComponentNumbering.State V) (root : V) : Nat × Nat :=
  if state.result root = none then (descendStores vertices parents state root, 1) else (0, 0)

theorem step_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V) (state : ComponentNumbering.State V) (root : V) :
    unused vertices (ComponentNumbering.step vertices.length parents state root).result +
        (stepStores vertices parents state root).1 = unused vertices state.result ∧
      (ComponentNumbering.step vertices.length parents state root).roots.length =
        state.roots.length + (stepStores vertices parents state root).2 := by
  by_cases fresh : state.result root = none
  · have balance := descend_balance vertices unique covered parents state root
    simp only [ComponentNumbering.step, stepStores, if_pos fresh, List.length_append, List.length_singleton]
    exact ⟨balance, trivial⟩
  · simp [ComponentNumbering.step, stepStores, fresh]

def passStores (vertices : List V) (parents : V → List V) : List V → ComponentNumbering.State V → Nat × Nat
  | [], _ => (0, 0)
  | root :: rest, state =>
    let first := stepStores vertices parents state root
    let tail := passStores vertices parents rest (ComponentNumbering.step vertices.length parents state root)
    (first.1 + tail.1, first.2 + tail.2)

theorem pass_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V) (roots : List V) (state : ComponentNumbering.State V) :
    unused vertices (ComponentNumbering.pass vertices.length parents roots state).result +
        (passStores vertices parents roots state).1 = unused vertices state.result ∧
      (ComponentNumbering.pass vertices.length parents roots state).roots.length =
        state.roots.length + (passStores vertices parents roots state).2 := by
  induction roots generalizing state with
  | nil => simp [ComponentNumbering.pass, passStores]
  | cons root rest ih =>
    have first := step_balance vertices unique covered parents state root
    have tail := ih (ComponentNumbering.step vertices.length parents state root)
    simp only [ComponentNumbering.pass, passStores]
    constructor <;> omega

theorem finish_stores (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) :
    (passStores vertices parents roots ComponentNumbering.initial).1 = vertices.length ∧
      (passStores vertices parents roots ComponentNumbering.initial).2 =
        (ComponentNumbering.finish vertices roots parents).roots.length ∧
      (passStores vertices parents roots ComponentNumbering.initial).2 ≤ vertices.length := by
  have balance := pass_balance vertices unique covered parents roots ComponentNumbering.initial
  have assigned : ∀ vertex, ReverseDfsWork.assigned (ComponentNumbering.finish vertices roots parents).result vertex = true := by
    intro vertex
    obtain ⟨id, found⟩ := ComponentNumbering.finish_assigned vertices roots parents roots_cover vertex
    simp [ReverseDfsWork.assigned, found]
  have zero := ForwardDfs.credit_zero vertices (fun _ => 1) _ assigned
  change unused vertices (ComponentNumbering.finish vertices roots parents).result = 0 at zero
  have start : unused vertices ComponentNumbering.initial.result = vertices.length := by
    change DeletionQueue.credit (fun _ => 1) (fun _ => false) vertices = _
    rw [DeletionQueue.initial_credit]
    have generic : ∀ items : List V, (items.map (fun _ => 1)).sum = items.length := by
      intro items
      induction items with
      | nil => rfl
      | cons head rest ih => simp [ih, Nat.add_comm]
    exact generic vertices
  have bounded := ComponentNumbering.roots_bound vertices unique covered _ (ComponentNumbering.finish_invariant vertices roots parents)
  change unused vertices (ComponentNumbering.finish vertices roots parents).result +
      (passStores vertices parents roots ComponentNumbering.initial).1 = _ ∧
    (ComponentNumbering.finish vertices roots parents).roots.length =
      0 + (passStores vertices parents roots ComponentNumbering.initial).2 at balance
  rw [zero, start] at balance
  constructor
  · omega
  · constructor <;> omega

end PetaProof.ReverseDfsStores
