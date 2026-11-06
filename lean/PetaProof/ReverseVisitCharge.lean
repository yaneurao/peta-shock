import PetaProof.CheckingDfsAccounting

/-! 第二DFSの各popに任意の非負費用を課す。選別前の逆辺行の走査も数えられる。 -/
namespace PetaProof.ReverseVisitCharge

universe u
variable {V : Type u} [DecidableEq V]

def credit (vertices : List V) (charge : V → Nat) (result : V → Option Nat) : Nat :=
  DeletionQueue.credit charge (ReverseDfsWork.assigned result) vertices

def potential (vertices : List V) (charge : V → Nat) (state : ReverseDfsStack.State V) : Nat :=
  credit vertices charge state.result + (state.pending.map charge).sum

theorem push_preserves (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (id : Nat) (state : ReverseDfsStack.State V) (vertex : V) :
    potential vertices charge (ReverseDfsStack.push id state vertex) = potential vertices charge state := by
  cases found : state.result vertex with
  | some old => simp [ReverseDfsStack.push, found]
  | none =>
    have seen : ReverseDfsWork.assigned (fun other => if other = vertex then some id else state.result other) =
        markSeen (ReverseDfsWork.assigned state.result) vertex := by
      funext other
      by_cases same : other = vertex <;> simp [ReverseDfsWork.assigned, markSeen, same]
    have moved := DeletionQueue.credit_mark charge (ReverseDfsWork.assigned state.result) vertex vertices
      unique (covered vertex) (by simp [ReverseDfsWork.assigned, found])
    simp only [potential, credit, ReverseDfsStack.push, found, seen, List.map_cons, List.sum_cons]
    omega

theorem scan_preserves (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (id : Nat) (items : List V) (state : ReverseDfsStack.State V) :
    potential vertices charge (ReverseDfsStack.scan id items state) = potential vertices charge state := by
  induction items generalizing state with
  | nil => rfl
  | cons vertex rest ih => rw [ReverseDfsStack.scan, ih, push_preserves vertices unique covered]

def visitCharge (charge : V → Nat) (state : ReverseDfsStack.State V) : Nat :=
  match state.pending with
  | [] => 0
  | vertex :: _ => charge vertex

theorem visit_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (id : Nat) (parents : V → List V) (state : ReverseDfsStack.State V) :
    potential vertices charge (ReverseDfsStack.visit id parents state) + visitCharge charge state =
      potential vertices charge state := by
  cases pending : state.pending with
  | nil => simp [ReverseDfsStack.visit, visitCharge, pending]
  | cons vertex rest =>
    simp only [ReverseDfsStack.visit, pending, scan_preserves vertices unique covered]
    simp [potential, credit, ReverseDfsStack.pop, pending, visitCharge,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 遷移はparentsだけで決まり、会計用chargeは探索結果を変えない。 -/
def walkCharge (charge : V → Nat) (id : Nat) (parents : V → List V) : Nat → ReverseDfsStack.State V → Nat
  | 0, _ => 0
  | fuel + 1, state => visitCharge charge state +
      walkCharge charge id parents fuel (ReverseDfsStack.visit id parents state)

theorem walk_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat)
    (id : Nat) (parents : V → List V) (fuel : Nat) (state : ReverseDfsStack.State V) :
    potential vertices charge (ReverseDfsStack.walk id parents fuel state) +
      walkCharge charge id parents fuel state = potential vertices charge state := by
  induction fuel generalizing state with
  | zero => simp [ReverseDfsStack.walk, walkCharge]
  | succ fuel ih =>
    have first := visit_balance vertices unique covered charge id parents state
    have tail := ih (ReverseDfsStack.visit id parents state)
    simp only [ReverseDfsStack.walk, walkCharge]
    omega

def descendCharge (vertices : List V) (charge : V → Nat) (parents : V → List V)
    (state : ComponentNumbering.State V) (root : V) : Nat :=
  walkCharge charge state.roots.length parents vertices.length
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)

theorem descend_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    credit vertices charge (ComponentNumbering.descend vertices.length parents state root).result +
      descendCharge vertices charge parents state root = credit vertices charge state.result := by
  have balance := walk_balance vertices unique covered charge state.roots.length parents vertices.length
    (ReverseDfsStack.push state.roots.length (ReverseDfsStack.initial state.result) root)
  have moved := push_preserves vertices unique covered charge state.roots.length
    (ReverseDfsStack.initial state.result) root
  have empty := ComponentNumbering.descend_drains vertices unique covered parents state valid root
  change (ComponentNumbering.descend vertices.length parents state root).pending = [] at empty
  change potential vertices charge (ComponentNumbering.descend vertices.length parents state root) +
    descendCharge vertices charge parents state root = _ at balance
  rw [moved] at balance
  simpa [potential, empty, ReverseDfsStack.initial] using balance

def stepCharge (vertices : List V) (charge : V → Nat) (parents : V → List V)
    (state : ComponentNumbering.State V) (root : V) : Nat :=
  if state.result root = none then descendCharge vertices charge parents state root else 0

theorem step_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    credit vertices charge (ComponentNumbering.step vertices.length parents state root).result +
      stepCharge vertices charge parents state root = credit vertices charge state.result := by
  by_cases fresh : state.result root = none
  · simpa only [ComponentNumbering.step, stepCharge, if_pos fresh] using
      descend_balance vertices unique covered charge parents state valid root
  · simp [ComponentNumbering.step, stepCharge, fresh]

def passCharge (vertices : List V) (charge : V → Nat) (parents : V → List V) :
    List V → ComponentNumbering.State V → Nat
  | [], _ => 0
  | root :: rest, state => stepCharge vertices charge parents state root +
      passCharge vertices charge parents rest (ComponentNumbering.step vertices.length parents state root)

theorem pass_balance (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat) (parents : V → List V)
    (roots : List V) (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) :
    credit vertices charge (ComponentNumbering.pass vertices.length parents roots state).result +
      passCharge vertices charge parents roots state = credit vertices charge state.result := by
  induction roots generalizing state with
  | nil => simp [ComponentNumbering.pass, passCharge]
  | cons root rest ih =>
    have first := step_balance vertices unique covered charge parents state valid root
    have tail := ih (ComponentNumbering.step vertices.length parents state root)
      (ComponentNumbering.step_preserves vertices.length parents state valid root)
    simp only [ComponentNumbering.pass, passCharge]
    omega

theorem finish_charge (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (charge : V → Nat) (parents : V → List V)
    (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) :
    passCharge vertices charge parents roots ComponentNumbering.initial = (vertices.map charge).sum := by
  have balance := pass_balance vertices unique covered charge parents roots ComponentNumbering.initial
    ComponentNumbering.initial_invariant
  have assigned : ∀ vertex, ReverseDfsWork.assigned
      (ComponentNumbering.finish vertices roots parents).result vertex = true := by
    intro vertex
    obtain ⟨id, found⟩ := ComponentNumbering.finish_assigned vertices roots parents roots_cover vertex
    simp [ReverseDfsWork.assigned, found]
  have zero := ForwardDfs.credit_zero vertices charge _ assigned
  change credit vertices charge (ComponentNumbering.finish vertices roots parents).result = 0 at zero
  have start : credit vertices charge ComponentNumbering.initial.result = (vertices.map charge).sum :=
    DeletionQueue.initial_credit vertices charge
  change credit vertices charge (ComponentNumbering.finish vertices roots parents).result + _ = _ at balance
  rw [zero, start] at balance
  omega

end PetaProof.ReverseVisitCharge
