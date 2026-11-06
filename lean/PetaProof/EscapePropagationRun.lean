import PetaProof.EscapePropagationBatch

/-! popと全逆辺通知を交互実行する。通知の新規性を前のpop履歴から導く。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

def openNext (state : State V E) (head : V × Nat) : State V E :=
  { state with frame := ⟨head.1, head.2, EscapeFifo.pop state.frame.queue⟩ }

omit [DecidableEq V] [DecidableEq E] in
theorem openNext_preserves (state : State V E) (inv : Invariant input state)
    (head : V × Nat) (rest : List (V × Nat)) (pending : state.frame.queue.pending = head :: rest) :
    Invariant input (state.openNext head) := by
  refine ⟨EscapeFifo.Frame.begin_preserves state.frame.queue inv.frame.queue head rest pending,
    inv.counters, inv.seen_notified, inv.pending_history, inv.own_empty, ?_⟩
  intro edge reported
  have logged := inv.notified_logged edge reported
  change (input.child edge, state.received edge) ∈ (EscapeFifo.pop state.frame.queue).popped
  simp only [EscapeFifo.pop, pending]
  exact List.mem_append_left _ logged

omit [DecidableEq V] [DecidableEq E] in
/-- 新たにpopする子は以前のpop済み列にないため、その逆辺はまだ通知されていない。 -/
theorem openNext_fresh (state : State V E) (inv : Invariant input state)
    (head : V × Nat) (rest : List (V × Nat)) (pending : state.frame.queue.pending = head :: rest)
    (edge : E) (member : edge ∈ input.incoming head.1) : state.notified edge = false := by
  cases notified : state.notified edge with
  | false => rfl
  | true =>
    have logged := inv.notified_logged edge notified
    have old : input.child edge ∈ state.frame.queue.popped.map Prod.fst := List.mem_map.mpr
      ⟨(input.child edge, state.received edge), logged, rfl⟩
    have child := (input.incoming_correct head.1 edge).mp member
    rw [child] at old
    have unique : ((state.frame.queue.popped.map Prod.fst) ++ (head.1 :: rest.map Prod.fst)).Nodup := by
      simpa only [EscapeFifo.State.total, pending, List.map_append, List.map_cons] using inv.frame.queue.unique
    have cross := (List.pairwise_append.mp unique).2.2
    exact False.elim (cross head.1 old head.1 (by simp) rfl)

/-- pop済みの全ての子について、全逆辺の通知を終えた状態。 -/
def Complete (state : State V E) : Prop :=
  ∀ edge, state.notified edge = true ↔ input.child edge ∈ state.frame.queue.popped.map Prod.fst

def advance (state : State V E) : State V E :=
  match state.frame.queue.pending with
  | [] => state
  | head :: _ => notifyIncoming input (state.openNext head)

theorem advance_preserves (state : State V E) (inv : Invariant input state) :
    Invariant input (advance input state) := by
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using inv
  | cons head rest =>
    simp only [advance, pending]
    apply notifyIncoming_preserves input (state.openNext head) (openNext_preserves input state inv head rest pending)
    exact openNext_fresh input state inv head rest pending

theorem advance_complete (state : State V E) (complete : Complete input state) :
    Complete input (advance input state) := by
  intro edge
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using complete edge
  | cons head rest =>
    simp only [advance, pending]
    change (notifyIncoming input (state.openNext head)).notified edge = true ↔ _
    rw [notifyIncoming_complete]
    have popped := notifyMany_popped input (state.openNext head) (input.incoming head.1)
    change (notifyIncoming input (state.openNext head)).frame.queue.popped = _ at popped
    rw [popped]
    change input.child edge = head.1 ∨ state.notified edge = true ↔
      input.child edge ∈ (EscapeFifo.pop state.frame.queue).popped.map Prod.fst
    simp only [EscapeFifo.pop, pending, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rw [complete edge]
    exact or_comm

def run : Nat → State V E → State V E
  | 0, state => state
  | fuel + 1, state => run fuel (advance input state)

theorem run_preserves (fuel : Nat) (state : State V E) (inv : Invariant input state) :
    Invariant input (run input fuel state) := by
  induction fuel generalizing state with
  | zero => exact inv
  | succ fuel ih => exact ih _ (advance_preserves input state inv)

theorem run_complete (fuel : Nat) (state : State V E) (complete : Complete input state) :
    Complete input (run input fuel state) := by
  induction fuel generalizing state with
  | zero => exact complete
  | succ fuel ih => exact ih _ (advance_complete input state complete)

theorem advance_popped_length (state : State V E) (head : V × Nat) (rest : List (V × Nat))
    (pending : state.frame.queue.pending = head :: rest) :
    (advance input state).frame.queue.popped.length = state.frame.queue.popped.length + 1 := by
  have logged := notifyMany_popped input (state.openNext head) (input.incoming head.1)
  change (notifyIncoming input (state.openNext head)).frame.queue.popped = _ at logged
  simp only [advance, pending]
  rw [logged]
  simp [openNext, EscapeFifo.pop, pending]

theorem run_empty (fuel : Nat) (state : State V E) (empty : state.frame.queue.pending = []) :
    (run input fuel state).frame.queue.pending = [] := by
  induction fuel with
  | zero => exact empty
  | succ fuel ih => simpa only [run, advance, empty] using ih

/-- 全親の実カウンターを更新する制御も、一意投入により高々N回のpopで止まる。 -/
theorem run_drained (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (fuel : Nat) (state : State V E) (inv : Invariant input state)
    (budget : vertices.length ≤ state.frame.queue.popped.length + fuel) :
    (run input fuel state).frame.queue.pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := EscapeFifo.total_length_bound state.frame.queue inv.frame.queue vertices covered
    simp only [EscapeFifo.State.total, List.length_append] at bound
    have empty : state.frame.queue.pending.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero empty
  | succ fuel ih =>
    cases pending : state.frame.queue.pending with
    | nil => exact run_empty input (fuel + 1) state pending
    | cons head rest =>
      have count := advance_popped_length input state head rest pending
      exact ih (advance input state) (advance_preserves input state inv) (by omega)

omit [DecidableEq V] [DecidableEq E] in
theorem pending_own_outside (state : State V E) (inv : Invariant input state) (complete : Complete input state)
    (vertex : V) (own : input.own vertex = true) (pending : (state.counters vertex).result = none)
    (edge : E) (member : edge ∈ input.outgoing vertex) :
    input.child edge ∉ state.frame.queue.popped.map Prod.fst := by
  intro inside
  have notified := (complete edge).mpr inside
  rw [pending_own_unreported input state inv vertex own pending edge member] at notified
  cases notified

omit [DecidableEq V] [DecidableEq E] in
theorem pending_child_outside (state : State V E) (inv : Invariant input state) (complete : Complete input state)
    (vertex : V) (pending : (state.counters vertex).result = none) :
    ∃ edge ∈ input.outgoing vertex, input.child edge ∉ state.frame.queue.popped.map Prod.fst := by
  obtain ⟨edge, member, absent⟩ := pending_missing input state inv vertex pending
  refine ⟨edge, member, ?_⟩
  intro inside
  have notified := (complete edge).mpr inside
  rw [absent] at notified
  cases notified

end PetaProof.EscapePropagation.State
