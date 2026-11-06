import PetaProof.AdmissionQueue
import PetaProof.History

/-! 距離付きFIFOの実push/pop。最短脱出の親を現在距離+1で積むと取り出し順が保たれる。 -/
namespace PetaProof.EscapeFifo

universe u
variable {V : Type u} [DecidableEq V]

structure State (V : Type u) where
  seen : V → Bool
  popped : List (V × Nat)
  pending : List (V × Nat)

def State.total (state : State V) : List (V × Nat) := state.popped ++ state.pending
def initial : State V := ⟨fun _ => false, [], []⟩

def push (state : State V) (vertex : V) (distance : Nat) : State V :=
  if state.seen vertex then state else
    ⟨markSeen state.seen vertex, state.popped, state.pending ++ [(vertex, distance)]⟩

def pop (state : State V) : State V :=
  match state.pending with
  | [] => state
  | head :: rest => { state with popped := state.popped ++ [head], pending := rest }

/-- pendingに現れる距離は高々二つの隣接した層。全ログの順序も保持する。 -/
structure Invariant (state : State V) : Prop where
  unique : (state.total.map Prod.fst).Nodup
  seen_exact : ∀ vertex, state.seen vertex = true ↔ vertex ∈ state.total.map Prod.fst
  ordered : state.total.Pairwise (fun left right => left.2 ≤ right.2)
  narrow : ∀ head rest, state.pending = head :: rest → ∀ next ∈ rest, next.2 ≤ head.2 + 1

omit [DecidableEq V] in
theorem initial_invariant : Invariant (initial : State V) := by
  constructor <;> simp [initial, State.total]

omit [DecidableEq V] in
theorem pop_total (state : State V) : (pop state).total = state.total := by
  cases pending : state.pending <;> simp [pop, pending, State.total, List.append_assoc]

theorem push_preserves (state : State V) (inv : Invariant state) (vertex : V) (distance : Nat)
    (upper : ∀ item ∈ state.total, item.2 ≤ distance)
    (width : ∀ head rest, state.pending = head :: rest → distance ≤ head.2 + 1) :
    Invariant (push state vertex distance) := by
  cases seen : state.seen vertex with
  | true => simpa only [push, seen, ite_true] using inv
  | false =>
    have fresh : vertex ∉ state.total.map Prod.fst := by
      intro member
      have contradiction := (inv.seen_exact vertex).mpr member
      rw [seen] at contradiction
      cases contradiction
    have total : (push state vertex distance).total = state.total ++ [(vertex, distance)] := by
      simp [push, seen, State.total, List.append_assoc]
    constructor
    · rw [total, List.map_append]
      exact nodup_append_fresh _ inv.unique vertex fresh
    · intro other
      rw [total, List.map_append, List.mem_append]
      simp only [push, seen, Bool.false_eq_true, ite_false]
      change markSeen state.seen vertex other = true ↔ other ∈ state.total.map Prod.fst ∨ other ∈ [vertex]
      rw [markSeen_true_iff, ← inv.seen_exact other]
      simp only [List.mem_singleton, or_comm]
    · rw [total]
      apply List.pairwise_append.mpr
      refine ⟨inv.ordered, by simp, ?_⟩
      intro left member right singleton
      have same : right = (vertex, distance) := by simpa using singleton
      subst right
      exact upper left member
    · intro head rest pending next member
      have row : state.pending ++ [(vertex, distance)] = head :: rest := by
        simpa only [push, seen, Bool.false_eq_true, ite_false] using pending
      cases old : state.pending with
      | nil =>
        simp only [old, List.nil_append, List.cons.injEq] at row
        rw [← row.2] at member
        cases member
      | cons first tail =>
        simp only [old, List.cons_append, List.cons.injEq] at row
        have choices : next ∈ tail ∨ next ∈ [(vertex, distance)] := by
          rw [← row.2] at member
          exact List.mem_append.mp member
        rw [← row.1]
        rcases choices with original | singleton
        · exact inv.narrow first tail old next original
        · have same : next = (vertex, distance) := by simpa using singleton
          subst next
          exact width first tail old

omit [DecidableEq V] in
theorem pop_preserves (state : State V) (inv : Invariant state) : Invariant (pop state) := by
  cases pending : state.pending with
  | nil => simpa only [pop, pending] using inv
  | cons first rest =>
    constructor
    · rw [pop_total]; exact inv.unique
    · intro vertex
      rw [pop_total]
      simpa only [pop, pending] using inv.seen_exact vertex
    · rw [pop_total]; exact inv.ordered
    · intro head tail row next member
      have newRow : rest = head :: tail := by simpa only [pop, pending] using row
      have pendingOrder := (List.pairwise_append.mp inv.ordered).2.1
      rw [pending] at pendingOrder
      have firstLower := (List.pairwise_cons.mp pendingOrder).1 head (by simp [newRow])
      have oldBound := inv.narrow first rest pending next (by rw [newRow]; simp [member])
      omega

def Bound (state : State V) (distance : Nat) : Prop := ∀ item ∈ state.total, item.2 ≤ distance
def Width (state : State V) (distance : Nat) : Prop :=
  ∀ head rest, state.pending = head :: rest → distance ≤ head.2 + 1

theorem push_bound (state : State V) (vertex : V) (distance : Nat) (bound : Bound state distance) :
    Bound (push state vertex distance) distance := by
  cases seen : state.seen vertex with
  | true => simpa only [push, seen, ite_true] using bound
  | false =>
    intro item member
    have total : (push state vertex distance).total = state.total ++ [(vertex, distance)] := by
      simp [push, seen, State.total, List.append_assoc]
    rw [total, List.mem_append] at member
    rcases member with old | singleton
    · exact bound item old
    · have same : item = (vertex, distance) := by simpa using singleton
      subst item
      exact Nat.le_refl _

theorem push_width (state : State V) (vertex : V) (distance : Nat) (width : Width state distance) :
    Width (push state vertex distance) distance := by
  cases seen : state.seen vertex with
  | true => simpa only [push, seen, ite_true] using width
  | false =>
    intro head rest pending
    have row : state.pending ++ [(vertex, distance)] = head :: rest := by
      simpa only [push, seen, Bool.false_eq_true, ite_false] using pending
    cases old : state.pending with
    | nil =>
      simp only [old, List.nil_append, List.cons.injEq] at row
      rw [← row.1]
      exact Nat.le_succ _
    | cons first tail =>
      simp only [old, List.cons_append, List.cons.injEq] at row
      rw [← row.1]
      exact width first tail old

def pushMany (distance : Nat) : State V → List V → State V
  | state, [] => state
  | state, vertex :: rest => pushMany distance (push state vertex distance) rest

theorem pushMany_preserves (state : State V) (inv : Invariant state) (distance : Nat) (vertices : List V)
    (bound : Bound state distance) (width : Width state distance) :
    Invariant (pushMany distance state vertices) ∧ Bound (pushMany distance state vertices) distance ∧
      Width (pushMany distance state vertices) distance := by
  induction vertices generalizing state with
  | nil => exact ⟨inv, bound, width⟩
  | cons vertex rest ih =>
    exact ih _ (push_preserves state inv vertex distance bound width)
      (push_bound state vertex distance bound) (push_width state vertex distance width)

omit [DecidableEq V] in
theorem popped_front_bound (state : State V) (inv : Invariant state) (head : V × Nat) (rest : List (V × Nat))
    (pending : state.pending = head :: rest) : Bound (pop state) (head.2 + 1) := by
  intro item member
  rw [pop_total, State.total, List.mem_append] at member
  rcases member with old | queued
  · have lower := (List.pairwise_append.mp inv.ordered).2.2 item old head (by simp [pending])
    omega
  · rw [pending, List.mem_cons] at queued
    rcases queued with same | tail
    · subst item; omega
    · exact inv.narrow head rest pending item tail

omit [DecidableEq V] in
theorem popped_front_width (state : State V) (inv : Invariant state) (head : V × Nat) (rest : List (V × Nat))
    (pending : state.pending = head :: rest) : Width (pop state) (head.2 + 1) := by
  intro next tail row
  have newRow : rest = next :: tail := by simpa only [pop, pending] using row
  have ordered := (List.pairwise_append.mp inv.ordered).2.1
  rw [pending] at ordered
  have lower := (List.pairwise_cons.mp ordered).1 next (by simp [newRow])
  omega

/-- 一つの子をpopし、今回確定した親だけを現在距離+1で末尾へ積む。 -/
def advance (state : State V) (parents : List V) : State V :=
  match state.pending with
  | [] => state
  | head :: _ => pushMany (head.2 + 1) (pop state) parents

theorem advance_preserves (state : State V) (inv : Invariant state) (parents : List V) :
    Invariant (advance state parents) := by
  cases pending : state.pending with
  | nil => simpa only [advance, pending] using inv
  | cons head rest =>
    simpa only [advance, pending] using
      (pushMany_preserves (pop state) (pop_preserves state inv) (head.2 + 1) parents
        (popped_front_bound state inv head rest pending) (popped_front_width state inv head rest pending)).1

def seeded (goals : List V) : State V := pushMany 0 initial goals

theorem seeded_invariant (goals : List V) : Invariant (seeded goals) := by
  exact (pushMany_preserves initial initial_invariant 0 goals
    (by intro item member; cases member) (by intro head rest impossible; cases impossible)).1

private theorem count_lt_two (items : List V) (unique : items.Nodup) (vertex : V) : items.count vertex < 2 := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = vertex
    · subst head
      simp [List.count_cons, List.count_eq_zero_of_not_mem parts.1]
    · simpa [List.count_cons, same, Ne.symm same] using ih parts.2

theorem total_length_bound (state : State V) (inv : Invariant state)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) : state.total.length ≤ vertices.length := by
  have bound := history_length_bound vertices (state.total.map Prod.fst) 2
    (fun vertex _ => covered vertex) (fun vertex _ => count_lt_two _ inv.unique vertex)
  simpa using bound

def run (accepted : V → Nat → State V → List V) : Nat → State V → State V
  | 0, state => state
  | fuel + 1, state => match state.pending with
      | [] => state
      | head :: _ => run accepted fuel (advance state (accepted head.1 head.2 state))

theorem run_preserves (accepted : V → Nat → State V → List V) (fuel : Nat) (state : State V)
    (inv : Invariant state) : Invariant (run accepted fuel state) := by
  induction fuel generalizing state with
  | zero => exact inv
  | succ fuel ih =>
    cases pending : state.pending with
    | nil => simpa only [run, pending] using inv
    | cons head rest =>
      simpa only [run, pending] using ih _ (advance_preserves state inv _)

theorem pushMany_popped (distance : Nat) (state : State V) (vertices : List V) :
    (pushMany distance state vertices).popped = state.popped := by
  induction vertices generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [pushMany, ih]
    cases seen : state.seen vertex <;> simp [push, seen]

theorem advance_popped_length (state : State V) (parents : List V) (head : V × Nat)
    (rest : List (V × Nat)) (pending : state.pending = head :: rest) :
    (advance state parents).popped.length = state.popped.length + 1 := by
  simp only [advance, pending, pushMany_popped, pop, List.length_append, List.length_singleton]

/-- 新規投入がどの親の集合であっても、重複ガードにより高々N回のpopで排出できる。 -/
theorem run_drained (accepted : V → Nat → State V → List V)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (fuel : Nat) (state : State V)
    (inv : Invariant state) (budget : vertices.length ≤ state.popped.length + fuel) :
    (run accepted fuel state).pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := total_length_bound state inv vertices covered
    simp only [State.total, List.length_append] at bound
    have empty : state.pending.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero empty
  | succ fuel ih =>
    cases pending : state.pending with
    | nil => simp only [run, pending]
    | cons head rest =>
      have step := advance_popped_length state (accepted head.1 head.2 state) head rest pending
      simpa only [run, pending] using ih _ (advance_preserves state inv _) (by omega)

end PetaProof.EscapeFifo
