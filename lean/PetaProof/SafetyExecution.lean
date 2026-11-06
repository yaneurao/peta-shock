import PetaProof.SafetyCounterSemantics
import PetaProof.DeletionQueue

/-! safety()の全親カウンター、削除フラグ、待機キューと走査途中の逆辺を一つの状態にする。 -/
namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

structure Graph (V : Type u) (E : Type v) where
  view : V → SafetyCounter.View E
  own : V → Bool
  eligible : V → Bool
  source : E → V
  target : E → V
  source_of_mem : ∀ vertex edge, edge ∈ (view vertex).internal → source edge = vertex
  source_eligible : ∀ vertex edge, edge ∈ (view vertex).internal → eligible vertex = true
  target_eligible : ∀ vertex edge, edge ∈ (view vertex).internal → eligible (target edge) = true
  incoming : V → List E
  incoming_unique : ∀ vertex, (incoming vertex).Nodup
  incoming_spec : ∀ vertex edge, edge ∈ incoming vertex ↔
    edge ∈ (view (source edge)).internal ∧ target edge = vertex

structure State (V : Type u) (E : Type v) where
  deleted : V → Bool
  counters : V → SafetyCounter.Counter E
  pending : List V
  work : List E
  handled : E → Bool

def alive (state : State V E) (vertex : V) : Prop := state.deleted vertex = false

def rejected (graph : Graph V E) (state : State V E) (vertex : V) : Prop :=
  ¬ (graph.view vertex).canStay (graph.own vertex) (state.counters vertex)

def shouldEnqueue (own : Bool) (count : Nat) : Bool := !own || count == 0

/-- 通知は辺IDごとに一回。削除済み親のcountは変更しない。 -/
def notify (graph : Graph V E) (state : State V E) (edge : E) (rest : List E) : State V E :=
  let parent := graph.source edge
  if state.deleted parent then
    { state with work := rest, handled := markSeen state.handled edge }
  else
    let next := SafetyCounter.removeEdge (state.counters parent) edge
    { state with
      counters := fun vertex => if vertex = parent then next else state.counters vertex
      pending := if shouldEnqueue (graph.own parent) next.count then state.pending ++ [parent] else state.pending
      work := rest
      handled := markSeen state.handled edge }

/-- 一つのpopではaliveを落とし、逆辺走査を開始する。重複項目のpopは読み飛ばす。 -/
def pop (graph : Graph V E) (state : State V E) (vertex : V) (rest : List V) : State V E :=
  if state.deleted vertex then { state with pending := rest }
  else { state with deleted := markSeen state.deleted vertex, pending := rest, work := graph.incoming vertex }

def tick (graph : Graph V E) (state : State V E) : State V E :=
  match state.work with
  | edge :: rest => notify graph state edge rest
  | [] => match state.pending with
    | vertex :: rest => pop graph state vertex rest
    | [] => state

/-- countは生存親だけが対象。handledは削除済み親の辺も含む証明用の走査履歴。 -/
structure Invariant (graph : Graph V E) (state : State V E) : Prop where
  exact_count : ∀ vertex, alive state vertex →
    SafetyCounter.Exact (graph.view vertex).good.length (graph.view vertex).internal (state.counters vertex)
  history : ∀ vertex, alive state vertex → ∀ edge ∈ (graph.view vertex).internal,
    (state.counters vertex).seen edge = state.handled edge
  no_early : ∀ edge, state.handled edge = true → state.deleted (graph.target edge) = true
  work_unique : state.work.Nodup
  work_fresh : ∀ edge ∈ state.work, state.handled edge = false
  work_internal : ∀ edge ∈ state.work, edge ∈ (graph.view (graph.source edge)).internal
  work_deleted : ∀ edge ∈ state.work, state.deleted (graph.target edge) = true
  complete : ∀ vertex, alive state vertex → ∀ edge ∈ (graph.view vertex).internal,
    state.deleted (graph.target edge) = true → state.handled edge = true ∨ edge ∈ state.work
  queue_sound : ∀ vertex ∈ state.pending, alive state vertex → rejected graph state vertex
  queue_complete : ∀ vertex, alive state vertex → rejected graph state vertex → vertex ∈ state.pending

omit [DecidableEq V] in
theorem enqueue_iff_rejected (graph : Graph V E) (state : State V E) (parent : V)
    (edge : E) (member : edge ∈ (graph.view parent).internal)
    (fresh : (state.counters parent).seen edge = false)
    (exact_count : SafetyCounter.Exact (graph.view parent).good.length (graph.view parent).internal
      (state.counters parent)) :
    shouldEnqueue (graph.own parent) (SafetyCounter.removeEdge (state.counters parent) edge).count = true ↔
      ¬ (graph.view parent).canStay (graph.own parent) (SafetyCounter.removeEdge (state.counters parent) edge) := by
  cases own : graph.own parent with
  | true =>
    simp only [shouldEnqueue, own, Bool.not_true, Bool.false_or, beq_iff_eq]
    exact SafetyCounter.or_remove_invalid_iff _ _ exact_count edge member fresh
  | false =>
    have invalid := SafetyCounter.and_remove_invalid (graph.view parent) (state.counters parent) edge member
    simp [shouldEnqueue, own, invalid]

theorem notify_deleted (graph : Graph V E) (state : State V E) (edge : E) (rest : List E) :
    (notify graph state edge rest).deleted = state.deleted := by
  dsimp only [notify]
  split <;> rfl

theorem notify_preserves (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (edge : E) (rest : List E) (work : state.work = edge :: rest) :
    Invariant graph (notify graph state edge rest) := by
  have member : edge ∈ state.work := by simp [work]
  have internal := inv.work_internal edge member
  have fresh := inv.work_fresh edge member
  have dead := inv.work_deleted edge member
  have unique : (edge :: rest).Nodup := by simpa only [work] using inv.work_unique
  have tail_unique := (List.nodup_cons.mp unique).2
  have not_tail := (List.nodup_cons.mp unique).1
  have rest_mem : ∀ e ∈ rest, e ∈ state.work := by intro e h; simp [work, h]
  have history_update : ∀ vertex, alive state vertex → ∀ e ∈ (graph.view vertex).internal,
      (if vertex = graph.source edge then SafetyCounter.removeEdge (state.counters (graph.source edge)) edge
        else state.counters vertex).seen e = markSeen state.handled edge e := by
    intro vertex live e present
    by_cases same : vertex = graph.source edge
    · subst vertex
      simp only [ite_true, SafetyCounter.removeEdge]
      unfold markSeen
      split
      · rfl
      · exact inv.history _ live e present
    · have different : e ≠ edge := by
        intro equal
        subst e
        exact same (graph.source_of_mem vertex edge present).symm
      simp only [if_neg same, markSeen, if_neg different]
      exact inv.history vertex live e present
  have common_history : ∀ vertex, alive state vertex →
      state.deleted (graph.source edge) = true → ∀ e ∈ (graph.view vertex).internal,
      (state.counters vertex).seen e = markSeen state.handled edge e := by
    intro vertex live parent_dead e present
    have different : e ≠ edge := by
      intro equal
      subst e
      have source := graph.source_of_mem vertex edge present
      rw [source] at parent_dead
      have live' : state.deleted vertex = false := live
      rw [live'] at parent_dead
      cases parent_dead
    simp only [markSeen, if_neg different]
    exact inv.history vertex live e present
  have marked_sound : ∀ e, markSeen state.handled edge e = true → state.deleted (graph.target e) = true := by
    intro e seen
    rcases (markSeen_true_iff state.handled edge e).mp seen with same | old
    · simpa only [same] using dead
    · exact inv.no_early e old
  have tail_fresh : ∀ e ∈ rest, markSeen state.handled edge e = false := by
    intro e present
    have different : e ≠ edge := by intro same; subst e; exact not_tail present
    simp [markSeen, different, inv.work_fresh e (rest_mem e present)]
  have complete_next : ∀ vertex, alive state vertex → ∀ e ∈ (graph.view vertex).internal,
      state.deleted (graph.target e) = true → markSeen state.handled edge e = true ∨ e ∈ rest := by
    intro vertex live e present child_dead
    rcases inv.complete vertex live e present child_dead with seen | waiting
    · exact Or.inl ((markSeen_true_iff state.handled edge e).mpr (Or.inr seen))
    · have waiting' : e = edge ∨ e ∈ rest := by simpa only [work, List.mem_cons] using waiting
      rcases waiting' with same | tail
      · exact Or.inl ((markSeen_true_iff state.handled edge e).mpr (Or.inl same))
      · exact Or.inr tail
  cases parent_deleted : state.deleted (graph.source edge) with
  | true =>
    simp only [notify, parent_deleted, ite_true]
    exact {
      exact_count := inv.exact_count
      history := fun v live e present => common_history v live parent_deleted e present
      no_early := marked_sound
      work_unique := tail_unique
      work_fresh := tail_fresh
      work_internal := fun e h => inv.work_internal e (rest_mem e h)
      work_deleted := fun e h => inv.work_deleted e (rest_mem e h)
      complete := complete_next
      queue_sound := inv.queue_sound
      queue_complete := inv.queue_complete
    }
  | false =>
    have parent_live : alive state (graph.source edge) := parent_deleted
    have edge_fresh : (state.counters (graph.source edge)).seen edge = false := by
      rw [inv.history _ parent_live edge internal]
      exact fresh
    have exact_next := (SafetyCounter.remove_exact _ _ (graph.view (graph.source edge)).internal_unique
      _ (inv.exact_count _ parent_live) edge internal edge_fresh).1
    have triggered := enqueue_iff_rejected graph state (graph.source edge) edge internal edge_fresh
      (inv.exact_count _ parent_live)
    simp only [notify, parent_deleted, Bool.false_eq_true, ite_false]
    constructor
    · intro vertex live
      by_cases same : vertex = graph.source edge
      · subst vertex; simpa only [ite_true] using exact_next
      · simpa only [if_neg same] using inv.exact_count vertex live
    · exact history_update
    · exact marked_sound
    · exact tail_unique
    · exact tail_fresh
    · exact fun e h => inv.work_internal e (rest_mem e h)
    · exact fun e h => inv.work_deleted e (rest_mem e h)
    · exact complete_next
    · intro vertex queued live
      unfold rejected
      by_cases same : vertex = graph.source edge
      · subst vertex
        simp only [ite_true]
        by_cases flag : shouldEnqueue (graph.own (graph.source edge))
            (SafetyCounter.removeEdge (state.counters (graph.source edge)) edge).count = true
        · exact triggered.mp flag
        · have old_member : graph.source edge ∈ state.pending := by simpa only [if_neg flag] using queued
          exact SafetyCounter.invalid_persists _ _ _ edge (inv.queue_sound _ old_member live)
      · simp only [if_neg same]
        have old_member : vertex ∈ state.pending := by
          split at queued
          · rcases List.mem_append.mp queued with old | added
            · exact old
            · simp only [List.mem_singleton] at added
              exact False.elim (same added)
          · exact queued
        exact inv.queue_sound vertex old_member live
    · intro vertex live invalid
      by_cases same : vertex = graph.source edge
      · subst vertex
        have invalid' : ¬ (graph.view (graph.source edge)).canStay (graph.own (graph.source edge))
            (SafetyCounter.removeEdge (state.counters (graph.source edge)) edge) := by
          simpa only [rejected, ite_true] using invalid
        have flag := triggered.mpr invalid'
        simp only [flag, ite_true, List.mem_append, List.mem_singleton]
        exact Or.inr trivial
      · have old_invalid : rejected graph state vertex := by simpa only [rejected, if_neg same] using invalid
        have old_member := inv.queue_complete vertex live old_invalid
        split
        · exact List.mem_append_left _ old_member
        · exact old_member

theorem alive_mark_iff (deleted : V → Bool) (vertex other : V) :
    markSeen deleted vertex other = false ↔ other ≠ vertex ∧ deleted other = false := by
  by_cases same : other = vertex <;> simp [markSeen, same]

omit [DecidableEq E] in
theorem pop_preserves (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (vertex : V) (rest : List V) (work : state.work = []) (pending : state.pending = vertex :: rest) :
    Invariant graph (pop graph state vertex rest) := by
  have rest_mem : ∀ v ∈ rest, v ∈ state.pending := by intro v h; simp [pending, h]
  cases deleted : state.deleted vertex with
  | true =>
    simp only [pop, deleted, ite_true]
    refine { inv with
      queue_sound := fun v member live => inv.queue_sound v (rest_mem v member) live
      queue_complete := ?_ }
    intro v live invalid
    have queued := inv.queue_complete v live invalid
    have cases' : v = vertex ∨ v ∈ rest := by simpa only [pending, List.mem_cons] using queued
    rcases cases' with same | member
    · subst v
      change state.deleted vertex = false at live
      rw [deleted] at live
      cases live
    · exact member
  | false =>
    have was_live : ∀ v, markSeen state.deleted vertex v = false → alive state v :=
      fun v h => ((alive_mark_iff _ _ _).mp h).2
    have distinct : ∀ v, markSeen state.deleted vertex v = false → v ≠ vertex :=
      fun v h => ((alive_mark_iff _ _ _).mp h).1
    simp only [pop, deleted, Bool.false_eq_true, ite_false]
    constructor
    · intro v live; exact inv.exact_count v (was_live v live)
    · intro v live; exact inv.history v (was_live v live)
    · intro e seen
      exact (markSeen_true_iff state.deleted vertex _).mpr (Or.inr (inv.no_early e seen))
    · exact graph.incoming_unique vertex
    · intro e member
      have target := ((graph.incoming_spec vertex e).mp member).2
      cases seen : state.handled e with
      | false => rfl
      | true =>
        have dead := inv.no_early e seen
        rw [target, deleted] at dead
        cases dead
    · intro e member; exact ((graph.incoming_spec vertex e).mp member).1
    · intro e member
      have target := ((graph.incoming_spec vertex e).mp member).2
      simp [markSeen, target]
    · intro v live e member dead
      rcases (markSeen_true_iff state.deleted vertex (graph.target e)).mp dead with same | old
      · right
        apply (graph.incoming_spec vertex e).mpr
        refine ⟨?_, same⟩
        simpa only [graph.source_of_mem v e member] using member
      · rcases inv.complete v (was_live v live) e member old with seen | waiting
        · exact Or.inl seen
        · rw [work] at waiting; cases waiting
    · intro v queued live
      exact inv.queue_sound v (rest_mem v queued) (was_live v live)
    · intro v live invalid
      have queued := inv.queue_complete v (was_live v live) invalid
      have cases' : v = vertex ∨ v ∈ rest := by simpa only [pending, List.mem_cons] using queued
      exact cases'.resolve_left (distinct v live)

theorem tick_preserves (graph : Graph V E) (state : State V E) (inv : Invariant graph state) :
    Invariant graph (tick graph state) := by
  cases work : state.work with
  | cons edge rest => simpa only [tick, work] using notify_preserves graph state inv edge rest work
  | nil =>
    cases pending : state.pending with
    | nil => simpa only [tick, work, pending] using inv
    | cons vertex rest => simpa only [tick, work, pending] using pop_preserves graph state inv vertex rest work pending

omit [DecidableEq V] in
/-- 有効な走査状態から、減算前countの正値性を通知の新規性込みで導く。 -/
theorem work_no_underflow (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (edge : E) (member : edge ∈ state.work) (live : alive state (graph.source edge)) :
    0 < (state.counters (graph.source edge)).count := by
  have internal := inv.work_internal edge member
  have fresh : (state.counters (graph.source edge)).seen edge = false := by
    rw [inv.history _ live edge internal]
    exact inv.work_fresh edge member
  exact (SafetyCounter.remove_exact _ _ (graph.view (graph.source edge)).internal_unique _
    (inv.exact_count _ live) edge internal fresh).2.1

def initialReject (graph : Graph V E) (vertex : V) : Bool :=
  if graph.own vertex then
    (graph.view vertex).good.length + (graph.view vertex).internal.length == 0
  else !(graph.view vertex).bad.isEmpty

def initial (graph : Graph V E) (vertices : List V) : State V E := {
  deleted := fun vertex => !(graph.eligible vertex)
  counters := fun vertex => SafetyCounter.initial (graph.view vertex).good.length (graph.view vertex).internal
  pending := vertices.filter (fun vertex => graph.eligible vertex && initialReject graph vertex)
  work := []
  handled := fun _ => false
}

omit [DecidableEq V] [DecidableEq E] in
theorem initial_reject_iff (graph : Graph V E) (vertex : V) :
    initialReject graph vertex = true ↔
      ¬ (graph.view vertex).canStay (graph.own vertex)
        (SafetyCounter.initial (graph.view vertex).good.length (graph.view vertex).internal) := by
  rw [SafetyCounter.initial_invalid_iff]
  cases own : graph.own vertex <;> simp [initialReject, own, SafetyCounter.initial, List.isEmpty_iff]

omit [DecidableEq V] [DecidableEq E] in
theorem initial_invariant (graph : Graph V E) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    Invariant graph (initial graph vertices) := by
  constructor
  · intro vertex _; exact SafetyCounter.initial_exact _ _
  · intro vertex _ edge _; rfl
  · intro edge impossible; cases impossible
  · exact List.nodup_nil
  · intro edge impossible; cases impossible
  · intro edge impossible; cases impossible
  · intro edge impossible; cases impossible
  · intro vertex _ edge member dead
    have eligible := graph.target_eligible vertex edge member
    change Bool.not (graph.eligible (graph.target edge)) = true at dead
    simp [eligible] at dead
  · intro vertex member _
    have member' : vertex ∈ vertices ∧ graph.eligible vertex = true ∧ initialReject graph vertex = true := by
      simpa only [initial, List.mem_filter, Bool.and_eq_true] using member
    have reject := member'.2.2
    exact (initial_reject_iff graph vertex).mp reject
  · intro vertex live invalid
    have eligible : graph.eligible vertex = true := by simpa only [alive, initial, Bool.not_eq_false'] using live
    apply List.mem_filter.mpr
    exact ⟨covered vertex, by simp [eligible, (initial_reject_iff graph vertex).mpr invalid]⟩

inductive Run (graph : Graph V E) : State V E → Nat → State V E → Prop
  | done (state) : Run graph state 0 state
  | next {start finish n} : Run graph (tick graph start) n finish → Run graph start (n + 1) finish

theorem Run.invariant (graph : Graph V E) {start finish : State V E} {n : Nat}
    (run : Run graph start n finish) (inv : Invariant graph start) : Invariant graph finish := by
  induction run with
  | done => exact inv
  | next tail ih => exact ih (tick_preserves graph _ inv)

end PetaProof.SafetyExecution
