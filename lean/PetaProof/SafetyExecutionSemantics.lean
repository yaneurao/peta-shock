import PetaProof.SafetyExecution

namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- この局所グラフの安全手。固定の良い出口、または候補内に残る内部辺。 -/
def Graph.safe (graph : Graph V E) (kept : V → Prop) (vertex : V) (edge : E) : Prop :=
  edge ∈ (graph.view vertex).good ∨ (edge ∈ (graph.view vertex).internal ∧ kept (graph.target edge))

def Graph.canStay (graph : Graph V E) (kept : V → Prop) (vertex : V) : Prop :=
  (graph.own vertex = true → ∃ e ∈ (graph.view vertex).outgoing, graph.safe kept vertex e) ∧
  (graph.own vertex = false → ∀ e ∈ (graph.view vertex).outgoing, graph.safe kept vertex e)

def Graph.SafeSet (graph : Graph V E) (kept : V → Prop) : Prop :=
  ∀ vertex, kept vertex → graph.canStay kept vertex

omit [DecidableEq V] [DecidableEq E] in
theorem live_edge_unseen (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (vertex : V) (live : alive state vertex) (edge : E) (internal : edge ∈ (graph.view vertex).internal)
    (child_live : alive state (graph.target edge)) : (state.counters vertex).seen edge = false := by
  rw [inv.history vertex live edge internal]
  cases seen : state.handled edge with
  | false => rfl
  | true =>
    have dead := inv.no_early edge seen
    change state.deleted (graph.target edge) = false at child_live
    rw [child_live] at dead
    cases dead

omit [DecidableEq V] [DecidableEq E] in
theorem safe_subset_supported (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (kept : V → Prop) (subset : ∀ vertex, kept vertex → alive state vertex)
    (vertex : V) (live : alive state vertex) (edge : E) (safe : graph.safe kept vertex edge) :
    (graph.view vertex).safe (state.counters vertex) edge := by
  rcases safe with good | ⟨internal, child⟩
  · exact Or.inl good
  · exact Or.inr ⟨internal, live_edge_unseen graph state inv vertex live edge internal (subset _ child)⟩

omit [DecidableEq V] [DecidableEq E] in
theorem safe_subset_canStay (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (kept : V → Prop) (safe : graph.SafeSet kept) (subset : ∀ vertex, kept vertex → alive state vertex)
    (vertex : V) (member : kept vertex) :
    (graph.view vertex).canStay (graph.own vertex) (state.counters vertex) := by
  have stay := safe vertex member
  constructor
  · intro own
    obtain ⟨e, legal, support⟩ := stay.1 own
    exact ⟨e, legal, safe_subset_supported graph state inv kept subset vertex (subset _ member) e support⟩
  · intro other e legal
    exact safe_subset_supported graph state inv kept subset vertex (subset _ member) e (stay.2 other e legal)

theorem tick_alive_subset (graph : Graph V E) (state : State V E) :
    ∀ vertex, alive (tick graph state) vertex → alive state vertex := by
  intro vertex live
  cases work : state.work with
  | cons edge rest =>
    simpa only [alive, tick, work, notify_deleted] using live
  | nil =>
    cases pending : state.pending with
    | nil => simpa only [tick, work, pending] using live
    | cons head rest =>
      simp only [tick, work, pending, alive] at live
      cases dead : state.deleted head with
      | true => simpa only [pop, dead, ite_true] using live
      | false =>
        simp only [pop, dead, Bool.false_eq_true, ite_false] at live
        exact ((alive_mark_iff _ _ _).mp live).2

theorem tick_preserves_safe (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (kept : V → Prop) (safe : graph.SafeSet kept) (subset : ∀ vertex, kept vertex → alive state vertex) :
    ∀ vertex, kept vertex → alive (tick graph state) vertex := by
  intro vertex member
  have live := subset vertex member
  cases work : state.work with
  | cons edge rest => simpa only [alive, tick, work, notify_deleted] using live
  | nil =>
    cases pending : state.pending with
    | nil => simpa only [tick, work, pending] using live
    | cons head rest =>
      have different : vertex ≠ head := by
        intro same
        subst vertex
        have queued : head ∈ state.pending := by simp [pending]
        exact inv.queue_sound head queued live (safe_subset_canStay graph state inv kept safe subset head member)
      simp only [tick, work, pending, alive]
      cases dead : state.deleted head with
      | true => simpa only [pop, dead, ite_true] using live
      | false =>
        simp only [pop, dead, Bool.false_eq_true, ite_false]
        exact (alive_mark_iff _ _ _).mpr ⟨different, live⟩

theorem Run.alive_subset (graph : Graph V E) {start finish : State V E} {n : Nat}
    (run : Run graph start n finish) : ∀ vertex, alive finish vertex → alive start vertex := by
  induction run with
  | done => exact fun _ h => h
  | next tail ih => exact fun vertex live => tick_alive_subset graph _ vertex (ih vertex live)

theorem Run.preserves_safe (graph : Graph V E) {start finish : State V E} {n : Nat}
    (run : Run graph start n finish) (inv : Invariant graph start)
    (kept : V → Prop) (safe : graph.SafeSet kept) (subset : ∀ vertex, kept vertex → alive start vertex) :
    ∀ vertex, kept vertex → alive finish vertex := by
  induction run with
  | done => exact subset
  | next tail ih => exact ih (tick_preserves graph _ inv) (tick_preserves_safe graph _ inv kept safe subset)

omit [DecidableEq V] [DecidableEq E] in
theorem support_at_boundary (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (boundary : state.work = []) (vertex : V) (live : alive state vertex) (edge : E) :
    (graph.view vertex).safe (state.counters vertex) edge ↔ graph.safe (alive state) vertex edge := by
  constructor
  · intro support
    rcases support with good | ⟨internal, unseen⟩
    · exact Or.inl good
    · right
      refine ⟨internal, ?_⟩
      cases dead : state.deleted (graph.target edge) with
      | false => exact dead
      | true =>
        rcases inv.complete vertex live edge internal dead with seen | waiting
        · have same := inv.history vertex live edge internal
          rw [seen, unseen] at same
          cases same
        · rw [boundary] at waiting; cases waiting
  · intro support
    exact safe_subset_supported graph state inv (alive state) (fun _ h => h) vertex live edge support

omit [DecidableEq V] [DecidableEq E] in
theorem canStay_at_boundary (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (boundary : state.work = []) (vertex : V) (live : alive state vertex) :
    (graph.view vertex).canStay (graph.own vertex) (state.counters vertex) ↔ graph.canStay (alive state) vertex := by
  constructor <;> intro stay <;> constructor
  · intro own
    obtain ⟨e, legal, support⟩ := stay.1 own
    exact ⟨e, legal, (support_at_boundary graph state inv boundary vertex live e).mp support⟩
  · intro other e legal
    exact (support_at_boundary graph state inv boundary vertex live e).mp (stay.2 other e legal)
  · intro own
    obtain ⟨e, legal, support⟩ := stay.1 own
    exact ⟨e, legal, (support_at_boundary graph state inv boundary vertex live e).mpr support⟩
  · intro other e legal
    exact (support_at_boundary graph state inv boundary vertex live e).mpr (stay.2 other e legal)

omit [DecidableEq V] [DecidableEq E] in
theorem halted_safe (graph : Graph V E) (state : State V E) (inv : Invariant graph state)
    (boundary : state.work = []) (empty : state.pending = []) : graph.SafeSet (alive state) := by
  intro vertex live
  apply (canStay_at_boundary graph state inv boundary vertex live).mp
  apply Classical.byContradiction
  intro rejected
  have queued := inv.queue_complete vertex live rejected
  rw [empty] at queued
  cases queued

/-- 初期分類された局所グラフについて、停止時の生存集合は初期候補内の最大安全集合である。 -/
theorem greatest_at_halt (graph : Graph V E) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    {finish : State V E} {n : Nat} (run : Run graph (initial graph vertices) n finish)
    (boundary : finish.work = []) (empty : finish.pending = []) :
    graph.SafeSet (alive finish) ∧ (∀ vertex, alive finish vertex → graph.eligible vertex = true) ∧
      ∀ kept, graph.SafeSet kept → (∀ vertex, kept vertex → graph.eligible vertex = true) →
        ∀ vertex, kept vertex → alive finish vertex := by
  have inv := initial_invariant graph vertices covered
  refine ⟨halted_safe graph finish (run.invariant graph inv) boundary empty, ?_, ?_⟩
  · intro vertex live
    have was_live := run.alive_subset graph vertex live
    simpa only [alive, initial, Bool.not_eq_false'] using was_live
  · intro kept safe subset
    apply run.preserves_safe graph inv kept safe
    intro vertex member
    simp only [alive, initial, Bool.not_eq_false']
    exact subset vertex member

end PetaProof.SafetyExecution
