import PetaProof.EscapePropagation

/-! 現在pop中の子の全逆辺を順に通知し、全親・全体履歴の不変条件を保つ。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

private theorem parent_position (own : Bool) (frame : EscapeFifo.Frame V) (parent : V)
    (counter : EscapeCounter.State E) (edge : E) :
    (frame.notifyParent own parent counter edge).2.child = frame.child ∧
      (frame.notifyParent own parent counter edge).2.distance = frame.distance := by
  unfold EscapeFifo.Frame.notifyParent
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    cases (EscapeCounter.hit own counter edge frame.distance).result <;> exact ⟨rfl, rfl⟩

theorem notify_position (state : State V E) (edge : E) :
    (notify input state edge).frame.child = state.frame.child ∧
      (notify input state edge).frame.distance = state.frame.distance :=
  parent_position (input.own (input.source edge)) state.frame (input.source edge) (state.counters (input.source edge)) edge

theorem notify_popped (state : State V E) (edge : E) :
    (notify input state edge).frame.queue.popped = state.frame.queue.popped :=
  notifyKnown_popped input (state.record edge) edge

theorem notify_notified (state : State V E) (edge : E) :
    (notify input state edge).notified = markSeen state.notified edge := rfl

def notifyMany (state : State V E) : List E → State V E
  | [] => state
  | edge :: rest => notifyMany (notify input state edge) rest

theorem notifyMany_preserves (state : State V E) (inv : Invariant input state)
    (edges : List E) (unique : edges.Nodup) (fresh : ∀ edge ∈ edges, state.notified edge = false)
    (current : ∀ edge ∈ edges, input.child edge = state.frame.child) :
    Invariant input (notifyMany input state edges) := by
  induction edges generalizing state with
  | nil => exact inv
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    apply ih (notify input state edge)
      (notify_preserves input state inv edge (fresh edge (by simp)) (current edge (by simp))) parts.2
    · intro other member
      rw [notify_notified]
      have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
      simp only [markSeen, if_neg different]
      exact fresh other (by simp [member])
    · intro other member
      exact (current other (by simp [member])).trans (notify_position input state edge).1.symm

theorem notifyMany_position (state : State V E) (edges : List E) :
    (notifyMany input state edges).frame.child = state.frame.child ∧
      (notifyMany input state edges).frame.distance = state.frame.distance := by
  induction edges generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons edge rest ih =>
    have tail := ih (notify input state edge)
    have head := notify_position input state edge
    exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

theorem notifyMany_popped (state : State V E) (edges : List E) :
    (notifyMany input state edges).frame.queue.popped = state.frame.queue.popped := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih => exact (ih (notify input state edge)).trans (notify_popped input state edge)

theorem notifyMany_notified (state : State V E) (edges : List E) :
    (notifyMany input state edges).notified = EscapeReverseEdges.Input.markAll state.notified edges := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih => exact ih (notify input state edge)

def notifyIncoming (state : State V E) : State V E :=
  notifyMany input state (input.incoming state.frame.child)

/-- 完全な逆辺表を渡すので、全親への通知対象を外から別途列挙する必要はない。 -/
theorem notifyIncoming_preserves (state : State V E) (inv : Invariant input state)
    (fresh : ∀ edge ∈ input.incoming state.frame.child, state.notified edge = false) :
    Invariant input (notifyIncoming input state) :=
  notifyMany_preserves input state inv _ (input.incoming_unique _) fresh
    (fun edge member => (input.incoming_correct _ edge).mp member)

theorem notifyIncoming_complete (state : State V E) (edge : E) :
    (notifyIncoming input state).notified edge = true ↔
      input.child edge = state.frame.child ∨ state.notified edge = true := by
  rw [notifyIncoming, notifyMany_notified, EscapeReverseEdges.Input.markAll_spec]
  rw [input.incoming_correct]

omit [DecidableEq V] [DecidableEq E] in
/-- 自分番が未確定のままなら、その出辺はどれもまだ通知されていない。 -/
theorem pending_own_unreported (state : State V E) (inv : Invariant input state) (vertex : V)
    (own : input.own vertex = true) (pending : (state.counters vertex).result = none)
    (edge : E) (member : edge ∈ input.outgoing vertex) : state.notified edge = false := by
  rw [← inv.pending_history vertex pending edge member]
  exact inv.own_empty vertex own pending edge member

omit [DecidableEq V] [DecidableEq E] in
/-- 未確定親には少なくとも一つ未通知辺が残る。残数が正という不変条件から導く。 -/
theorem pending_missing (state : State V E) (inv : Invariant input state) (vertex : V)
    (pending : (state.counters vertex).result = none) :
    ∃ edge ∈ input.outgoing vertex, state.notified edge = false := by
  classical
  apply Classical.byContradiction
  intro missing
  have allSeen : ∀ edge ∈ input.outgoing vertex, (state.counters vertex).seen edge = true := by
    intro edge member
    rw [inv.pending_history vertex pending edge member]
    cases flag : state.notified edge with
    | true => rfl
    | false => exact False.elim (missing ⟨edge, member, flag⟩)
  have zero := (remaining_zero_iff _ _).mpr allSeen
  have exactCount := (inv.counters vertex).exact_count pending
  have positive := (inv.counters vertex).positive pending
  omega

end PetaProof.EscapePropagation.State
