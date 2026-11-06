import PetaProof.ForwardDfsTimeline

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem active_not_finished (state : State V) (valid : Invariant state) (vertex : V)
    (active : vertex ∈ state.active) : vertex ∉ state.finished := by
  intro finished
  exact (List.pairwise_append.mp valid.unique).2.2 vertex finished vertex active rfl

theorem Timeline.finished_index {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (vertex : V) (member : vertex ∈ state.finished) :
    last.finished.idxOf vertex < state.finished.length := by
  obtain ⟨added, same⟩ := run.finished_extends
  rw [same, List.idxOf_append, if_pos member]
  exact List.idxOf_lt_length member

theorem Timeline.active_future_index {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (valid : Invariant state) (last_valid : Invariant last)
    (empty : last.stack = []) (vertex : V) (active : vertex ∈ state.active) :
    vertex ∈ last.finished ∧ state.finished.length ≤ last.finished.idxOf vertex := by
  have seen := (valid.covers vertex).mpr (List.mem_append_right state.finished active)
  have last_seen := run.seen_stable vertex seen
  have member : vertex ∈ last.finished := by
    have total := (last_valid.covers vertex).mp last_seen
    simpa [State.total, State.active, empty] using total
  refine ⟨member, ?_⟩
  obtain ⟨added, same⟩ := run.finished_extends
  rw [same, List.idxOf_append, if_neg (active_not_finished state valid vertex active)]
  omega

/-- 今終了する頂点の順位は、それまでに終了した頂点数に等しい。 -/
theorem retirement_rank (outgoing : V → List (Option V)) (state last : State V)
    (valid : Invariant state) (frame : Frame V) (rest : List (Frame V))
    (stack : state.stack = frame :: rest) (done : frame.todo = [])
    (tail : Timeline outgoing (tick outgoing state) last) :
    last.finished.idxOf frame.vertex = state.finished.length := by
  have fresh : frame.vertex ∉ state.finished :=
    active_not_finished state valid frame.vertex (by simp [State.active, stack])
  obtain ⟨added, same⟩ := tail.finished_extends
  have combined : last.finished = state.finished ++ (frame.vertex :: added) := by
    simpa [tick, stack, done, retire, List.append_assoc] using same
  rw [combined]
  simp [List.idxOf_append, fresh]

/-- 終了直後も残る祖先は、その頂点より厳密に後で終了する。 -/
theorem retirement_ancestor_later (outgoing : V → List (Option V)) (state last : State V)
    (valid : Invariant state) (last_valid : Invariant last) (empty : last.stack = [])
    (frame : Frame V) (rest : List (Frame V)) (stack : state.stack = frame :: rest)
    (done : frame.todo = []) (tail : Timeline outgoing (tick outgoing state) last)
    (ancestor : V) (below : ancestor ∈ rest.map Frame.vertex) :
    last.finished.idxOf frame.vertex < last.finished.idxOf ancestor := by
  have active : ancestor ∈ (tick outgoing state).active := by
    simpa [tick, stack, done, retire, State.active] using below
  have future := (tail.active_future_index (tick_preserves outgoing state valid) last_valid empty ancestor active).2
  have position := retirement_rank outgoing state last valid frame rest stack done tail
  have length : (tick outgoing state).finished.length = state.finished.length + 1 := by
    simp [tick, stack, done, retire]
  omega

def Retiring (state : State V) (vertex : V) : Prop :=
  ∃ frame rest, state.stack = frame :: rest ∧ frame.vertex = vertex ∧ frame.todo = []

theorem Event.new_finished {outgoing : V → List (Option V)} {state next : State V}
    (event : Event outgoing state next) (vertex : V) (member : vertex ∈ next.finished)
    (fresh : vertex ∉ state.finished) : Retiring state vertex ∧ next = tick outgoing state := by
  cases event with
  | seed target _ => exact False.elim (fresh (by simpa [discover_finished] using member))
  | advance =>
    refine ⟨?_, rfl⟩
    cases stack : state.stack with
    | nil => exact False.elim (fresh (by simpa [tick, stack] using member))
    | cons frame rest =>
      cases todo : frame.todo with
      | nil =>
        have candidates : vertex ∈ state.finished ∨ vertex = frame.vertex := by
          simpa [tick, stack, todo, retire] using member
        exact ⟨frame, rest, stack, (candidates.resolve_left fresh).symm, todo⟩
      | cons target remaining =>
        have old : vertex ∈ state.finished := by
          cases target with
          | none => simpa [tick, stack, todo, trim_finished] using member
          | some child => simpa [tick, stack, todo, discover_finished, trim_finished] using member
        exact False.elim (fresh old)

/-- 最終終了順の新しい頂点には、実際にその頂点を取り除いた時点がある。 -/
theorem Timeline.retirement_witness {outgoing : V → List (Option V)} {state last : State V}
    (run : Timeline outgoing state last) (vertex : V) (member : vertex ∈ last.finished)
    (fresh : vertex ∉ state.finished) :
    ∃ before, Timeline outgoing state before ∧ Retiring before vertex ∧ Timeline outgoing (tick outgoing before) last := by
  induction run with
  | done => exact False.elim (fresh member)
  | @next state middle last event tail ih =>
    by_cases already : vertex ∈ middle.finished
    · obtain ⟨retiring, same⟩ := event.new_finished vertex already fresh
      exact ⟨state, .done state, retiring, by simpa only [same] using tail⟩
    · obtain ⟨before, first, retiring, final⟩ := ih member already
      exact ⟨before, .next event first, retiring, final⟩

end PetaProof.ForwardDfs
