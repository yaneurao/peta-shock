import PetaProof.EscapeSound

/-! 最短性の反対側の不等式。自分番は通知済み全辺、相手番は確定を支える一辺を使う。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

structure Bounds (goals : List V) (state : State V E) : Prop where
  own : ∀ edge, state.notified edge = true → input.own (input.source edge) = true →
    ∃ distance, (state.counters (input.source edge)).result = some distance ∧ distance ≤ state.received edge + 1
  other : ∀ vertex distance, vertex ∉ goals → input.own vertex = false →
    (state.counters vertex).result = some distance →
    ∃ edge ∈ input.outgoing vertex, ∃ cost, (state.counters (input.child edge)).result = some cost ∧ distance ≤ cost + 1

omit [DecidableEq E] in
theorem initialGoals_bounds (goals : List V) (frame : EscapeFifo.Frame V) :
    Bounds input goals (initialGoals input (fun vertex => decide (vertex ∈ goals)) frame) := by
  constructor
  · intro edge impossible
    cases impossible
  · intro vertex distance notGoal _ impossible
    simp [initialGoals, notGoal, EscapeCounter.initial] at impossible

omit [DecidableEq V] in
theorem record_bounds (goals : List V) (state : State V E) (bounds : Bounds input goals state) (edge : E)
    (fresh : state.notified edge = false) : Bounds input goals (state.record edge) := by
  refine ⟨?_, bounds.other⟩
  intro other notified own
  change state.notified other = true at notified
  have different : other ≠ edge := by
    intro equal
    subst other
    rw [fresh] at notified
    cases notified
  simpa only [record, if_neg different] using bounds.own other notified own

private theorem new_own_bound (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (edge : E) (own : input.own (input.source edge) = true) :
    ∃ distance, ((notifyKnown input state edge).counters (input.source edge)).result = some distance ∧
      distance ≤ state.frame.distance + 1 := by
  let parent := input.source edge
  cases prior : (state.counters parent).result with
  | some distance =>
    refine ⟨distance, notifyKnown_result_stable input state edge parent distance prior, ?_⟩
    exact inv.frame.upper _ ((coherent parent distance).mp prior)
  | none =>
    refine ⟨state.frame.distance + 1, ?_, Nat.le_refl _⟩
    have oldSource : (state.counters (input.source edge)).result = none := prior
    simp [notifyKnown, EscapeFifo.Frame.notifyParent, EscapeCounter.hit, oldSource, own]

theorem notifyKnown_bounds (goals : List V) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (bounds : Bounds input goals state) (edge : E)
    (currentChild : input.child edge = state.frame.child) (currentCost : state.received edge = state.frame.distance) :
    Bounds input goals (notifyKnown input state edge) := by
  constructor
  · intro other notified own
    change markSeen state.notified edge other = true at notified
    rcases (markSeen_true_iff _ _ _).mp notified with equal | old
    · subst other
      obtain ⟨distance, known, bound⟩ := new_own_bound input state inv coherent edge own
      exact ⟨distance, known, by simpa only [notifyKnown, currentCost] using bound⟩
    · obtain ⟨distance, known, bound⟩ := bounds.own other old own
      exact ⟨distance, notifyKnown_result_stable input state edge _ distance known, bound⟩
  · intro vertex distance notGoal own known
    let parent := input.source edge
    by_cases same : vertex = parent
    · subst vertex
      cases prior : (state.counters parent).result with
      | some oldDistance =>
        have stable := notifyKnown_result_stable input state edge parent oldDistance prior
        have equal : oldDistance = distance := Option.some.inj (stable.symm.trans known)
        obtain ⟨move, member, cost, childKnown, bound⟩ := bounds.other parent oldDistance notGoal own prior
        exact ⟨move, member, cost, notifyKnown_result_stable input state edge _ cost childKnown, by omega⟩
      | none =>
        have priorSource : (state.counters (input.source edge)).result = none := prior
        have ownSource : input.own (input.source edge) = false := own
        have peak : (state.counters parent).peak ≤ state.frame.distance := by
          rw [(inv.counters parent).exact_peak, EscapeCounter.seenMaximum_bound]
          intro other member seen
          exact inv.frame.past_bound _ (inv.notified_logged other (inv.seen_notified parent other member seen))
        have ready : (if (state.counters parent).left == 1 then some (state.frame.distance + 1) else none) = some distance := by
          simpa only [notifyKnown, EscapeFifo.Frame.notifyParent, priorSource, Option.isSome_none,
            Bool.false_eq_true, ite_false, if_pos rfl, ownSource, EscapeCounter.hit,
            Nat.max_eq_right peak, parent] using known
        have equal : distance = state.frame.distance + 1 := by
          split at ready
          · exact (Option.some.inj ready).symm
          · cases ready
        have childKnown : (state.counters (input.child edge)).result = some state.frame.distance := by
          apply (coherent _ _).mpr
          rw [currentChild]
          exact List.mem_append_left _ inv.frame.active_logged
        refine ⟨edge, (input.outgoing_correct parent edge).mpr rfl, state.frame.distance,
          notifyKnown_result_stable input state edge _ _ childKnown, ?_⟩
        omega
    · have different : vertex ≠ input.source edge := same
      have oldKnown : (state.counters vertex).result = some distance := by
        simpa only [notifyKnown, if_neg different] using known
      obtain ⟨move, member, cost, childKnown, bound⟩ := bounds.other vertex distance notGoal own oldKnown
      exact ⟨move, member, cost, notifyKnown_result_stable input state edge _ cost childKnown, bound⟩

theorem notify_bounds (goals : List V) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (bounds : Bounds input goals state) (edge : E)
    (fresh : state.notified edge = false) (currentChild : input.child edge = state.frame.child) :
    Bounds input goals (notify input state edge) := by
  apply notifyKnown_bounds input goals (state.record edge) (record_preserves input state inv edge fresh)
    coherent (record_bounds input goals state bounds edge fresh) edge currentChild
  simp [record]

theorem notifyMany_bounds (goals : List V) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (bounds : Bounds input goals state) (edges : List E)
    (unique : edges.Nodup) (fresh : ∀ edge ∈ edges, state.notified edge = false)
    (current : ∀ edge ∈ edges, input.child edge = state.frame.child) :
    Bounds input goals (notifyMany input state edges) := by
  induction edges generalizing state with
  | nil => exact bounds
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    apply ih (notify input state edge)
      (notify_preserves input state inv edge (fresh edge (by simp)) (current edge (by simp)))
      (notify_coherent input state inv.frame.queue coherent edge)
      (notify_bounds input goals state inv coherent bounds edge (fresh edge (by simp)) (current edge (by simp))) parts.2
    · intro other member
      rw [notify_notified]
      have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
      simp only [markSeen, if_neg different]
      exact fresh other (by simp [member])
    · intro other member
      exact (current other (by simp [member])).trans (notify_position input state edge).1.symm

theorem advance_bounds (goals : List V) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (bounds : Bounds input goals state) : Bounds input goals (advance input state) := by
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using bounds
  | cons head rest =>
    simp only [advance, pending]
    exact notifyMany_bounds input goals (state.openNext head) (openNext_preserves input state inv head rest pending)
      (openNext_coherent state coherent head) ⟨bounds.own, bounds.other⟩ _ (input.incoming_unique _)
      (openNext_fresh input state inv head rest pending) (fun edge member => (input.incoming_correct _ edge).mp member)

theorem run_bounds (goals : List V) (fuel : Nat) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (bounds : Bounds input goals state) : Bounds input goals (run input fuel state) := by
  induction fuel generalizing state with
  | zero => exact bounds
  | succ fuel ih =>
    exact ih _ (advance_preserves input state inv) (advance_coherent input state inv coherent)
      (advance_bounds input goals state inv coherent bounds)

theorem start_bounds (goals : List V) (state : State V E) (started : start input goals = some state) :
    Bounds input goals state := by
  cases pending : (EscapeFifo.seeded goals).pending with
  | nil => simp [start, pending] at started
  | cons head rest =>
    let frame : EscapeFifo.Frame V := ⟨head.1, head.2, EscapeFifo.pop (EscapeFifo.seeded goals)⟩
    let initialState := initialGoals input (fun vertex => decide (vertex ∈ goals)) frame
    have equal : notifyIncoming input initialState = state := by
      simpa only [start, pending, Option.some.injEq] using started
    rw [← equal]
    have valid : frame.Invariant := EscapeFifo.Frame.begin_preserves (EscapeFifo.seeded goals)
      (EscapeFifo.seeded_invariant goals) head rest pending
    exact notifyMany_bounds input goals initialState (initialGoals_invariant input _ frame valid)
      (initialGoals_coherent input goals head) (initialGoals_bounds input goals frame) _
      (input.incoming_unique _) (by intro edge _; rfl) (fun edge member => (input.incoming_correct _ edge).mp member)

end PetaProof.EscapePropagation.State
