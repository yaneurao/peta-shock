import PetaProof.EscapeFifoNotify
import PetaProof.EscapeReverseEdges

/-! 全親のカウンターを一つの実行状態にまとめる。完成済み距離表を入力しない。 -/
namespace PetaProof.EscapePropagation

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

structure Input (V : Type u) (E : Type v) extends EscapeReverseEdges.Input V E where
  source : E → V
  outgoing : V → List E
  outgoing_correct : ∀ vertex edge, edge ∈ outgoing vertex ↔ source edge = vertex
  outgoing_unique : ∀ vertex, (outgoing vertex).Nodup
  outgoing_nonempty : ∀ vertex, 0 < (outgoing vertex).length
  own : V → Bool

structure State (V : Type u) (E : Type v) where
  frame : EscapeFifo.Frame V
  counters : V → EscapeCounter.State E
  notified : E → Bool
  received : E → Nat

namespace State
variable (input : Input V E)

/-- receivedは実際の通知距離の証明用記録。未通知辺の値は使用しない。 -/
structure Invariant (state : State V E) : Prop where
  frame : state.frame.Invariant
  counters : ∀ vertex, EscapeCounter.Invariant (input.outgoing vertex) state.received (state.counters vertex)
  seen_notified : ∀ vertex edge, edge ∈ input.outgoing vertex →
    (state.counters vertex).seen edge = true → state.notified edge = true
  pending_history : ∀ vertex, (state.counters vertex).result = none →
    ∀ edge ∈ input.outgoing vertex, (state.counters vertex).seen edge = state.notified edge
  own_empty : ∀ vertex, input.own vertex = true → (state.counters vertex).result = none →
    ∀ edge ∈ input.outgoing vertex, (state.counters vertex).seen edge = false
  notified_logged : ∀ edge, state.notified edge = true →
    (input.child edge, state.received edge) ∈ state.frame.queue.popped

def initial (frame : EscapeFifo.Frame V) : State V E :=
  ⟨frame, fun vertex => EscapeCounter.initial (input.outgoing vertex), fun _ => false, fun _ => 0⟩

omit [DecidableEq V] [DecidableEq E] in
theorem initial_invariant (frame : EscapeFifo.Frame V) (valid : frame.Invariant) :
    Invariant input (initial input frame) := by
  refine ⟨valid, fun vertex => EscapeCounter.initial_invariant _ _ (input.outgoing_nonempty vertex),
    ?_, ?_, ?_, ?_⟩
  · intro vertex edge _ impossible
    cases impossible
  · intro vertex _ edge _
    rfl
  · intro vertex _ _ edge _
    rfl
  · intro edge impossible
    cases impossible

/-- 目標の距離0は最初から確定させ、自己辺などで上書きしない。 -/
def initialGoals (goals : V → Bool) (frame : EscapeFifo.Frame V) : State V E :=
  let base := initial input frame
  { base with
    counters := fun vertex =>
      let counter := EscapeCounter.initial (input.outgoing vertex)
      if goals vertex then { counter with result := some 0 } else counter }

omit [DecidableEq V] [DecidableEq E] in
theorem initialGoals_invariant (goals : V → Bool) (frame : EscapeFifo.Frame V) (valid : frame.Invariant) :
    Invariant input (initialGoals input goals frame) := by
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertex
    cases goal : goals vertex with
    | false => simpa only [initialGoals, goal, Bool.false_eq_true, ite_false] using
        EscapeCounter.initial_invariant (input.outgoing vertex) (fun _ => 0) (input.outgoing_nonempty vertex)
    | true =>
      constructor
      · simp [initialGoals, goal]
      · simp [initialGoals, goal]
      · simp [initialGoals, goal, EscapeCounter.initial, EscapeCounter.seenMaximum_initial]
  · intro vertex edge _ seen
    cases goal : goals vertex <;> simp [initialGoals, goal, EscapeCounter.initial] at seen
  · intro vertex _ edge _
    cases goal : goals vertex <;> simp [initialGoals, initial, goal, EscapeCounter.initial]
  · intro vertex _ _ edge _
    cases goal : goals vertex <;> simp [initialGoals, goal, EscapeCounter.initial]
  · intro edge impossible
    cases impossible

omit [DecidableEq E] in
private theorem maximum_congr (seen : E → Bool) (first second : E → Nat) (edges : List E)
    (same : ∀ edge ∈ edges, seen edge = true → first edge = second edge) :
    EscapeCounter.seenMaximum seen first edges = EscapeCounter.seenMaximum seen second edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
    have tail := ih (fun other member => same other (by simp [member]))
    cases present : seen edge with
    | false => simp [EscapeCounter.seenMaximum, present, tail]
    | true => simp [EscapeCounter.seenMaximum, present, tail, same edge (by simp) present]

def record (state : State V E) (edge : E) : State V E :=
  { state with received := fun other => if other = edge then state.frame.distance else state.received other }

omit [DecidableEq V] in
/-- 未通知辺に今回の距離を記録しても、既に使った最大値とpop対応は変わらない。 -/
theorem record_preserves (state : State V E) (inv : Invariant input state) (edge : E)
    (fresh : state.notified edge = false) : Invariant input (state.record edge) := by
  refine ⟨inv.frame, ?_, inv.seen_notified, inv.pending_history, inv.own_empty, ?_⟩
  · intro vertex
    have prior := inv.counters vertex
    refine ⟨prior.exact_count, prior.positive, prior.exact_peak.trans ?_⟩
    apply maximum_congr
    intro other member seen
    have different : other ≠ edge := by
      intro equal
      subst other
      have impossible := inv.seen_notified vertex edge member seen
      rw [fresh] at impossible
      cases impossible
    simp [record, different]
  · intro other notified
    change state.notified other = true at notified
    have different : other ≠ edge := by
      intro equal
      subst other
      rw [fresh] at notified
      cases notified
    simpa only [record, if_neg different] using inv.notified_logged other notified

/-- 距離が記録済みの一通知。親以外のカウンターは変更しない。 -/
def notifyKnown (state : State V E) (edge : E) : State V E :=
  let parent := input.source edge
  let next := state.frame.notifyParent (input.own parent) parent (state.counters parent) edge
  { frame := next.2
    counters := fun vertex => if vertex = parent then next.1 else state.counters vertex
    notified := markSeen state.notified edge
    received := state.received }

theorem notifyKnown_popped (state : State V E) (edge : E) :
    (notifyKnown input state edge).frame.queue.popped = state.frame.queue.popped := by
  dsimp only [notifyKnown]
  unfold EscapeFifo.Frame.notifyParent
  split
  · rfl
  · exact EscapeFifo.Frame.commit_popped _ _ _

private theorem next_seen (state : State V E) (edge other : E)
    (seen : (state.frame.notifyParent (input.own (input.source edge)) (input.source edge)
      (state.counters (input.source edge)) edge).1.seen other = true) :
    other = edge ∨ (state.counters (input.source edge)).seen other = true := by
  unfold EscapeFifo.Frame.notifyParent at seen
  split at seen
  · exact Or.inr seen
  · rename_i pending
    have absent : (state.counters (input.source edge)).result = none := by
      cases result : (state.counters (input.source edge)).result with
      | none => rfl
      | some distance => simp [result] at pending
    simp only [EscapeCounter.hit, absent, Option.isSome_none, Bool.false_eq_true, ite_false] at seen
    exact (markSeen_true_iff _ _ _).mp seen

theorem notifyKnown_preserves (state : State V E) (inv : Invariant input state) (edge : E)
    (fresh : state.notified edge = false) (currentChild : input.child edge = state.frame.child)
    (currentCost : state.received edge = state.frame.distance) :
    Invariant input (notifyKnown input state edge) := by
  let parent := input.source edge
  let next := state.frame.notifyParent (input.own parent) parent (state.counters parent) edge
  have member : edge ∈ input.outgoing parent := (input.outgoing_correct parent edge).mpr rfl
  have localInv : EscapeCounter.Invariant (input.outgoing parent) state.received next.1 ∧
      next.2.Invariant := by
    cases result : (state.counters parent).result with
    | none =>
      have localFresh : (state.counters parent).seen edge = false := by
        rw [inv.pending_history parent result edge member, fresh]
      have reported : state.frame.Reported (input.outgoing parent) input.child state.received
          (state.counters parent) := fun other inRow seen =>
        inv.notified_logged other (inv.seen_notified parent other inRow seen)
      have kept := EscapeFifo.Frame.notifyParent_preserves (input.own parent) state.frame inv.frame parent
        (input.outgoing parent) (input.outgoing_unique parent) input.child state.received
        (state.counters parent) (inv.counters parent) reported edge member localFresh result currentChild currentCost
      exact ⟨kept.1, kept.2.1⟩
    | some distance =>
      have frozen := EscapeFifo.Frame.notifyParent_frozen (input.own parent) state.frame parent
        (state.counters parent) edge (by simp [result])
      simpa only [next, frozen] using And.intro (inv.counters parent) inv.frame
  refine ⟨localInv.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertex
    change EscapeCounter.Invariant (input.outgoing vertex) state.received
      (if vertex = parent then next.1 else state.counters vertex)
    by_cases same : vertex = parent
    · subst vertex
      simpa only [if_pos rfl] using localInv.1
    · simpa only [if_neg same] using inv.counters vertex
  · intro vertex other inRow seen
    change (if vertex = parent then next.1 else state.counters vertex).seen other = true at seen
    change markSeen state.notified edge other = true
    apply (markSeen_true_iff _ _ _).mpr
    by_cases same : vertex = parent
    · subst vertex
      have present : next.1.seen other = true := by simpa only [if_pos rfl] using seen
      rcases next_seen input state edge other present with equal | old
      · exact Or.inl equal
      · exact Or.inr (inv.seen_notified parent other inRow old)
    · have old : (state.counters vertex).seen other = true := by simpa only [if_neg same] using seen
      exact Or.inr (inv.seen_notified vertex other inRow old)
  · intro vertex pending other inRow
    change (if vertex = parent then next.1 else state.counters vertex).result = none at pending
    change (if vertex = parent then next.1 else state.counters vertex).seen other = markSeen state.notified edge other
    by_cases same : vertex = parent
    · subst vertex
      have nextPending : next.1.result = none := by simpa only [if_pos rfl] using pending
      have oldPending : (state.counters parent).result = none := by
        cases result : (state.counters parent).result with
        | none => rfl
        | some distance => simp [next, EscapeFifo.Frame.notifyParent, result] at nextPending
      cases own : input.own parent with
      | true =>
        simp [next, EscapeFifo.Frame.notifyParent, EscapeCounter.hit, oldPending, own] at nextPending
      | false =>
        simp only [if_pos rfl]
        simp only [next, EscapeFifo.Frame.notifyParent, oldPending, Option.isSome_none,
          Bool.false_eq_true, ite_false, EscapeCounter.hit, own, ite_true]
        by_cases equal : other = edge
        · simp [markSeen, equal]
        · simp only [markSeen, if_neg equal]
          exact inv.pending_history parent oldPending other inRow
    · have different : other ≠ edge := by
        intro equal
        subst other
        exact same ((input.outgoing_correct vertex edge).mp inRow).symm
      have oldPending : (state.counters vertex).result = none := by
        simpa only [if_neg same] using pending
      simpa only [if_neg same, markSeen, if_neg different] using
        inv.pending_history vertex oldPending other inRow
  · intro vertex own pending other inRow
    change (if vertex = parent then next.1 else state.counters vertex).result = none at pending
    change (if vertex = parent then next.1 else state.counters vertex).seen other = false
    by_cases same : vertex = parent
    · subst vertex
      have nextPending : next.1.result = none := by simpa only [if_pos rfl] using pending
      cases result : (state.counters parent).result with
      | none => simp [next, EscapeFifo.Frame.notifyParent, EscapeCounter.hit, result, own] at nextPending
      | some distance => simp [next, EscapeFifo.Frame.notifyParent, result] at nextPending
    · have oldPending : (state.counters vertex).result = none := by simpa only [if_neg same] using pending
      simpa only [if_neg same] using inv.own_empty vertex own oldPending other inRow
  · intro other notified
    change (input.child other, state.received other) ∈ (notifyKnown input state edge).frame.queue.popped
    change markSeen state.notified edge other = true at notified
    rw [notifyKnown_popped]
    rcases (markSeen_true_iff state.notified edge other).mp notified with equal | old
    · subst other
      rw [currentChild, currentCost]
      exact inv.frame.active_logged
    · exact inv.notified_logged other old

/-- 実際のpop距離を記録してから通知する。事前に最終距離を知る必要はない。 -/
def notify (state : State V E) (edge : E) : State V E := notifyKnown input (state.record edge) edge

theorem notify_preserves (state : State V E) (inv : Invariant input state) (edge : E)
    (fresh : state.notified edge = false) (currentChild : input.child edge = state.frame.child) :
    Invariant input (notify input state edge) := by
  apply notifyKnown_preserves input (state.record edge) (record_preserves input state inv edge fresh) edge fresh currentChild
  simp [record]

end State
end PetaProof.EscapePropagation
