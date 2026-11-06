import PetaProof.EscapePropagationRun

/-! 親の確定結果と、pop済み列・待機列を合わせた距離ラベルとの双方向の一致。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

def Coherent (state : State V E) : Prop :=
  ∀ vertex distance, (state.counters vertex).result = some distance ↔
    (vertex, distance) ∈ state.frame.queue.total

omit [DecidableEq V] [DecidableEq E] in
private theorem pending_not_seen (state : State V E) (queueInv : EscapeFifo.Invariant state.frame.queue)
    (coherent : Coherent state) (vertex : V) (pending : (state.counters vertex).result = none) :
    state.frame.queue.seen vertex = false := by
  cases flag : state.frame.queue.seen vertex with
  | false => rfl
  | true =>
    obtain ⟨item, member, same⟩ := List.mem_map.mp ((queueInv.seen_exact vertex).mp flag)
    have known := (coherent vertex item.2).mpr (by simpa only [← same, Prod.eta] using member)
    rw [pending] at known
    cases known

/-- 未確定の親だけを新規投入するので、既存の別距離ラベルと衝突しない。 -/
theorem notifyKnown_coherent (state : State V E) (queueInv : EscapeFifo.Invariant state.frame.queue)
    (coherent : Coherent state) (edge : E) : Coherent (notifyKnown input state edge) := by
  let parent := input.source edge
  cases old : (state.counters parent).result with
  | some prior =>
    intro vertex distance
    by_cases same : vertex = parent
    · subst vertex
      simpa [notifyKnown, EscapeFifo.Frame.notifyParent, parent, old] using coherent parent distance
    · simpa [notifyKnown, EscapeFifo.Frame.notifyParent, parent, old, same] using coherent vertex distance
  | none =>
    have fresh := pending_not_seen state queueInv coherent parent old
    let next := EscapeCounter.hit (input.own parent) (state.counters parent) edge state.frame.distance
    have expand : notifyKnown input state edge = {
        frame := state.frame.commit parent next.result
        counters := fun vertex => if vertex = parent then next else state.counters vertex
        notified := markSeen state.notified edge
        received := state.received } := by
      have oldSource : (state.counters (input.source edge)).result = none := old
      simp only [notifyKnown, EscapeFifo.Frame.notifyParent, oldSource, Option.isSome_none,
        Bool.false_eq_true, ite_false]
      rfl
    have absent (distance : Nat) : (parent, distance) ∉ state.frame.queue.total := by
      intro member
      have impossible := (coherent parent distance).mpr member
      rw [old] at impossible
      cases impossible
    cases result : next.result with
    | none =>
      intro vertex distance
      rw [expand]
      by_cases same : vertex = parent
      · subst vertex
        simp [EscapeFifo.Frame.commit, result, absent]
      · simpa [EscapeFifo.Frame.commit, result, same] using coherent vertex distance
    | some found =>
      intro vertex distance
      rw [expand]
      simp only [result, EscapeFifo.Frame.commit]
      have total : (EscapeFifo.push state.frame.queue parent found).total =
          state.frame.queue.total ++ [(parent, found)] := by
        simp [EscapeFifo.push, fresh, EscapeFifo.State.total, List.append_assoc]
      change (if vertex = parent then next else state.counters vertex).result = some distance ↔
        (vertex, distance) ∈ (EscapeFifo.push state.frame.queue parent found).total
      rw [total, List.mem_append, List.mem_singleton]
      by_cases same : vertex = parent
      · subst vertex
        simp [result, absent, eq_comm]
      · have different : (vertex, distance) ≠ (parent, found) := by
          intro equal
          exact same (congrArg Prod.fst equal)
        simpa only [if_neg same, different, or_false] using coherent vertex distance

theorem notify_coherent (state : State V E) (queueInv : EscapeFifo.Invariant state.frame.queue)
    (coherent : Coherent state) (edge : E) : Coherent (notify input state edge) :=
  notifyKnown_coherent input (state.record edge) queueInv coherent edge

theorem notifyMany_coherent (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (edges : List E) (unique : edges.Nodup) (fresh : ∀ edge ∈ edges, state.notified edge = false)
    (current : ∀ edge ∈ edges, input.child edge = state.frame.child) :
    Coherent (notifyMany input state edges) := by
  induction edges generalizing state with
  | nil => exact coherent
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    apply ih (notify input state edge)
      (notify_preserves input state inv edge (fresh edge (by simp)) (current edge (by simp)))
      (notify_coherent input state inv.frame.queue coherent edge) parts.2
    · intro other member
      rw [notify_notified]
      have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
      simp only [markSeen, if_neg different]
      exact fresh other (by simp [member])
    · intro other member
      exact (current other (by simp [member])).trans (notify_position input state edge).1.symm

theorem notifyIncoming_coherent (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (fresh : ∀ edge ∈ input.incoming state.frame.child, state.notified edge = false) :
    Coherent (notifyIncoming input state) :=
  notifyMany_coherent input state inv coherent _ (input.incoming_unique _) fresh
    (fun edge member => (input.incoming_correct _ edge).mp member)

omit [DecidableEq V] [DecidableEq E] in
theorem openNext_coherent (state : State V E) (coherent : Coherent state) (head : V × Nat) :
    Coherent (state.openNext head) := by
  intro vertex distance
  change (state.counters vertex).result = some distance ↔
    (vertex, distance) ∈ (EscapeFifo.pop state.frame.queue).total
  rw [EscapeFifo.pop_total]
  exact coherent vertex distance

theorem advance_coherent (state : State V E) (inv : Invariant input state) (coherent : Coherent state) :
    Coherent (advance input state) := by
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using coherent
  | cons head rest =>
    simp only [advance, pending]
    exact notifyIncoming_coherent input (state.openNext head)
      (openNext_preserves input state inv head rest pending) (openNext_coherent state coherent head)
      (openNext_fresh input state inv head rest pending)

theorem run_coherent (fuel : Nat) (state : State V E) (inv : Invariant input state) (coherent : Coherent state) :
    Coherent (run input fuel state) := by
  induction fuel generalizing state with
  | zero => exact coherent
  | succ fuel ih => exact ih _ (advance_preserves input state inv) (advance_coherent input state inv coherent)

/-- 既に確定した結果は、他の辺の通知でも同じ親への再通知でも変わらない。 -/
theorem notifyKnown_result_stable (state : State V E) (edge : E) (vertex : V) (distance : Nat)
    (known : (state.counters vertex).result = some distance) :
    ((notifyKnown input state edge).counters vertex).result = some distance := by
  by_cases same : vertex = input.source edge
  · subst vertex
    simp [notifyKnown, EscapeFifo.Frame.notifyParent, known]
  · simpa only [notifyKnown, if_neg same] using known

theorem notify_result_stable (state : State V E) (edge : E) (vertex : V) (distance : Nat)
    (known : (state.counters vertex).result = some distance) :
    ((notify input state edge).counters vertex).result = some distance :=
  notifyKnown_result_stable input (state.record edge) edge vertex distance known

theorem notifyMany_result_stable (state : State V E) (edges : List E) (vertex : V) (distance : Nat)
    (known : (state.counters vertex).result = some distance) :
    ((notifyMany input state edges).counters vertex).result = some distance := by
  induction edges generalizing state with
  | nil => exact known
  | cons edge rest ih => exact ih _ (notify_result_stable input state edge vertex distance known)

theorem advance_result_stable (state : State V E) (vertex : V) (distance : Nat)
    (known : (state.counters vertex).result = some distance) :
    ((advance input state).counters vertex).result = some distance := by
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using known
  | cons head rest =>
    simp only [advance, pending]
    exact notifyMany_result_stable input (state.openNext head) _ vertex distance known

theorem run_result_stable (fuel : Nat) (state : State V E) (vertex : V) (distance : Nat)
    (known : (state.counters vertex).result = some distance) :
    ((run input fuel state).counters vertex).result = some distance := by
  induction fuel generalizing state with
  | zero => exact known
  | succ fuel ih => exact ih _ (advance_result_stable input state vertex distance known)

end PetaProof.EscapePropagation.State
