import PetaProof.EscapeSeed

/-! 任意の目標一覧から初回popと全逆辺通知を実行する。空目標は処理枠を作らない。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

def start (goals : List V) : Option (State V E) :=
  let queue := EscapeFifo.seeded goals
  match queue.pending with
  | [] => none
  | head :: _ =>
    let frame : EscapeFifo.Frame V := ⟨head.1, head.2, EscapeFifo.pop queue⟩
    some (notifyIncoming input (initialGoals input (fun vertex => decide (vertex ∈ goals)) frame))

theorem start_none_iff (goals : List V) : start input goals = none ↔ goals = [] := by
  constructor
  · intro absent
    by_cases empty : goals = []
    · exact empty
    · have nonempty := EscapeFifo.seeded_nonempty goals empty
      cases pending : (EscapeFifo.seeded goals).pending with
      | nil => exact False.elim (nonempty pending)
      | cons head rest => simp [start, pending] at absent
  · intro empty
    subst goals
    rfl

/-- 最初の処理枠・通知の新規性・通知完了を、入力目標から導く。 -/
theorem start_good (goals : List V) (state : State V E) (started : start input goals = some state) :
    Invariant input state ∧ Coherent state ∧ Complete input state := by
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
    have inv : Invariant input initialState := initialGoals_invariant input _ frame valid
    have coherent : Coherent initialState := initialGoals_coherent input goals head
    have fresh : ∀ edge ∈ input.incoming initialState.frame.child, initialState.notified edge = false := by
      intro edge _
      rfl
    refine ⟨notifyIncoming_preserves input initialState inv fresh,
      notifyIncoming_coherent input initialState inv coherent fresh, ?_⟩
    intro edge
    rw [notifyIncoming_complete]
    have logged := notifyMany_popped input initialState (input.incoming initialState.frame.child)
    change (notifyIncoming input initialState).frame.queue.popped = _ at logged
    rw [logged]
    change input.child edge = head.1 ∨ false = true ↔
      input.child edge ∈ (EscapeFifo.pop (EscapeFifo.seeded goals)).popped.map Prod.fst
    simp [EscapeFifo.pop, pending, EscapeFifo.seeded_popped]

theorem start_exists (goals : List V) (nonempty : goals ≠ []) : ∃ state, start input goals = some state := by
  cases result : start input goals with
  | none => exact False.elim (nonempty ((start_none_iff input goals).mp result))
  | some state => exact ⟨state, rfl⟩

theorem started_run_good (goals : List V) (state : State V E) (started : start input goals = some state)
    (fuel : Nat) : Invariant input (run input fuel state) ∧ Coherent (run input fuel state) ∧
      Complete input (run input fuel state) := by
  obtain ⟨inv, coherent, complete⟩ := start_good input goals state started
  exact ⟨run_preserves input fuel state inv, run_coherent input fuel state inv coherent,
    run_complete input fuel state complete⟩

theorem started_run_drained (goals : List V) (state : State V E) (started : start input goals = some state)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    (run input vertices.length state).frame.queue.pending = [] :=
  run_drained input vertices covered vertices.length state (start_good input goals state started).1 (by omega)

theorem start_goal_zero (goals : List V) (state : State V E) (started : start input goals = some state)
    (vertex : V) (goal : vertex ∈ goals) : (state.counters vertex).result = some 0 := by
  cases pending : (EscapeFifo.seeded goals).pending with
  | nil => simp [start, pending] at started
  | cons head rest =>
    let frame : EscapeFifo.Frame V := ⟨head.1, head.2, EscapeFifo.pop (EscapeFifo.seeded goals)⟩
    let initialState := initialGoals input (fun vertex => decide (vertex ∈ goals)) frame
    have equal : notifyIncoming input initialState = state := by
      simpa only [start, pending, Option.some.injEq] using started
    rw [← equal]
    apply notifyMany_result_stable input initialState _ vertex 0
    simp only [initialState, initialGoals, goal, decide_true, ite_true]

theorem started_run_goal_zero (goals : List V) (state : State V E) (started : start input goals = some state)
    (fuel : Nat) (vertex : V) (goal : vertex ∈ goals) :
    ((run input fuel state).counters vertex).result = some 0 :=
  run_result_stable input fuel state vertex 0 (start_goal_zero input goals state started vertex goal)

end PetaProof.EscapePropagation.State
