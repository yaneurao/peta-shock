import PetaProof.EscapeAdmission

/-! 重複を許す目標一覧から、距離0の一意な初期キューと確定結果を作る。 -/
namespace PetaProof.EscapeFifo

universe u
variable {V : Type u} [DecidableEq V]

theorem push_seen_iff (state : State V) (vertex : V) (distance : Nat) (other : V) :
    (push state vertex distance).seen other = true ↔ other = vertex ∨ state.seen other = true := by
  cases flag : state.seen vertex with
  | false => simp only [push, flag, Bool.false_eq_true, ite_false, markSeen_true_iff]
  | true =>
    by_cases same : other = vertex
    · subst other
      simp [push, flag]
    · simp [push, flag, same]

theorem pushMany_seen_iff (distance : Nat) (state : State V) (vertices : List V) (other : V) :
    (pushMany distance state vertices).seen other = true ↔ other ∈ vertices ∨ state.seen other = true := by
  induction vertices generalizing state with
  | nil => simp [pushMany]
  | cons head rest ih =>
    rw [pushMany, ih, push_seen_iff]
    simp only [List.mem_cons, or_left_comm, or_assoc]

def Uniform (state : State V) (distance : Nat) : Prop :=
  ∀ item ∈ state.total, item.2 = distance

theorem push_uniform (state : State V) (distance : Nat) (uniform : Uniform state distance) (vertex : V) :
    Uniform (push state vertex distance) distance := by
  cases flag : state.seen vertex with
  | true => simpa only [push, flag, ite_true] using uniform
  | false =>
    intro item member
    have choices : item ∈ state.total ++ [(vertex, distance)] := by
      simpa [push, flag, State.total, List.append_assoc] using member
    rcases List.mem_append.mp choices with old | added
    · exact uniform item old
    · have same : item = (vertex, distance) := by simpa using added
      subst item
      rfl

theorem pushMany_uniform (distance : Nat) (state : State V) (uniform : Uniform state distance) (vertices : List V) :
    Uniform (pushMany distance state vertices) distance := by
  induction vertices generalizing state with
  | nil => exact uniform
  | cons head rest ih => exact ih _ (push_uniform state distance uniform head)

theorem seeded_uniform (goals : List V) : Uniform (seeded goals) 0 :=
  pushMany_uniform 0 initial (by intro item member; cases member) goals

theorem seeded_seen_iff (goals : List V) (vertex : V) :
    (seeded goals).seen vertex = true ↔ vertex ∈ goals := by
  simpa [seeded, initial] using pushMany_seen_iff 0 (initial : State V) goals vertex

theorem seeded_member (goals : List V) (vertex : V) (distance : Nat) :
    (vertex, distance) ∈ (seeded goals).total ↔ vertex ∈ goals ∧ distance = 0 := by
  have inv := seeded_invariant goals
  constructor
  · intro member
    have flagged := (inv.seen_exact vertex).mpr (List.mem_map.mpr ⟨(vertex, distance), member, rfl⟩)
    exact ⟨(seeded_seen_iff goals vertex).mp flagged, seeded_uniform goals _ member⟩
  · rintro ⟨member, zero⟩
    obtain ⟨item, logged, same⟩ := List.mem_map.mp ((inv.seen_exact vertex).mp ((seeded_seen_iff goals vertex).mpr member))
    have cost := seeded_uniform goals item logged
    have equal : item = (vertex, distance) := Prod.ext same (cost.trans zero.symm)
    exact equal ▸ logged

theorem seeded_popped (goals : List V) : (seeded goals).popped = [] := by
  exact pushMany_popped 0 initial goals

theorem seeded_nonempty (goals : List V) (nonempty : goals ≠ []) : (seeded goals).pending ≠ [] := by
  cases goals with
  | nil => exact False.elim (nonempty rfl)
  | cons head rest =>
    intro empty
    have member := (seeded_member (head :: rest) head 0).mpr ⟨by simp, rfl⟩
    simp only [State.total, seeded_popped, empty, List.nil_append, List.not_mem_nil] at member

end PetaProof.EscapeFifo

namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

omit [DecidableEq E] in
/-- 最初のpop後も、目標の距離0と初期キューのラベルが双方向に一致する。 -/
theorem initialGoals_coherent (goals : List V) (head : V × Nat) :
    Coherent (initialGoals input (fun vertex => decide (vertex ∈ goals))
      ⟨head.1, head.2, EscapeFifo.pop (EscapeFifo.seeded goals)⟩) := by
  intro vertex distance
  change (if decide (vertex ∈ goals) then
      { EscapeCounter.initial (input.outgoing vertex) with result := some 0 }
      else EscapeCounter.initial (input.outgoing vertex)).result = some distance ↔
    (vertex, distance) ∈ (EscapeFifo.pop (EscapeFifo.seeded goals)).total
  rw [EscapeFifo.pop_total, EscapeFifo.seeded_member]
  by_cases goal : vertex ∈ goals <;> simp [goal, EscapeCounter.initial, eq_comm]

end PetaProof.EscapePropagation.State
