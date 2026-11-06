import PetaProof.RecordedMaximum

/-!
固定閾値内で、通常通知・局所追加・popと初回値書込みを一緒に追う。
機械的な記録規則の証明であり、通知の安全性や局所集合の正しさは別の証拠を要する。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

inductive RecordedPhase (indexed : G.IndexedMoves E) (level : Int)
    (initial : PropagationState V E) (initialValues : V → Int) : PropagationState V E → (V → Int) → Prop
  | initial : RecordedPhase indexed level initial initialValues initial initialValues
  | notify {state values} : RecordedPhase indexed level initial initialValues state values → (edge : E) →
      RecordedPhase indexed level initial initialValues (state.notify indexed edge)
        (if ((state.notify indexed edge).counters (indexed.source edge)).admitted then
          writeAdmission values level (indexed.source edge) else values)
  | batch {state values} : RecordedPhase indexed level initial initialValues state values → (vertices : List V) →
      RecordedPhase indexed level initial initialValues (state.addMany vertices) (writeAdmissions values level vertices)
  | pop {state values} : RecordedPhase indexed level initial initialValues state values →
      RecordedPhase indexed level initial initialValues state.pop values

/-- 各要素への実書込み列を、閾値終了時の集合での一回の記録へ縮約できる。 -/
theorem RecordedPhase.invariants (indexed : G.IndexedMoves E) (level : Int) (positive : 0 < level)
    (initial : PropagationState V E) (initialValues : V → Int)
    (initial_rep : ∀ vertex, initial.won vertex ↔ initialValues vertex ≠ 0)
    {state : PropagationState V E} {values : V → Int}
    (run : RecordedPhase indexed level initial initialValues state values) :
    (∀ vertex, state.won vertex ↔ values vertex ≠ 0) ∧
      values = latchValues initialValues level (fun vertex => (state.counters vertex).admitted) := by
  have nonzero : level ≠ 0 := by omega
  induction run with
  | initial => exact ⟨initial_rep, (latch_existing initialValues level _ initial_rep).symm⟩
  | @notify state values _ edge ih =>
    rw [record_notified_parent indexed state values level edge ih.1]
    constructor
    · intro vertex
      exact latch_represents values level _ nonzero
        (fun child recorded => PropagationState.won_notify_mono indexed state edge child ((ih.1 child).mpr recorded)) vertex
    · rw [ih.2]
      exact latch_compose initialValues level _ _ (PropagationState.won_notify_mono indexed state edge)
  | @batch state values _ vertices ih =>
    rw [record_added_vertices state values level vertices ih.1]
    have monotone : ∀ vertex, state.won vertex → (state.addMany vertices).won vertex :=
      fun vertex inside => (PropagationState.won_addMany_iff state vertices vertex).mpr (Or.inl inside)
    constructor
    · intro vertex
      exact latch_represents values level _ nonzero
        (fun child recorded => monotone child ((ih.1 child).mpr recorded)) vertex
    · rw [ih.2]
      exact latch_compose initialValues level _ _ monotone
  | pop _ ih => exact ih

end PetaProof.ThresholdGame
