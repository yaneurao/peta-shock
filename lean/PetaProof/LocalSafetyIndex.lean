import PetaProof.LocalIndex32

namespace PetaProof.LocalIndex

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

omit [DecidableEq E] in
theorem packed32_flag_update (core : List V) (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (flags : V → Bool) (vertex : V) (value : Bool) (member : vertex ∈ core) :
    (core.map flags).set (registered32 core vertex).toUInt32.toNat value = core.map (writeFlag flags vertex value) := by
  have nonnegative : 0 ≤ (registered32 core vertex).toInt := by
    rw [registered32_decodes core bounded, registered_member core unique vertex member]
    omega
  rw [nonnegative32_cast _ nonnegative, registered32_decodes core bounded,
    registered_member core unique vertex member, Int.toNat_ofNat]
  exact (packed_flag_update core unique flags vertex value member).symm

omit [DecidableEq E] in
/-- 初期のlocal_index所属判定と局所alive読込が、core&&!wonに一致する。 -/
theorem eligible_local_guard (input : SafetyClassification.Input G E) (core : List V)
    (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (represented : ∀ vertex, input.core vertex = true ↔ vertex ∈ core) (vertex : V) :
    localFlag32 core (fun vertex => !input.won vertex) vertex = true ↔
      SafetyClassification.eligible input vertex = true := by
  rw [localFlag32_iff core unique bounded]
  simp only [SafetyClassification.eligible, Bool.and_eq_true, Bool.not_eq_true', represented vertex]

omit [DecidableEq E] in
theorem eligible_local_guard_eq (input : SafetyClassification.Input G E) (core : List V)
    (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (represented : ∀ vertex, input.core vertex = true ↔ vertex ∈ core) (vertex : V) :
    localFlag32 core (fun vertex => !input.won vertex) vertex = SafetyClassification.eligible input vertex := by
  have same := eligible_local_guard input core unique bounded represented vertex
  cases left : localFlag32 core (fun vertex => !input.won vertex) vertex <;>
    cases right : SafetyClassification.eligible input vertex <;> simp_all

def indexedInternal (input : SafetyClassification.Input G E) (core : List V) (vertex : V) (edge : E) : Bool :=
  !SafetyClassification.goodFlag input edge && match input.indexed.move edge with
  | .leaf _ => false
  | .node child => localFlag32 core (fun vertex => !input.won vertex) child &&
      (decide (G.owner vertex = G.player) || input.checked vertex child)

omit [DecidableEq E] in
theorem indexedInternal_eq (input : SafetyClassification.Input G E) (core : List V)
    (unique : core.Nodup) (bounded : core.length ≤ 2147483648)
    (represented : ∀ vertex, input.core vertex = true ↔ vertex ∈ core) (vertex : V) (edge : E) :
    indexedInternal input core vertex edge = SafetyClassification.internalFlag input vertex edge := by
  cases move : input.indexed.move edge <;>
    simp only [indexedInternal, SafetyClassification.internalFlag, move,
      eligible_local_guard_eq input core unique bounded represented]

/-- 削除実行後も、生存する頂点は初期core内なので、局所alive参照は全体状態の生存性に一致する。 -/
theorem dynamic_local_guard (input : SafetyClassification.Input G E) (vertices : List V) (unique_vertices : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (core : List V) (unique_core : core.Nodup)
    (bounded : core.length ≤ 2147483648) (represented : ∀ vertex, input.core vertex = true ↔ vertex ∈ core)
    {state : SafetyExecution.State V E} {n : Nat}
    (run : SafetyExecution.Run (SafetyClassification.graph input vertices unique_vertices covered)
      (SafetyExecution.initial (SafetyClassification.graph input vertices unique_vertices covered) vertices) n state)
    (vertex : V) :
    localFlag32 core (fun vertex => !state.deleted vertex) vertex = true ↔ SafetyExecution.alive state vertex := by
  rw [localFlag32_iff core unique_core bounded]
  simp only [Bool.not_eq_true']
  constructor
  · exact And.right
  · intro live
    have initial_live := run.alive_subset _ vertex live
    have active : SafetyClassification.eligible input vertex = true := by
      simpa only [SafetyExecution.alive, SafetyExecution.initial, SafetyClassification.graph, Bool.not_eq_false'] using initial_live
    have in_core : input.core vertex = true := by
      have flags : input.core vertex = true ∧ input.won vertex = false := by
        simpa only [SafetyClassification.eligible, Bool.and_eq_true, Bool.not_eq_true'] using active
      exact flags.1
    exact ⟨(represented vertex).mp in_core, live⟩

end PetaProof.LocalIndex
