import PetaProof.SafetyInitialization
import PetaProof.SafetyReturnedChoice

namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

omit [DecidableEq E] in
/-- 実際の初期走査の逆辺配列を親IDへ写すと、親IDを直接appendした結果に一致する。 -/
theorem initialized_parent_buckets (input : Input G E) (vertices : List V) (unique : vertices.Nodup) (vertex : V) :
    ((initializeRows input vertices emptyArrays).incoming vertex).map input.indexed.source =
      buildBuckets (target input) input.indexed.source (allInternal input vertices) (fun _ => []) vertex := by
  rw [(initialize_spec input vertices unique).incoming vertex]
  exact (built_incoming_parents input vertices vertex).symm

/-- 初期count/bad/incoming/queueの逐次構築から、有限削除と具体的な返却方策の保証まで。 -/
theorem initialized_solves (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    ∃ n state, SafetyExecution.Run (initializedGraph input vertices unique covered)
      (executionOf input (initializeRows input vertices emptyArrays)) n state ∧
      SafetyExecution.Stopped state ∧
      Nonempty (G.SafeBatch (fun vertex => input.won vertex = true) (SafetyExecution.alive state)) ∧
      (∀ vertex, SafetyExecution.alive state vertex → G.owner vertex = G.player →
        ∃ edge, returnedIndex input state vertex = some edge) ∧
      ∀ kept, G.SafeSet (fun vertex => input.won vertex = true) kept →
        (∀ vertex, kept vertex → eligible input vertex = true) →
          ∀ vertex, kept vertex → SafetyExecution.alive state vertex := by
  simpa only [initializedGraph_eq input vertices unique covered, initialize_state_eq input vertices unique covered]
    using classified_solves input vertices unique covered

end PetaProof.SafetyClassification
