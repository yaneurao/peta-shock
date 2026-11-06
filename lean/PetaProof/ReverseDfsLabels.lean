import PetaProof.ReverseDfsStack

namespace PetaProof.ReverseDfsStack

universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem pop_result (state : State V) : (pop state).result = state.result := by
  cases pending : state.pending <;> simp [pop, pending]

/-- 割当済みの頂点は、別の成分の探索でも上書きしない。 -/
theorem push_label_stable (id : Nat) (state : State V) (target vertex : V) (label : Nat)
    (assigned : state.result vertex = some label) :
    (push id state target).result vertex = some label := by
  cases found : state.result target with
  | some old => simpa [push, found] using assigned
  | none =>
    have different : vertex ≠ target := by
      intro same
      subst vertex
      rw [found] at assigned
      cases assigned
    simpa [push, found, different] using assigned

theorem push_label_cases (id : Nat) (state : State V) (target vertex : V) :
    (push id state target).result vertex = state.result vertex ∨
    (push id state target).result vertex = some id := by
  cases found : state.result target with
  | some old => exact Or.inl (by simp [push, found])
  | none =>
    by_cases same : vertex = target
    · exact Or.inr (by simp [push, found, same])
    · exact Or.inl (by simp [push, found, same])

theorem Run.label_stable {id : Nat} {start state : State V} (run : Run id start state)
    (vertex : V) (label : Nat) (assigned : start.result vertex = some label) :
    state.result vertex = some label := by
  induction run with
  | refl => exact assigned
  | push _ target ih => exact push_label_stable id _ target vertex label ih
  | pop _ ih => simpa only [pop_result] using ih

theorem Run.label_cases {id : Nat} {start state : State V} (run : Run id start state)
    (vertex : V) : state.result vertex = start.result vertex ∨ state.result vertex = some id := by
  induction run with
  | refl => exact Or.inl rfl
  | push prior target ih =>
    rcases push_label_cases id _ target vertex with same | current
    · rcases ih with old | current
      · exact Or.inl (same.trans old)
      · exact Or.inr (same.trans current)
    · exact Or.inr current
  | pop _ ih => simpa only [pop_result] using ih

theorem visit_run (id : Nat) (parents : V → List V) (state : State V) :
    Run id state (visit id parents state) := by
  cases pending : state.pending with
  | nil => simpa [visit, pending] using Run.refl (id := id) state
  | cons vertex rest =>
    simpa only [visit, pending] using
      (Run.pop (Run.refl state)).trans (scan_run id (parents vertex) (pop state))

theorem walk_run (id : Nat) (parents : V → List V) (fuel : Nat) (state : State V) :
    Run id state (walk id parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl state
  | succ fuel ih => exact (visit_run id parents state).trans (ih _)

end PetaProof.ReverseDfsStack
