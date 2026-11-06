import PetaProof.FiniteDeletionResponse

/-! 削除回、有限応手選択、検査の成功・拒否を具体的な数値計算で検査する。 -/
namespace PetaProof.FiniteDeletionExamples

open HistoryArena HistoryArena.DeletionInput

def next (v : Fin 3) : List (Fin 3) := if v = 0 then [1, 2] else [0]
def bad (v _w : Fin 3) : Bool := v != 0

def arena : HistoryArena (Fin 3) where
  edge := fun v w => w ∈ next v
  owner := fun v => v != 0
  player := false
  bad := fun v w => bad v w = true
  moves_exist := by
    intro v
    by_cases zero : v = 0
    · exact ⟨1, by simp [next, zero]⟩
    · exact ⟨0, by simp [next, zero]⟩

def input : DeletionInput arena where
  next := next
  edges := fun _ _ => Iff.rfl
  bad := bad
  bad_correct := fun _ _ => Iff.rfl

theorem first_alive : (input.run 1).alive = #[true, false, false] := by decide
theorem second_alive : (input.run 2).alive = #[false, false, false] := by decide
theorem first_ranks : (input.run 1).ranks = #[1, 1, 1] := by decide
theorem second_ranks : (input.run 2).ranks = #[2, 1, 1] := by decide
theorem later_ranks : (input.run 3).ranks = #[2, 1, 1] := by decide
theorem checked_success : input.checkedCounter.isSome = true := by decide
theorem finite_response : input.response (input.run 3).ranks 1 = 0 := by decide
theorem both_responses : input.response (input.run 3).ranks 1 = 0 ∧
    input.response (input.run 3).ranks 2 = 0 := by decide

theorem refutes_every_root (v : Fin 3) : ¬ arena.HistoryWinning v :=
  (input.checkedCounter_iff.mp checked_success) v

def safeArena : HistoryArena (Fin 1) where
  edge := fun _ _ => True
  owner := fun _ => false
  player := false
  bad := fun _ _ => False
  moves_exist := fun _ => ⟨0, trivial⟩

def safeInput : DeletionInput safeArena where
  next := fun _ => [0]
  edges := by
    intro _ w
    have zero : w = 0 := Fin.ext (by have := w.isLt; omega)
    simp [zero, safeArena]
  bad := fun _ _ => false
  bad_correct := fun _ _ => by simp [safeArena]

theorem safe_survives : (safeInput.run 1).alive = #[true] := by decide
theorem safe_rejected : safeInput.checkedCounter.isSome = false := by decide
theorem safe_no_false_certificate : safeInput.checkedCounter = none := by
  cases found : safeInput.checkedCounter with
  | none => rfl
  | some counter =>
    have rejected := safe_rejected
    simp [found] at rejected

end PetaProof.FiniteDeletionExamples
