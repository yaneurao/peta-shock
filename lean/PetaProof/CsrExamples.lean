import PetaProof.SccCsrView
import PetaProof.SccIndexedExamples

namespace PetaProof.Csr.Examples

def target (edge : Nat) : Nat := if edge = 0 ∨ edge = 2 then 2 else 0
def edges : List Nat := [0, 1, 2, 3]

/-- 子1と3の入次数は0で、隣接offsetが同じになる。 -/
theorem degrees_and_offsets :
    (List.range 4).map (degrees target edges) = [2, 0, 2, 0] ∧
    (List.range 5).map (offset (degrees target edges)) = [0, 2, 2, 4, 4] := by decide

theorem scattered_storage :
    (List.range 4).map (built target edges).memory = [some 1, some 3, some 0, some 2] := by decide

theorem exact_rows : (List.range 4).map (row target edges) = [[1, 3], [], [0, 2], []] := by decide

theorem cursor_reaches_each_end : (List.range 4).map (built target edges).cursor = [2, 2, 4, 4] := by decide

/-- 辺ID自体が同じでも入力列に2回あれば別スロットへ2回保存する。 -/
theorem duplicate_occurrences_preserved : row target [0, 1, 0] 2 = [0, 0] := by decide

theorem all_writes_safe : WritesWithin edges.length target edges (initial (degrees target edges)) := by
  apply built_writes_within target edges 4
  intro edge member
  simp [edges] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem empty_storage (vertex : Nat) :
    row target [] vertex = [] ∧ (built target []).cursor vertex = 0 := by
  constructor
  · rw [row_exact]; rfl
  · rw [final_cursor]
    have zero : degrees target [] = fun _ => 0 := rfl
    rw [zero]
    induction vertex with
    | zero => rfl
    | succ vertex ih => simpa [offset] using ih

theorem exact_row_by_general_proof (vertex : Nat) : row target edges vertex = bucket target edges vertex :=
  row_exact target edges vertex

def indexed := SccIndexedView.Examples.view
def allow := SccIndexedView.Examples.allow

theorem indexed_storage :
    (List.range 4).map (offset (degrees (SccCsrView.target indexed) (SccCsrView.edges indexed))) = [0, 1, 4, 5] ∧
    (List.range 5).map (built (SccCsrView.target indexed) (SccCsrView.edges indexed)).memory =
      [some 2, some 0, some 1, some 3, some 4] := by decide

theorem indexed_rows :
    (List.finRange 3).map (SccCsrView.incoming indexed) = [[2], [0, 1, 3], [4]] := by decide

theorem csr_cycle_core : SccCsrView.core indexed allow = [0, 1, 2] := by decide

theorem csr_core_by_general_proof (vertex : Fin 3) :
    vertex ∈ SccCsrView.core indexed allow ↔ CyclicVertex (SccIndexedView.relation indexed allow) vertex :=
  SccCsrView.core_correct indexed allow vertex

theorem csr_safe_by_general_proof :
    WritesWithin (SccCsrView.edges indexed).length (SccCsrView.target indexed) (SccCsrView.edges indexed)
      (initial (degrees (SccCsrView.target indexed) (SccCsrView.edges indexed))) :=
  SccCsrView.writes_within indexed

end PetaProof.Csr.Examples
