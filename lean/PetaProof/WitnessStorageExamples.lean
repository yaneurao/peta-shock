import PetaProof.DenseWitnessIndex
import PetaProof.CapturedCandidateTable
import PetaProof.GeneratedFamilyExamples

/-! 全状態を保存しない順位記録、代表閾値の直接参照、省略条件と重複条件を検査する。 -/
namespace PetaProof.WitnessStorageExamples

namespace Index

set_option maxRecDepth 4096

def marked (level : Nat) : Bool := level == 20 || level == 30
def table := DenseWitnessIndex.build 40 marked

theorem length_fixed : table.size = 41 := DenseWitnessIndex.build_size _ _
theorem omitted_twenty_one : table[21]? = some 30 := by decide
theorem below_first : table[1]? = some 20 := by decide
theorem above_last : table[31]? = some 40 := by decide
theorem exact_leaf : table[20]? = some 20 := by decide
theorem no_leaves : (DenseWitnessIndex.build 4 (fun _ => false))[1]? = some 4 := by decide
theorem empty_cap : (DenseWitnessIndex.build 0 (fun _ => false)).size = 1 := by decide
theorem specified_work : DenseWitnessIndex.buildWork 40 = 201 := by decide

open ThresholdGame QueueThresholdScanExamples

theorem actual_context_lookup : top.witnessIndex[21]? = some 30 := by
  have same := top.witnessIndex_eq 21 (by decide) (by decide)
  simpa only [GeneratedFamilyExamples.Leaves.gap_representative] using same

end Index

namespace Capture
open SelectiveRankCapture

def requests (level : Nat) : List (Fin 3) :=
  if level = 30 then [0] else if level = 20 then [1] else []

def payload (level state : Nat) (vertex : Fin 3) : Nat :=
  if level = 30 ∧ vertex = 0 then 7 else if level = 20 ∧ vertex = 1 then 9 else 999 + state

def result := run (fun _ state : Nat => state + 1) requests payload [40, 30, 20] 0 (Array.replicate 3 none)

theorem only_requested_cells : result.2 = #[some 7, some 9, none] := by decide
theorem still_three_slots : result.2.size = 3 := by decide
theorem state_not_replayed : result.1 = 3 := by decide
theorem two_reads : reads [40, 30, 20] requests = 2 := by decide
theorem unique_requests : ([40, 30, 20].flatMap requests).Nodup := by decide

theorem later_payload_does_not_change_first : storedRank result.2 (0 : Fin 3) = 7 := by decide
theorem omitted_cell_defaults_zero : storedRank result.2 (2 : Fin 3) = 0 := by decide

def expected (vertex : Fin 3) : Nat := if vertex = 0 then 7 else if vertex = 1 then 9 else 0

theorem correct_only_where_requested (level state : Nat) (vertex : Fin 3)
    (present : vertex ∈ requests level) : payload level (state + 1) vertex = expected vertex := by
  by_cases thirty : level = 30
  · simp only [requests, if_pos thirty, List.mem_singleton] at present
    subst vertex
    simp [payload, expected, thirty]
  · by_cases twenty : level = 20
    · simp only [requests, if_neg thirty, if_pos twenty, List.mem_singleton] at present
      subst vertex
      simp [payload, expected, twenty]
    · simp [requests, thirty, twenty] at present

theorem whole_table_correct (vertex : Fin 3) : storedRank result.2 vertex = expected vertex := by
  apply run_complete (fun _ state : Nat => state + 1) requests payload (fun _ => True) expected
    (fun _ _ _ => trivial) (fun level state _ vertex present => correct_only_where_requested level state vertex present)
    [40, 30, 20] 0 trivial _ vertex
  intro vertex
  by_cases zero : vertex = 0
  · simp [zero, requests]
  · by_cases one : vertex = 1
    · simp [one, requests]
    · exact Or.inr (by simp [expected, zero, one])

/-- 二度要求すると値は保存できても、一度だけ取得という費用条件は満たさない。 -/
theorem duplicates_not_unique : ¬ ([0, 0] : List (Fin 3)).Nodup := by decide

theorem duplicate_write_result : capture (fun _ : Fin 3 => 7) [0, 0] (Array.replicate 3 none) =
    #[some 7, none, none] := by decide

end Capture
end PetaProof.WitnessStorageExamples
