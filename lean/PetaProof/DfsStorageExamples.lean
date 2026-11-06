import PetaProof.DfsStorageAccounting
import PetaProof.CheckingRowAccountingExamples

/-! 重複根でも書込は増えず、固定長出力は順序と重複値を保つ。 -/
namespace PetaProof.DfsStorageExamples

def diamond := CheckingRowAccountingExamples.diamond
def cycle := CheckingRowAccountingExamples.cycle

theorem first_duplicate_roots : ForwardDfsStores.forestStores [()]
    (fun _ => [some ()]) [(), (), ()] ForwardDfs.initial = (1, 1) := by decide

theorem second_duplicate_roots : ReverseDfsStores.passStores [()]
    (fun _ => [(), ()]) [(), (), ()] ComponentNumbering.initial = (1, 1) := by decide

theorem initialized_empty : DfsStorage.initializationWork Unit 0 = 0 := by decide
theorem initialized_four : DfsStorage.initializationWork Unit 4 = 16 := by decide

theorem exact_capacity :
    (FixedOutputBuffer.fill [1, 2, 3] (FixedOutputBuffer.initial 3)).data = #[some 1, some 2, some 3] ∧
      (FixedOutputBuffer.fill [1, 2, 3] (FixedOutputBuffer.initial 3)).used = 3 := by decide

theorem repeated_values : (FixedOutputBuffer.fill [1, 1, 2] (FixedOutputBuffer.initial 3)).data =
    #[some 1, some 1, some 2] := by decide

theorem preserve_old_prefix : (FixedOutputBuffer.fill [2, 3]
    (⟨#[some 9, none, none], 1⟩ : FixedOutputBuffer.Buffer Nat)).data[0]? = some (some 9) := by decide

theorem empty_output : FixedOutputBuffer.SafeFill ([] : List Nat) (FixedOutputBuffer.initial 0) := by trivial
theorem over_capacity_not_safe : ¬FixedOutputBuffer.SafeFill [1, 2, 3, 4] (FixedOutputBuffer.initial 3) := by
  simp [FixedOutputBuffer.SafeFill, FixedOutputBuffer.initial, FixedOutputBuffer.append]

theorem diamond_stores : diamond.forwardStores = (4, 4) ∧ diamond.reverseStores = (4, 4) := by decide
theorem cycle_stores : cycle.forwardStores = (3, 3) ∧ cycle.reverseStores = (3, 2) := by decide
theorem diamond_storage_thirty_six : diamond.storageWork = 36 := by decide
theorem cycle_storage_twenty_six : cycle.storageWork = 26 := by decide
theorem diamond_stored_ninety_seven : diamond.storedDfsWork = 97 := by decide
theorem cycle_stored_seventy_seven : cycle.storedDfsWork = 77 := by decide

theorem cycle_stored_bound : cycle.storedDfsWork ≤ 78 := cycle.storedDfsWork_bound

end PetaProof.DfsStorageExamples
