import PetaProof.LocalSafetyIndex
import PetaProof.SafetyClassificationExamples

namespace PetaProof.LocalIndex.Examples

def core : List Nat := [10, 20, 30]
def flags : Nat → Bool := fun _ => true
def won : Nat → Bool := fun vertex => vertex == 20

theorem registered_values : registered core 10 = 0 ∧ registered core 20 = 1 ∧ registered core 30 = 2 ∧
    registered core 99 = -1 := by decide

theorem signed32_values : (registered32 core 10).toInt = 0 ∧ (registered32 core 20).toInt = 1 ∧
    (registered32 core 30).toInt = 2 ∧ (registered32 core 99).toInt = -1 := by decide

theorem middle_inverse : core[(registered32 core 20).toUInt32.toNat]? = some 20 :=
  (localIndex32_access core (by decide) (by decide) 20 (by decide)).2

theorem update_middle : (core.map flags).set (registered32 core 20).toUInt32.toNat false =
    core.map (writeFlag flags 20 false) := packed32_flag_update core (by decide) (by decide) flags 20 false (by decide)

theorem updated_flags : (core.map flags).set (registered32 core 20).toUInt32.toNat false = [true, false, true] := by decide

theorem won_still_has_index : registered core 20 = 1 ∧ localFlag32 core (fun vertex => !won vertex) 20 = false := by decide
theorem outside_is_rejected : localFlag32 core flags 99 = false := by decide

theorem cleanup_all : (clear32 core (registered32 core) 10).toInt = -1 ∧
    (clear32 core (registered32 core) 20).toInt = -1 ∧ (clear32 core (registered32 core) 30).toInt = -1 := by decide

theorem overlapping_reuse : (install32 [30, 10] 0 (clear32 core (registered32 core)) 30).toInt = 0 ∧
    (install32 [30, 10] 0 (clear32 core (registered32 core)) 10).toInt = 1 ∧
    (install32 [30, 10] 0 (clear32 core (registered32 core)) 20).toInt = -1 := by decide

-- core外の値を勝手に初期化する処理ではない。入口とcleanupの契約が必要である。
theorem stale_outside_survives_install : install core 0 (fun vertex => if vertex = 99 then 0 else -1) 99 = 0 := by decide

-- 重複coreでは最初と最後の出現位置が食い違う。Nodup条件が必要である。
theorem duplicate_core_loses_first_index : registered [10, 20, 10] 10 = 2 ∧
    ([10, 20, 10] : List Nat).idxOf 10 = 0 := by decide

theorem int32_boundary : (Int32.ofInt 2147483647).toInt = 2147483647 ∧
    (Int32.ofInt 2147483648).toInt = -2147483648 := by decide

open SafetyClassification.Examples (loopInput outsideInput vertices vertices_unique vertices_cover outsideGraph outsideStart outsideFinish)

theorem initial_guard_matches_classifier (vertex : Bool) :
    localFlag32 [false, true] (fun vertex => !loopInput.won vertex) vertex = true ↔
      SafetyClassification.eligible loopInput vertex = true :=
  eligible_local_guard loopInput [false, true] (by decide) (by decide)
    (by intro vertex; cases vertex <;> simp [loopInput]) vertex

theorem dynamic_guard_matches_after_delete (vertex : Bool) :
    localFlag32 [true] (fun vertex => !outsideFinish.deleted vertex) vertex = true ↔
      SafetyExecution.alive outsideFinish vertex :=
  dynamic_local_guard outsideInput vertices vertices_unique vertices_cover [true] (by decide) (by decide)
    (by intro v; cases v <;> simp [outsideInput, loopInput])
    (SafetyExecution.Run.next (SafetyExecution.Run.done outsideFinish)) vertex

end PetaProof.LocalIndex.Examples
