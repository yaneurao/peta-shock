import PetaProof.CheckingRowAccounting
import PetaProof.CheckingDfsAccountingExamples

/-! 不許可辺も選別費用に含み、自己辺anyの短絡と同じcoreを得る例。 -/
namespace PetaProof.CheckingRowAccountingExamples

def diamond := CheckingDfsAccountingExamples.diamond
def cycle := CheckingDfsAccountingExamples.cycle

theorem select_one : CountedRowOps.select (fun n : Nat => decide (n = 2)) (fun n => 10 * n) [1, 2, 3] =
    ([20], 6) := by decide
theorem reject_all : CountedRowOps.select (fun _ : Nat => false) id [1, 2, 3] = ([], 3) := by decide
theorem accept_all : CountedRowOps.select (fun _ : Nat => true) id [1, 2, 3] = ([1, 2, 3], 12) := by decide
theorem any_stops_on_second : CountedRowOps.any id [false, true, true] = (true, 2) := by decide
theorem any_checks_all : CountedRowOps.any id [false, false, false] = (false, 3) := by decide
theorem any_empty : CountedRowOps.any id [] = (false, 0) := by decide

theorem duplicate_root_charge_once : ReverseVisitCharge.passCharge [()]
    (fun _ => 7) (fun _ => [(), ()]) [(), (), ()] ComponentNumbering.initial = 7 := by decide
theorem zero_charge : ReverseVisitCharge.passCharge [()]
    (fun _ => 0) (fun _ => [(), ()]) [(), (), ()] ComponentNumbering.initial = 0 := by decide

theorem diamond_selection_ten : diamond.selectionWork = 10 := by decide
theorem diamond_self_four : diamond.chargedAggregation.2 = 4 := by decide
theorem diamond_row_work_sixty_one : diamond.rowDfsWork = 61 := by decide
theorem diamond_row_bound : diamond.rowDfsWork ≤ 75 := diamond.rowDfsWork_bound
theorem cycle_selection_twelve : cycle.selectionWork = 12 := by decide
theorem cycle_self_three : cycle.chargedAggregation.2 = 3 := by decide
theorem cycle_row_work_fifty_one : cycle.rowDfsWork = 51 := by decide
theorem charged_core_only : cycle.chargedCore .root = false ∧ cycle.chargedCore .other = true ∧
    cycle.chargedCore .own = true := by decide
theorem opposite_selection_six : (cycle.opposite (fun _ => false)).selectionWork = 6 := by decide

end PetaProof.CheckingRowAccountingExamples
