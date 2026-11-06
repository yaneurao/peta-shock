import PetaProof.DfsStackAccounting
import PetaProof.CheckingSlotExamples

/-! none枠・新規子・既訪問子を分け、再合流と重複根でもイベント数を増やさない。 -/
namespace PetaProof.DfsStackExamples

def diamond := CheckingSlotExamples.diamond
def cycle := CheckingSlotExamples.cycle

def active (todo : List (Option Bool)) : ForwardDfs.State Bool :=
  ⟨fun vertex => !vertex, [⟨false, todo⟩], []⟩

theorem empty_tick : (ForwardFrameAccounting.tickOperations (ForwardDfs.initial : ForwardDfs.State Bool)).total = 0 := by decide
theorem retire_three : (ForwardFrameAccounting.tickOperations (active [])).total = 3 := by decide
theorem none_four : (ForwardFrameAccounting.tickOperations (active [none])).total = 4 := by decide
theorem new_child_five : (ForwardFrameAccounting.tickOperations (active [some true])).total = 5 := by decide
theorem seen_child_four : (ForwardFrameAccounting.tickOperations (active [some false])).total = 4 := by decide

theorem repeated_roots_sixteen : ForwardFrameAccounting.frameWork [()]
    (fun _ => [some (), some (), none]) [(), (), ()] = 16 := by decide
theorem empty_forest : ForwardFrameAccounting.frameWork ([] : List Unit) (fun _ => []) [] = 0 := by decide

theorem diamond_ticks_nine : ForwardFrameAccounting.forestTicks diamond.vertices diamond.checkingOut
    diamond.vertices ForwardDfs.initial = 9 := by decide
theorem diamond_cursor_five : ForwardFrameAccounting.forestTrims diamond.vertices diamond.checkingOut
    diamond.vertices ForwardDfs.initial = 5 := by decide
theorem diamond_frames_thirty_six : diamond.forwardFrameWork = 36 := by decide
theorem diamond_reverse_twelve : diamond.reverseStackWork = 12 := by decide
theorem cycle_frames_twenty_four : cycle.forwardFrameWork = 24 := by decide
theorem cycle_reverse_nine : cycle.reverseStackWork = 9 := by decide
theorem stacks_initialized_six : cycle.stackInitializationWork = 6 := by decide
theorem diamond_combined_one_hundred_sixty_three : diamond.stackDfsWork = 163 := by decide
theorem cycle_combined_one_hundred_twenty_two : cycle.stackDfsWork = 122 := by decide
theorem cycle_stack_bound : cycle.stackDfsWork ≤ 123 := cycle.stackDfsWork_bound

end PetaProof.DfsStackExamples
