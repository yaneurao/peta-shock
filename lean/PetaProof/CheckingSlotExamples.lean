import PetaProof.CheckingSlotGeneration
import PetaProof.DfsStorageExamples

/-! 生成はseenの成功ガード内だけ。leaf・不許可辺もnoneの枠と費用を保つ。 -/
namespace PetaProof.CheckingSlotExamples

def diamond := DfsStorageExamples.diamond
def cycle := DfsStorageExamples.cycle

theorem duplicate_roots_charge_once : ForwardDiscoveryCharge.forestCharge [()]
    (fun _ => 7) (fun _ => [some (), some (), none]) [(), (), ()] ForwardDfs.initial = 7 := by decide

theorem zero_charge : ForwardDiscoveryCharge.forestCharge [()]
    (fun _ => 0) (fun _ => [some (), none]) [(), ()] ForwardDfs.initial = 0 := by decide

theorem empty_roots : ForwardDiscoveryCharge.forestCharge ([] : List Unit)
    (fun _ => 7) (fun _ => []) [] ForwardDfs.initial = 0 := by decide

theorem root_two_slots : diamond.slotProbe .root = ([some .left, some .right], 4) := by decide
theorem forbidden_keeps_slot : diamond.slotProbe .left = ([none], 2) := by decide
theorem leaf_keeps_slot : diamond.slotProbe .child = ([none], 2) := by decide

def discovered := ForwardDfs.discover diamond.checkingOut ForwardDfs.initial .root

theorem seen_does_not_regenerate : diamond.discoverProbe discovered .root = (discovered, 0) := by rfl
theorem diamond_slots_ten : diamond.slotGenerationWork = 10 := by decide
theorem cycle_slots_six : cycle.slotGenerationWork = 6 := by decide
theorem opposite_slots_six : (cycle.opposite (fun _ => false)).slotGenerationWork = 6 := by decide
theorem diamond_generated_one_hundred_seven : diamond.generatedDfsWork = 107 := by decide
theorem cycle_generated_eighty_three : cycle.generatedDfsWork = 83 := by decide
theorem cycle_generated_bound : cycle.generatedDfsWork ≤ 84 := cycle.generatedDfsWork_bound

end PetaProof.CheckingSlotExamples
