import PetaProof.CheckingDfsAccounting
import PetaProof.ComputedCheckingCoreExamples

/-! 成分をまたぐ再合流、自己辺、平行な逆辺項目、重複根の会計を検査する。 -/
namespace PetaProof.CheckingDfsAccountingExamples

def diamond := ComputedCheckingCoreExamples.diamond.prepared.1
def cycle := ComputedCheckingCoreExamples.cycle.prepared.1

theorem diamond_reverse_six : diamond.checkingReverseWork = 6 := by decide
theorem diamond_dfs_twenty_three : diamond.checkingDfsWork = 23 := by decide
theorem diamond_dfs_bound : diamond.checkingDfsWork ≤ 26 := diamond.checkingDfsWork_bound
theorem cycle_reverse_six : cycle.checkingReverseWork = 6 := by decide
theorem cycle_dfs_eighteen : cycle.checkingDfsWork = 18 := by decide

/-- 非王手辺を除く前のdiamondも、再合流先を二度popせず4+4となる。 -/
theorem unfiltered_diamond_eight : ReverseDfsWork.passWork
    QueueScanAccountingExamples.context.vertices
    (fun target => (QueueScanAccountingExamples.parents.incoming target).map QueueScanAccountingExamples.indexed.source)
    QueueScanAccountingExamples.context.vertices ComponentNumbering.initial = 8 := by decide

def duplicateParents (_ : Unit) : List Unit := [(), ()]

theorem self_and_parallel_items :
    ReverseDfsWork.passWork [()] duplicateParents [()] ComponentNumbering.initial = 3 := by decide

theorem duplicate_root_is_free :
    ReverseDfsWork.passWork [()] duplicateParents [(), (), ()] ComponentNumbering.initial = 3 := by decide

theorem empty_second_pass : ReverseDfsWork.passWork ([] : List Unit) duplicateParents []
    ComponentNumbering.initial = 0 := by decide

end PetaProof.CheckingDfsAccountingExamples
