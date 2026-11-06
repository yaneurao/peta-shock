import PetaProof.ProductiveWork
import PetaProof.PropagationStateExamples
import PetaProof.CertifiedPropagationExamples
import PetaProof.CertifiedPhase

/-! 通知・新規投入・pop・閾値消費による予算の減少と、無効な無進捗操作の検査。 -/
namespace PetaProof.ProductiveWorkExamples

open ThresholdGame CounterQueueExamples PropagationStateExamples

def vertices : List Bool := [false, true]
def edges : List ParentEdge := [.first, .second, .exit]
def c0 : WorkConfiguration Bool ParentEdge := ⟨start, 1⟩
def c1 : WorkConfiguration Bool ParentEdge := ⟨leafReady, 1⟩
def c2 : WorkConfiguration Bool ParentEdge := ⟨childTaken, 1⟩
def c3 : WorkConfiguration Bool ParentEdge := ⟨firstNotified, 1⟩
def c4 : WorkConfiguration Bool ParentEdge := ⟨bothNotified, 1⟩
def c5 : WorkConfiguration Bool ParentEdge := ⟨finished, 1⟩
def c6 : WorkConfiguration Bool ParentEdge := ⟨finished, 0⟩

theorem budgets : c0.potential vertices edges = 8 ∧ c1.potential vertices edges = 6 ∧
    c2.potential vertices edges = 5 ∧ c3.potential vertices edges = 4 ∧
    c4.potential vertices edges = 2 ∧ c5.potential vertices edges = 1 ∧ c6.potential vertices edges = 0 := by decide

theorem six_steps : ProductiveRun parentIndexed edges c0 6 c6 := by
  apply ProductiveRun.step (middle := c1)
  · exact ProductiveStep.notify ParentEdge.exit (by decide) (by decide)
  · apply ProductiveRun.step (middle := c2)
    · exact ProductiveStep.pop (by decide)
    · apply ProductiveRun.step (middle := c3)
      · exact ProductiveStep.notify ParentEdge.first (by decide) (by decide)
      · apply ProductiveRun.step (middle := c4)
        · exact ProductiveStep.notify ParentEdge.second (by decide) (by decide)
        · apply ProductiveRun.step (middle := c5)
          · exact ProductiveStep.pop (by decide)
          · exact ProductiveRun.step ProductiveStep.advance (ProductiveRun.done _)

theorem six_steps_within_bound : (6 : Nat) ≤ edges.length + 2 * vertices.length + 1 := by
  exact six_steps.initial_bound parentIndexed vertices (by decide)
    (by intro vertex; cases vertex <;> decide) edges (by decide) 1

/-- 空popは影の関数として呼べるが、予算は減らないため進捗イベントとしては認めない。 -/
theorem empty_pop_has_no_progress : finished.pop.workBudget vertices edges = finished.workBudget vertices edges := by decide

theorem empty_pop_not_productive : ¬ ProductiveStep parentIndexed edges c6 ⟨finished.pop, 0⟩ := by
  intro step
  have decrease := step.decreases parentIndexed vertices (by decide)
    (by intro vertex; cases vertex <;> decide) edges (by decide)
  have before : c6.potential vertices edges = 0 := by decide
  rw [before] at decrease
  omega

/-- 既に確定した頂点だけの再投入も、新規局所集合の進捗にはならない。 -/
theorem duplicate_add_has_no_progress :
    (finished.add true).workBudget vertices edges = finished.workBudget vertices edges := by decide

/-- 王手循環の一括追加でも、SafeBatchのfresh条件から進捗に必要な新規性を得る。 -/
theorem cyclic_batch_productive : ProductiveStep CertifiedPropagationExamples.loopIndexed [false, true]
    ⟨CertifiedPropagationExamples.loopStart, 0⟩ ⟨CertifiedPropagationExamples.loopAdded, 0⟩ := by
  apply ProductiveStep.batch [false, true] (by decide)
  exact ProductiveStep.fresh_queue_of_batch CertifiedPropagationExamples.loopIndexed _
    (PropagationState.initial_invariant _) _ CertifiedPropagationExamples.cyclicBatch

theorem cyclic_batch_budget :
    CertifiedPropagationExamples.loopStart.workBudget [false, true] [false, true] = 6 ∧
    CertifiedPropagationExamples.loopAdded.workBudget [false, true] [false, true] = 4 := by decide

def badStart : PropagationState Unit Unit := PropagationState.initial badLeafIndexed
def badConfig : WorkConfiguration Unit Unit := ⟨badStart, 0⟩

/-- 悪いleafしかない正値解法は、未確定・未通知を残した状態で正常停止する。 -/
def badHalt : HaltConditions badLeafIndexed badStart where
  queue_empty := rfl
  leaves_done := by
    intro edge score same good
    have equal : (-20 : Int) = score := Move.leaf.inj same
    change (1 : Int) ≤ score at good
    omega
  nodes_done := by intro _ impossible; cases impossible
  core := fun _ => False
  covers_core := by
    intro vertex cycle
    obtain ⟨child, edge, _⟩ := cycle
    cases edge.1
  rounds := 0
  local_empty := by intro _ impossible; exact impossible.1

theorem halted_budget_can_be_positive : Nonempty (HaltConditions badLeafIndexed badStart) ∧
    badConfig.potential [()] [()] = 3 := ⟨⟨badHalt⟩, by decide⟩

end PetaProof.ProductiveWorkExamples
