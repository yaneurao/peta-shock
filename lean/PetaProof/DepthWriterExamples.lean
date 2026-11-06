import PetaProof.DepthWriter

/-! 保存規則の回帰例。SCCの受理は別条件であり、この数値例から安全性を推定しない。 -/
namespace PetaProof.DepthWriterExamples

def input : DepthWriter.Input Unit (Fin 3) where
  rows := fun _ => [0, 1, 2]
  raw := fun _ _ => 100
  best := fun _ => 100
  depth := fun edge => if edge = 2 then 9999 else 1
  selected := fun _ => 0
  keepTies := fun _ => true
  selected_member := by intro _; simp
  selected_exact := by intro _; rfl
  upper := by intro _ _ _; exact Int.le_refl _

theorem selected_saved : input.saved () 0 = 100 := by
  rw [input.saved_formula]
  decide

theorem equal_depth_saved : input.saved () 1 = 100 := by
  rw [input.saved_formula]
  decide

theorem other_depth_lowered : input.saved () 2 = 99 := by
  rw [input.saved_formula]
  decide

def single : DepthWriter.Input Unit (Fin 3) :=
  { input with keepTies := fun _ => false }

theorem rejected_equal_depth_saved : single.saved () 1 = 99 := by
  rw [single.saved_formula]
  decide

/-- 上限丸めで同depthになる候補は、SCC検査側で安全性を確かめる必要がある。 -/
def capped : DepthWriter.Input Unit (Fin 3) :=
  { input with depth := fun edge => min (input.depth edge) 1 }

theorem capped_tie_saved : capped.saved () 2 = 100 := by
  rw [capped.saved_formula]
  decide

/-- 差し戻された選択手は、最小depthでなくても保存最大手として残せる。 -/
def restored : DepthWriter.Input Unit (Fin 3) :=
  { single with depth := fun edge => if edge = 0 then 9999 else 1 }

theorem restored_not_shortest : restored.depth 1 < restored.depth 0 := by decide

theorem restored_selected_saved : restored.saved () 0 = 100 := by
  rw [restored.saved_formula]
  decide

theorem restored_shorter_lowered : restored.saved () 1 = 99 := by
  rw [restored.saved_formula]
  decide

theorem shrink_keeps_equal_tie : (1 : Fin 3) ∈ input.outputRows true () := by
  rw [input.output_member]
  decide

end PetaProof.DepthWriterExamples
