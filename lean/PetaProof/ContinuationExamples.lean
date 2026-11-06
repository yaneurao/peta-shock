import PetaProof.QueueScanWitness
import PetaProof.OutputPreference
import PetaProof.IncrementalSemantics
import PetaProof.QueueThresholdScanExamples

/-! 全phase記録、正負のdepth、同点補正、更新領域外の保証の小規模回帰。 -/
namespace PetaProof.ContinuationExamples

open ThresholdGame

namespace Scan
open QueueThresholdScanExamples

def rows := phaseStates _ top top.generatedLevels top.generatedLevels_valid top.seeded

theorem levels_recorded : rows.map Prod.fst = [40, 30, 20] := by decide

theorem witnesses_from_generated_run (row : Int × PropagationState Unit Bool) (member : row ∈ rows) :
    ∃ positive : 0 < row.1, ∃ bounded : row.1 ≤ 40,
      Nonempty (((game.retune 40 (by decide) (by decide)).retune row.1 positive bounded).ResolvedRegions
        (fun vertex => row.1 ≤ top.generatedValue (fun _ => false) vertex) 3) := by
  exact generated_phase_regions top rfl (fun _ => false) bounded_leaves no_own_cycles no_other_cycles row member

end Scan

namespace Preference
open OutputPreference

def depth (edge : Bool) : Nat := if edge then 2 else 0

theorem positive_short : Preferred (fun _ : Bool => 85) depth (fun _ => True) 85 false := by
  refine ⟨trivial, rfl, ?_⟩
  intro other _ _
  cases other <;> decide
theorem negative_long : Preferred (fun _ : Bool => -85) depth (fun _ => True) (-85) true := by
  refine ⟨trivial, rfl, ?_⟩
  intro other _ _
  cases other <;> decide
theorem zero_short : Preferred (fun _ : Bool => 0) depth (fun _ => True) 0 false := by
  refine ⟨trivial, rfl, ?_⟩
  intro other _ _
  cases other <;> decide

theorem unsafe_short_rejected :
    ¬ Preferred (fun _ : Bool => 85) depth (fun edge => edge = true) 85 false := by
  intro preferred
  exact Bool.noConfusion preferred.1

theorem negative_saved : encoded (fun _ : Bool => -85) (fun edge => edge = true) (-85) false = -86 ∧
    encoded (fun _ : Bool => -85) (fun edge => edge = true) (-85) true = -85 := by
  classical
  simp [encoded]

theorem lower_score_unchanged : encoded (fun _ : Bool => 84) (fun _ => False) 85 false = 84 := by
  classical
  simp [encoded]

end Preference

namespace Update
open IncrementalBoundary

def game (changed : Bool) : ThresholdGame Bool where
  legal := fun vertex move => move = .leaf (if changed && vertex then 40 else 20)
  owner := id
  check := fun _ _ => False
  player := false
  threshold := 30
  mate := 40
  positive := by decide
  bounded := by decide
  alternating := by intro _ _ edge; contradiction
  nonempty_moves := fun _ => ⟨_, rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def agreement : Agreement (game false) (game true) (fun vertex => vertex = false) where
  legal := by intro vertex inside move; subst vertex; rfl
  owner := fun _ _ => rfl
  check := fun _ _ _ => Iff.rfl
  player := rfl
  threshold := rfl
  closed := by intro _ _ _ impossible; contradiction

theorem unchanged_root : (game false).FourfoldWinning false ↔ (game true).FourfoldWinning false :=
  agreement.fourfold_iff [false, true] (by intro vertex; cases vertex <;> simp) false rfl

def oldEdge (source child : Nat) : Prop := source = 0 ∧ child = 1
def newEdge (_ _ : Nat) : Prop := False

theorem removed_edge_still_affected : affectedBy oldEdge newEdge (fun v => v = 1) 0 :=
  ⟨1, rfl, ⟨.cons (Or.inl ⟨rfl, rfl⟩) (.nil 1)⟩⟩

theorem no_path_after_exit (exit : Nat) (outside : ¬ affectedBy oldEdge newEdge (fun v => v = 1) exit)
    (back : Walk (fun v w => oldEdge v w ∨ newEdge v w) exit 0) : False :=
  no_return (reachabilityRegion oldEdge newEdge (fun v => v = 1)) 0 exit removed_edge_still_affected outside back

end Update
end PetaProof.ContinuationExamples
