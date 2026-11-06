import PetaProof.SparseStopped

/-!
C++の for (level=Mate; level>0; --level) と、空のleafバケットを飛ばす条件を表す。
バケットに正しいleaf存在情報が入り、各処理閾値を正しく解けば、走査の値は完全である。
-/
namespace PetaProof

/-- cap,cap-1,...,1の降順列。 -/
def descendingLevels : Nat → List Int
  | 0 => []
  | cap + 1 => ((cap + 1 : Nat) : Int) :: descendingLevels cap

theorem mem_descendingLevels (cap : Nat) (level : Int) :
    level ∈ descendingLevels cap ↔ 0 < level ∧ level ≤ (cap : Int) := by
  induction cap with
  | zero =>
    constructor
    · intro impossible
      cases impossible
    · intro bound
      exact False.elim (by omega)
  | succ cap ih =>
    simp only [descendingLevels, List.mem_cons, ih]
    omega

theorem descendingLevels_ordered (cap : Nat) : (descendingLevels cap).Pairwise (fun a b => b < a) := by
  induction cap with
  | zero => exact List.Pairwise.nil
  | succ cap ih =>
    rw [descendingLevels, List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro level member
    have bound := (mem_descendingLevels cap level).mp member
    omega

/-- Mateまたはleafバケットが空でない閾値だけを残す。Mateにleafがあっても二重には処理しない。 -/
def processedLevels (mate : Nat) (hasLeaf : Int → Bool) : List Int :=
  (descendingLevels mate).filter (fun level => level == (mate : Int) || hasLeaf level)

theorem mem_processedLevels (mate : Nat) (hasLeaf : Int → Bool) (level : Int) :
    level ∈ processedLevels mate hasLeaf ↔
      0 < level ∧ level ≤ (mate : Int) ∧ (level = (mate : Int) ∨ hasLeaf level = true) := by
  simp only [processedLevels, List.mem_filter, mem_descendingLevels, Bool.or_eq_true,
    beq_iff_eq, and_assoc]

theorem processedLevels_ordered (mate : Nat) (hasLeaf : Int → Bool) :
    (processedLevels mate hasLeaf).Pairwise (fun a b => b < a) :=
  (descendingLevels_ordered mate).filter _

namespace ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- leafバケットの存在判定が正しければ、C++型の走査列は処理すべき閾値と厳密に一致する。 -/
theorem processedLevels_critical_iff (hasLeaf : Int → Bool)
    (buckets : ∀ level, 0 < level → level ≤ G.mate →
      (hasLeaf level = true ↔ ∃ v, G.legal v (.leaf level))) (level : Int) :
    level ∈ processedLevels G.mate.toNat hasLeaf ↔ G.CriticalLevel level := by
  have cast_mate : (G.mate.toNat : Int) = G.mate := Int.toNat_of_nonneg (Int.le_of_lt G.mate_positive)
  rw [mem_processedLevels, cast_mate]
  constructor
  · rintro ⟨positive, bounded, top | leaf⟩
    · exact ⟨positive, bounded, Or.inl top⟩
    · exact ⟨positive, bounded, Or.inr ((buckets level positive bounded).mp leaf)⟩
  · rintro ⟨positive, bounded, top | leaf⟩
    · exact ⟨positive, bounded, Or.inl top⟩
    · exact ⟨positive, bounded, Or.inr ((buckets level positive bounded).mpr leaf)⟩

/-- 空バケットを省略する降順走査の完全性。未処理の整数閾値でのみ勝てる局面は残らない。 -/
theorem processed_scan_complete [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (vertices_cover : ∀ v, v ∈ vertices)
    (hasLeaf : Int → Bool)
    (buckets : ∀ level, 0 < level → level ≤ G.mate →
      (hasLeaf level = true ↔ ∃ v, G.legal v (.leaf level)))
    (wins : Int → Bool) (root : V)
    (correct : ∀ level ∈ processedLevels G.mate.toNat hasLeaf,
      wins level = true ↔ G.LowerGuarantee root level) :
    G.PositiveMaximum root (firstWinning wins (processedLevels G.mate.toNat hasLeaf)) :=
  G.firstWinning_complete leaves vertices vertices_cover _
    (fun level member => (G.processedLevels_critical_iff hasLeaf buckets level).mp member)
    (fun level critical => (G.processedLevels_critical_iff hasLeaf buckets level).mpr critical)
    (processedLevels_ordered _ _) wins root correct

end ThresholdGame
end PetaProof
