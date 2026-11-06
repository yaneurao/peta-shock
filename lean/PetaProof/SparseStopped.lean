import PetaProof.SparseThresholds

/-!
処理した各閾値について、通常伝播と局所削除の停止証拠を与えれば、
勝敗判定の正しさを仮定せずに、既存の完全性定理から疎な走査へ接続できる。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 閾値1回分の抽象停止状態。配列やキューの実装からこれらの条件を取り出す証明は別である。 -/
structure StoppedThreshold (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate) where
  won : V → Prop
  sound : (G.retune level positive bounded).RankedRegion won
  ordinary : (G.retune level positive bounded).OrdinaryClosed won
  core : V → Prop
  covers_core : ∀ v, CyclicVertex (G.retune level positive bounded).OpponentChecking v → core v
  rounds : Nat
  empty : ∀ v, ¬ (G.retune level positive bounded).pruneIter won (fun w => core w ∧ ¬ won w) rounds v

namespace StoppedThreshold

variable {G} {level : Int} {positive : 0 < level} {bounded : level ≤ G.mate}

theorem correct [DecidableEq V] (stopped : G.StoppedThreshold level positive bounded)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    stopped.won root ↔ G.LowerGuarantee root level :=
  ((G.retune level positive bounded).stopped_exact_for_fourfold stopped.sound stopped.ordinary
    vertices covered stopped.core stopped.covers_core stopped.rounds stopped.empty root).trans
    (G.retune_winning_iff level positive bounded root)

end StoppedThreshold

/-- 全処理閾値の停止証拠と、各rootでの報告値を降順走査の完全性へ接続する。 -/
theorem firstWinning_from_stops [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (vertices_cover : ∀ v, v ∈ vertices)
    (levels : List Int) (valid : ∀ level ∈ levels, G.CriticalLevel level)
    (levels_cover : ∀ level, G.CriticalLevel level → level ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a))
    (stops : ∀ level (member : level ∈ levels),
      G.StoppedThreshold level (valid level member).1 (valid level member).2.1)
    (wins : Int → Bool) (root : V)
    (reported : ∀ level (member : level ∈ levels), wins level = true ↔ (stops level member).won root) :
    G.PositiveMaximum root (firstWinning wins levels) := by
  apply G.firstWinning_complete leaves vertices vertices_cover levels valid levels_cover descending wins root
  intro level member
  exact (reported level member).trans ((stops level member).correct vertices vertices_cover root)

end PetaProof.ThresholdGame
