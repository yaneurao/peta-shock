import PetaProof.AbsorbedPolicy

/-!
leaf付きの元の閾値モデルと、吸収状態付きアリーナの全履歴依存勝利集合を接続する。
局所core内の処理が空になったときの完全性にも、この接続を適用する。
四回出現で終わる将棋の利得との同値性は、まだこのファイルの結論に含めない。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 吸収アリーナでの全履歴依存の勝利と、元の履歴不要方策の証拠は同値。 -/
theorem absorbed_history_iff_positional (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) : G.absorbedArena.HistoryWinning (.node root) ↔ G.PositionalWinning root := by
  constructor
  · intro winning
    obtain ⟨won, ⟨policy⟩, inside⟩ :=
      (G.absorbedArena.history_winning_iff_ranked (G.absorbedVertices vertices)
        (G.absorbedVertices_cover vertices covered) (.node root)).mp winning
    exact ⟨(fun v => won (.node v)), ⟨(G.extractRankedRegion policy).positional⟩, inside⟩
  · rintro ⟨won, ⟨region⟩, inside⟩
    let ranked := region.ranked vertices covered
    exact (G.liftRankedRegion ranked).history_winning (G.absorbedVertices vertices)
      (G.absorbedVertices_cover vertices covered) (.node root) inside

/-- 有限グラフには、吸収モデルの全履歴依存勝利集合に一致する元の順位付き保証領域がある。 -/
theorem ranked_threshold_solution_exists (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∃ won, Nonempty (G.RankedRegion won) ∧
      ∀ v, won v ↔ G.absorbedArena.HistoryWinning (.node v) := by
  obtain ⟨states, ⟨policy⟩, exactness, _⟩ := G.absorbedArena.memoryless_determinacy
    (G.absorbedVertices vertices) (G.absorbedVertices_cover vertices covered)
  exact ⟨(fun v => states (.node v)), ⟨G.extractRankedRegion policy⟩,
    fun v => exactness (.node v)⟩

/-- 元の閾値解法の停止条件から、全履歴依存戦略に対する吸収モデル上の完全性を得る。 -/
theorem stopped_exact_for_absorbed_history {won : V → Prop} (sound : G.RankedRegion won)
    (ordinary : G.OrdinaryClosed won) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v) :
    ∀ v, won v ↔ G.absorbedArena.HistoryWinning (.node v) := by
  intro v
  exact (G.stopped_exact_for_positional sound ordinary vertices covered core covers_core n empty v).trans
    (G.absorbed_history_iff_positional vertices covered v).symm

end PetaProof.ThresholdGame
