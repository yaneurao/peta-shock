import PetaProof.FirstAdmissionValues
import PetaProof.IncrementalThreshold

/-!
各閾値の停止証拠と、0初期化・初回確定時だけ書く値配列を接続する。
各閾値の状態を実際の一つのC++実行から再構成する対応は別の課題である。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} (G : ThresholdGame V) [DecidableEq V]

/-- 記録済み値が確定フラグを表すとき、実際の局所投入列への書込みは終了集合での記録と同じ。 -/
theorem record_added_vertices (state : PropagationState V E) (values : V → Int) (level : Int)
    (vertices : List V) (represented : ∀ vertex, state.won vertex ↔ values vertex ≠ 0) :
    writeAdmissions values level vertices =
      latchValues values level (fun vertex => ((state.addMany vertices).counters vertex).admitted) := by
  apply writeAdmissions_eq_latch
  intro vertex
  exact (PropagationState.won_addMany_iff state vertices vertex).trans (or_congr (represented vertex) Iff.rfl)

/-- hitによる親1要素へのガード付き書込みも、通知後の確定集合での記録と一致する。 -/
theorem record_notified_parent [DecidableEq E] {H : ThresholdGame V} (indexed : H.IndexedMoves E)
    (state : PropagationState V E) (values : V → Int) (level : Int) (edge : E)
    (represented : ∀ vertex, state.won vertex ↔ values vertex ≠ 0) :
    (if ((state.notify indexed edge).counters (indexed.source edge)).admitted then
      writeAdmission values level (indexed.source edge) else values) =
      latchValues values level (fun vertex => ((state.notify indexed edge).counters vertex).admitted) := by
  let next := state.notify indexed edge
  let vertices := if (next.counters (indexed.source edge)).admitted then [indexed.source edge] else []
  have as_list : (if (next.counters (indexed.source edge)).admitted then
      writeAdmission values level (indexed.source edge) else values) = writeAdmissions values level vertices := by
    cases flag : (next.counters (indexed.source edge)).admitted <;> simp [vertices, flag, writeAdmissions]
  rw [as_list]
  apply writeAdmissions_eq_latch
  intro vertex
  change next.won vertex ↔ _
  rw [PropagationState.won_notify_iff, represented]
  change (values vertex ≠ 0 ∨ (vertex = indexed.source edge ∧
    (next.counters (indexed.source edge)).admitted = true)) ↔ _
  cases flag : (next.counters (indexed.source edge)).admitted <;>
    simp [vertices, flag]

/-- 停止集合に従う初回書込み配列は、最大の正の保証閾値を各局面に記録する。 -/
theorem recorded_from_stops (leaves : G.BoundedLeaves) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (levels : List Int) (valid : ∀ level ∈ levels, G.CriticalLevel level)
    (levels_cover : ∀ level, G.CriticalLevel level → level ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a))
    (states : Int → PropagationState V E)
    (stops : ∀ level (member : level ∈ levels),
      G.StoppedThreshold level (valid level member).1 (valid level member).2.1)
    (represented : ∀ level (member : level ∈ levels) vertex,
      (stops level member).won vertex ↔ (states level).won vertex)
    (root : V) :
    G.PositiveMaximum root
      (scanValues levels (fun level vertex => ((states level).counters vertex).admitted) (fun _ => 0) root) := by
  rw [scanValues_initial levels _ (fun level member => (valid level member).1)]
  apply G.firstWinning_from_stops leaves vertices covered levels valid levels_cover descending stops
  intro level member
  exact (represented level member root).symm

/-- 実際の空バケット省略列にも、同じ初回確定値の配列の定理を適用できる。 -/
theorem recorded_processed_levels (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (hasLeaf : Int → Bool)
    (buckets : ∀ level, 0 < level → level ≤ G.mate →
      (hasLeaf level = true ↔ ∃ vertex, G.legal vertex (.leaf level)))
    (states : Int → PropagationState V E)
    (stops : ∀ level (member : level ∈ processedLevels G.mate.toNat hasLeaf),
      G.StoppedThreshold level ((G.processedLevels_critical_iff hasLeaf buckets level).mp member).1
        ((G.processedLevels_critical_iff hasLeaf buckets level).mp member).2.1)
    (represented : ∀ level (member : level ∈ processedLevels G.mate.toNat hasLeaf) vertex,
      (stops level member).won vertex ↔ (states level).won vertex)
    (root : V) :
    G.PositiveMaximum root (scanValues (processedLevels G.mate.toNat hasLeaf)
      (fun level vertex => ((states level).counters vertex).admitted) (fun _ => 0) root) := by
  apply G.recorded_from_stops leaves vertices covered _
    (fun level member => (G.processedLevels_critical_iff hasLeaf buckets level).mp member)
    (fun level critical => (G.processedLevels_critical_iff hasLeaf buckets level).mpr critical)
    (processedLevels_ordered _ _) states stops represented root

end PetaProof.ThresholdGame
