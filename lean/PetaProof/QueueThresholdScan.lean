import PetaProof.QueueThresholdAdvance

/-!
leaf帯更新・固定閾値の二つのキュー・初回記録を一つの降順実行へまとめる。
停止証拠や各閾値の正解は入力せず、同じ通常状態を引き継ぐ。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanQueues : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) →
      PropagationState V E → (V → Int) → PropagationState V E × (V → Int)
  | _, _, [], _, state, values => (state, values)
  | G, ctx, t :: rest, valid, state, values =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let next := ctx.phase t positive bounded state
    scanQueues (G.retune t positive bounded) (ctx.atLevel t positive bounded)
      rest (fun s member => valid s (by simp [member])) next
      (latchValues values t (fun vertex => (next.counters vertex).admitted))

/-- 証明用の正解述語だけを元の閾値ゲームへ戻す。計算はこの述語を参照しない。 -/
theorem guaranteeFlags_retune (G : ThresholdGame V) (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) :
    (G.retune t positive bounded).guaranteeFlags = G.guaranteeFlags := by
  classical
  funext level vertex
  unfold guaranteeFlags
  exact congrArg (fun p : Prop => decide p) (propext (G.lower_retune_iff t positive bounded vertex level))

/-- 同じ通常状態を引き継ぐ全実行の初回記録は、各閾値の正しい勝敗による記録と一致する。 -/
theorem scanQueues_values (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a))
    (below : ∀ t ∈ levels, t ≤ G.threshold)
    (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) (values : V → Int) :
    (scanQueues G ctx levels valid state values).2 = scanValues levels G.guaranteeFlags values := by
  induction levels generalizing G state values with
  | nil => rfl
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let H := G.retune t positive bounded
    let low := ctx.atLevel t positive bounded
    let next := ctx.phase t positive bounded state
    have lower : t ≤ G.threshold := below t (by simp)
    obtain ⟨next_certificate⟩ := ctx.phase_certified state certificate t positive lower
    have next_boundary := ctx.phase_boundary state boundary t positive lower
    have flags : (fun vertex => (next.counters vertex).admitted) = G.guaranteeFlags t := by
      funext vertex
      apply Bool.eq_iff_iff.mpr
      simpa only [guaranteeFlags, decide_eq_true_eq, PropagationState.won] using
        ctx.phase_exact state certificate boundary covers_core t positive lower vertex
    have tail_valid : ∀ s ∈ rest, 0 < s ∧ s ≤ H.mate := fun s member => valid s (by simp [member])
    have tail_below : ∀ s ∈ rest, s ≤ H.threshold := fun s member =>
      Int.le_of_lt (List.rel_of_pairwise_cons descending member)
    have continuation := ih H low tail_valid descending.of_cons tail_below covers_core next next_certificate next_boundary
      (latchValues values t (fun vertex => (next.counters vertex).admitted))
    change (scanQueues H low rest tail_valid next
      (latchValues values t (fun vertex => (next.counters vertex).admitted))).2 = _
    rw [continuation, guaranteeFlags_retune G t positive bounded, flags]
    rfl

namespace QueueContext

variable {G : ThresholdGame V} (ctx : G.QueueContext E)

/-- 反対視点でも同じ内部辺と逆辺を使い、leaf利得だけを符号反転する。 -/
def opposite (otherCore : V → Bool) : G.opposite.QueueContext E where
  vertices := ctx.vertices
  unique := ctx.unique
  covered := ctx.covered
  indexed := {
    outgoing := ctx.indexed.outgoing
    source := ctx.indexed.source
    move := fun edge => (ctx.indexed.move edge).negate
    unique := ctx.indexed.unique
    at_source := ctx.indexed.at_source
    source_of_mem := ctx.indexed.source_of_mem
    legal := by
      intro vertex edge member
      change G.legal vertex (ctx.indexed.move edge).negate.negate
      simpa only [Move.negate_negate] using ctx.indexed.legal vertex edge member
    covers := by
      intro vertex move legal
      obtain ⟨edge, member, same⟩ := ctx.indexed.covers vertex move.negate legal
      exact ⟨edge, member, by rw [same, Move.negate_negate]⟩
  }
  parents := {
    incoming := ctx.parents.incoming
    unique := ctx.parents.unique
    exact := by
      intro child edge
      change edge ∈ ctx.parents.incoming child ↔ (ctx.indexed.move edge).negate = .node child
      rw [ctx.parents.exact]
      cases ctx.indexed.move edge <;> simp [Move.negate]
  }
  core := otherCore
  checked := ctx.checked
  check_correct := ctx.check_correct

/-- 上限で初期化を一度だけ行い、後はカウンターと初回記録を引き継ぐ。 -/
def positiveQueueValues (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : V → Int :=
  let top := ctx.atLevel G.mate G.mate_positive (Int.le_refl _)
  (scanQueues (G.retune G.mate G.mate_positive (Int.le_refl _)) top levels valid top.seeded (fun _ => 0)).2

theorem positiveQueueValues_correct (leaves : G.BoundedLeaves)
    (levels : List Int) (valid : ∀ t ∈ levels, G.CriticalLevel t)
    (levels_cover : ∀ t, G.CriticalLevel t → t ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a))
    (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) (root : V) :
    G.PositiveMaximum root (ctx.positiveQueueValues levels
      (fun t member => ⟨(valid t member).1, (valid t member).2.1⟩) root) := by
  let top := ctx.atLevel G.mate G.mate_positive (Int.le_refl _)
  have run := scanQueues_values (G.retune G.mate G.mate_positive (Int.le_refl _)) top levels
    (fun t member => ⟨(valid t member).1, (valid t member).2.1⟩) descending
    (fun t member => (valid t member).2.1) covers_core top.seeded top.seeded_certificate top.seeded_boundary (fun _ => 0)
  unfold positiveQueueValues
  rw [run, guaranteeFlags_retune, scanValues_initial levels _ (fun t member => (valid t member).1)]
  apply G.firstWinning_complete leaves ctx.vertices ctx.covered levels valid levels_cover descending
  intro t _
  simp [guaranteeFlags]

/-- ゲームから生成した疎な閾値列を使う。停止証拠の列を入力する必要はない。 -/
noncomputable def computedPositiveQueueValues : V → Int :=
  ctx.positiveQueueValues G.setLevels (fun t member =>
    ⟨((G.setLevels_critical_iff t).mp member).1, ((G.setLevels_critical_iff t).mp member).2.1⟩)

theorem computedPositiveQueueValues_correct (leaves : G.BoundedLeaves)
    (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) (root : V) :
    G.PositiveMaximum root (ctx.computedPositiveQueueValues root) :=
  ctx.positiveQueueValues_correct leaves G.setLevels (fun t member => (G.setLevels_critical_iff t).mp member)
    (fun t critical => (G.setLevels_critical_iff t).mpr critical) (processedLevels_ordered _ _) covers_core root

/-- 二つの視点の同じキュー算法から、元の固定プレイヤー視点の整数値を作る。 -/
noncomputable def queueGameValue (other : G.opposite.QueueContext E) : V → Int :=
  fun vertex => ctx.computedPositiveQueueValues vertex - other.computedPositiveQueueValues vertex

theorem queueGameValue_exact (other : G.opposite.QueueContext E) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → other.core vertex = true) (root : V) :
    G.ExactValue root (ctx.queueGameValue other root) :=
  G.merge_positive_maxima leaves ctx.vertices ctx.covered root
    (ctx.computedPositiveQueueValues_correct leaves own_covers root)
    (other.computedPositiveQueueValues_correct (G.opposite_bounded_leaves leaves) other_covers root)

noncomputable def computedQueueValue (otherCore : V → Bool) : V → Int := ctx.queueGameValue (ctx.opposite otherCore)

/-- グラフ入力と両側の循環候補だけから、全キュー実行の整数値の正当性を導く。 -/
theorem computedQueueValue_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) (root : V) :
    G.ExactValue root (ctx.computedQueueValue otherCore root) :=
  ctx.queueGameValue_exact (ctx.opposite otherCore) leaves own_covers other_covers root

end QueueContext
end PetaProof.ThresholdGame
