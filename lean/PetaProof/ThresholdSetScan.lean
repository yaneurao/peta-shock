import PetaProof.ThresholdSetSolver
import PetaProof.FirstAdmissionValues

/-!
固定閾値の集合制御を降順に実行する。確定集合と初回記録値を引き継ぎ、
停止証拠や各閾値の正解を入力せずに、最大正値へ接続する数学的仕様。
同期集合反復の定義から高速キュー版の実行時間は主張しない。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 返却値は確定集合と記録値。各段階は直前の集合から続ける。 -/
noncomputable def scanSets (vertices : List V) (core : V → Prop) :
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) →
      (V → Prop) → (V → Int) → (V → Prop) × (V → Int)
  | [], _, won, values => (won, values)
  | t :: rest, valid, won, values => by
    classical
    let next := (G.retune t (valid t (by simp)).1 (valid t (by simp)).2).settle
      vertices core vertices.length won
    exact scanSets vertices core rest (fun s member => valid s (by simp [member])) next
      (latchValues values t (fun v => decide (next v)))

/-- 各段階で同じ確定集合を拡張する。順序や値の健全性に依存しない。 -/
theorem scanSets_extends (vertices : List V) (core : V → Prop)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (won : V → Prop) (values : V → Int) :
    ∀ v, won v → (G.scanSets vertices core levels valid won values).1 v := by
  induction levels generalizing won values with
  | nil => exact fun _ h => h
  | cons t rest ih =>
    intro v inside
    apply ih (fun s member => valid s (by simp [member]))
    exact (G.retune t (valid t (by simp)).1 (valid t (by simp)).2).settle_extends
      vertices core vertices.length won v inside

/-- 記録済みの値は、低い閾値で集合が広がっても上書きしない。 -/
theorem scanSets_keeps_nonzero (vertices : List V) (core : V → Prop)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (won : V → Prop) (values : V → Int) (v : V) (recorded : values v ≠ 0) :
    (G.scanSets vertices core levels valid won values).2 v = values v := by
  classical
  induction levels generalizing won values with
  | nil => rfl
  | cons t rest ih =>
    let next := (G.retune t (valid t (by simp)).1 (valid t (by simp)).2).settle
      vertices core vertices.length won
    have same := latch_keeps_nonzero values t (fun v => decide (next v)) v recorded
    change (G.scanSets vertices core rest (fun s member => valid s (by simp [member])) next
      (latchValues values t (fun v => decide (next v)))).2 v = _
    rw [ih _ next _ (by simpa only [same] using recorded), same]

/-- 確定集合と記録値の非零要素が一致する不変条件を、全閾値で保存する。 -/
theorem scanSets_represents (vertices : List V) (core : V → Prop)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (won : V → Prop) (values : V → Int) (represented : ∀ v, won v ↔ values v ≠ 0) :
    ∀ v, (G.scanSets vertices core levels valid won values).1 v ↔
      (G.scanSets vertices core levels valid won values).2 v ≠ 0 := by
  classical
  induction levels generalizing won values with
  | nil => exact represented
  | cons t rest ih =>
    let H := G.retune t (valid t (by simp)).1 (valid t (by simp)).2
    let next := H.settle vertices core vertices.length won
    apply ih
    intro v
    have retained : ∀ w, values w ≠ 0 → decide (next w) = true := by
      intro w nonzero
      exact decide_eq_true (H.settle_extends vertices core vertices.length won w ((represented w).mpr nonzero))
    have nonzero : t ≠ 0 := by have positive := (valid t (by simp)).1; omega
    simpa only [decide_eq_true_eq] using
      (latch_represents values t (fun v => decide (next v)) nonzero retained v)

/-- 証明用の正解述語。scanSetsの計算定義はこの述語を参照しない。 -/
noncomputable def guaranteeFlags [DecidableEq V] (t : Int) (v : V) : Bool := by
  classical
  exact decide (G.LowerGuarantee v t)

/-- 前の閾値での保証を引き継いで解いた集合と、元ゲームの利得保証が一致する。 -/
theorem settled_at_level [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (cap : Int) (cap_positive : 0 < cap) (cap_bounded : cap ≤ G.mate)
    (t : Int) (positive : 0 < t) (lower : t ≤ cap)
    {won : V → Prop} (old : (G.retune cap cap_positive cap_bounded).RankedRegion won) (root : V) :
    (G.retune t positive (Int.le_trans lower cap_bounded)).settle
        vertices core vertices.length won root ↔ G.LowerGuarantee root t := by
  have weakened := old.weaken t positive lower
  exact ((G.retune t positive (Int.le_trans lower cap_bounded)).settle_exact
    vertices covered core covers_core vertices.length weakened (by omega) root).trans
      (G.retune_winning_iff t positive (Int.le_trans lower cap_bounded) root)

/-- 各段階の停止条件は手続きから生成する。勝敗判定の正しさは入力しない。 -/
theorem scanSets_values [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a))
    (cap : Int) (cap_positive : 0 < cap) (cap_bounded : cap ≤ G.mate)
    (below : ∀ t ∈ levels, t ≤ cap)
    {won : V → Prop} (old : (G.retune cap cap_positive cap_bounded).RankedRegion won)
    (values : V → Int) :
    (G.scanSets vertices core levels valid won values).2 =
      scanValues levels G.guaranteeFlags values := by
  classical
  induction levels generalizing cap won values with
  | nil => rfl
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let H := G.retune t positive bounded
    let next := H.settle vertices core vertices.length won
    have lower : t ≤ cap := below t (by simp)
    have weakened : H.RankedRegion won := old.weaken t positive lower
    obtain ⟨next_sound⟩ := H.settle_sound vertices covered core vertices.length weakened
    have flags : (fun v => decide (next v)) = G.guaranteeFlags t := by
      funext v
      change decide (next v) = decide (G.LowerGuarantee v t)
      apply congrArg (fun p : Prop => decide p)
      apply propext
      exact G.settled_at_level vertices covered core covers_core cap cap_positive cap_bounded
        t positive lower old v
    have tail_valid : ∀ s ∈ rest, 0 < s ∧ s ≤ G.mate := fun s member => valid s (by simp [member])
    have tail_below : ∀ s ∈ rest, s ≤ t := fun s member =>
      Int.le_of_lt (List.rel_of_pairwise_cons descending member)
    have continuation := ih tail_valid descending.of_cons t positive bounded tail_below next_sound
      (latchValues values t (fun v => decide (next v)))
    change (G.scanSets vertices core rest tail_valid next
      (latchValues values t (fun v => decide (next v)))).2 = _
    rw [continuation, flags]
    rfl

/-- 空集合と全0の値から、全処理閾値を一続きに解く。 -/
noncomputable def positiveSetValues (vertices : List V) (core : V → Prop)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : V → Int :=
  (G.scanSets vertices core levels valid (fun _ => False) (fun _ => 0)).2

/-- 疎な閾値列を網羅すれば、計算した初回記録は全正整数の最大保証値である。 -/
theorem positiveSetValues_correct [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (levels : List Int) (valid : ∀ t ∈ levels, G.CriticalLevel t)
    (levels_cover : ∀ t, G.CriticalLevel t → t ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a)) (root : V) :
    G.PositiveMaximum root (G.positiveSetValues vertices core levels
      (fun t member => ⟨(valid t member).1, (valid t member).2.1⟩) root) := by
  classical
  have mate_bound : G.mate ≤ G.mate := Int.le_refl _
  have run := G.scanSets_values vertices covered core covers_core levels
    (fun t member => ⟨(valid t member).1, (valid t member).2.1⟩) descending
    G.mate G.mate_positive mate_bound (fun t member => (valid t member).2.1)
    (RankedRegion.empty (G := G.retune G.mate G.mate_positive mate_bound)) (fun _ => 0)
  unfold positiveSetValues
  rw [run, scanValues_initial levels _ (fun t member => (valid t member).1)]
  apply G.firstWinning_complete leaves vertices covered levels valid levels_cover descending
  intro t _
  simp [guaranteeFlags]

/-- 正leafの存在だけで処理閾値を作る。正解の勝敗や最大値は参照しない。 -/
noncomputable def positiveLeafFlags (t : Int) : Bool := by
  classical
  exact decide (∃ v, G.legal v (.leaf t))

noncomputable def setLevels : List Int := processedLevels G.mate.toNat G.positiveLeafFlags

theorem setLevels_critical_iff (t : Int) : t ∈ G.setLevels ↔ G.CriticalLevel t := by
  apply G.processedLevels_critical_iff
  intro level _ _
  simp [positiveLeafFlags]

/-- 入力ゲームから閾値列を作り、確定集合と初回記録値を一続きに計算する。 -/
noncomputable def computedPositiveSetValues (vertices : List V) (core : V → Prop) : V → Int :=
  G.positiveSetValues vertices core G.setLevels (fun t member =>
    ⟨((G.setLevels_critical_iff t).mp member).1, ((G.setLevels_critical_iff t).mp member).2.1⟩)

theorem computedPositiveSetValues_correct [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v) (root : V) :
    G.PositiveMaximum root (G.computedPositiveSetValues vertices core root) :=
  G.positiveSetValues_correct leaves vertices covered core covers_core G.setLevels
    (fun t member => (G.setLevels_critical_iff t).mp member)
    (fun t critical => (G.setLevels_critical_iff t).mpr critical)
    (processedLevels_ordered _ _) root

/-- 両プレイヤーの同じ集合算法を実行し、固定プレイヤー視点の整数値へ戻す。 -/
noncomputable def computedSetValue (vertices : List V) (ownCore otherCore : V → Prop) : V → Int :=
  fun v => G.computedPositiveSetValues vertices ownCore v -
    G.opposite.computedPositiveSetValues vertices otherCore v

/-- 全閾値の停止証拠や各閾値の正解を外から与えない、集合算法全体の値の正当性。 -/
theorem computedSetValue_exact [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (ownCore otherCore : V → Prop)
    (own_covers : ∀ v, CyclicVertex G.OpponentChecking v → ownCore v)
    (other_covers : ∀ v, CyclicVertex G.opposite.OpponentChecking v → otherCore v) (root : V) :
    G.ExactValue root (G.computedSetValue vertices ownCore otherCore root) :=
  G.merge_positive_maxima leaves vertices covered root
    (G.computedPositiveSetValues_correct leaves vertices covered ownCore own_covers root)
    (G.opposite.computedPositiveSetValues_correct (G.opposite_bounded_leaves leaves)
      vertices covered otherCore other_covers root)

/-- 両側の王手循環頂点を候補に使う、集合算法全体の標準的な値定義。 -/
noncomputable def petaSetValue (vertices : List V) : V → Int :=
  G.computedSetValue vertices (CyclicVertex G.OpponentChecking) (CyclicVertex G.opposite.OpponentChecking)

theorem petaSetValue_exact [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    G.ExactValue root (G.petaSetValue vertices root) :=
  G.computedSetValue_exact leaves vertices covered _ _ (fun _ h => h) (fun _ h => h) root

/-- 正しい循環集合を含む上位集合を使っても、求まるゲーム値は変わらない。 -/
theorem computedSetValue_core_independent [DecidableEq V] (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (ownCore otherCore : V → Prop)
    (own_covers : ∀ v, CyclicVertex G.OpponentChecking v → ownCore v)
    (other_covers : ∀ v, CyclicVertex G.opposite.OpponentChecking v → otherCore v) (root : V) :
    G.computedSetValue vertices ownCore otherCore root = G.petaSetValue vertices root :=
  ExactValue.unique G vertices covered root
    (G.computedSetValue_exact leaves vertices covered ownCore otherCore own_covers other_covers root)
    (G.petaSetValue_exact leaves vertices covered root)

end PetaProof.ThresholdGame
