import PetaProof.OrdinaryClosure
import PetaProof.FiniteGame
import PetaProof.SparseStopped

/-!
固定閾値の集合仕様による制御手続き。通常閉包を求めた後、局所集合が空なら終了し、
非空なら一括追加して繰り返す。高速キュー版の実行時間をこの同期仕様から主張しない。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

theorem pruneIter_add (won initial : V → Prop) (a b : Nat) :
    G.pruneIter won initial (a + b) = G.pruneIter won (G.pruneIter won initial a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, pruneIter, ih, pruneIter]

theorem prune_of_safe {won current : V → Prop} (safe : G.SafeSet won current) : G.prune won current = current := by
  funext v
  apply propext
  exact ⟨And.left, fun hv => ⟨hv, safe v hv⟩⟩

theorem pruneIter_of_safe {won current : V → Prop} (safe : G.SafeSet won current) (n : Nat) :
    G.pruneIter won current n = current := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pruneIter, ih, prune_of_safe G safe]

def localResult (vertices : List V) (core won : V → Prop) : V → Prop :=
  G.pruneIter won (fun v => core v ∧ ¬ won v) vertices.length

theorem localResult_safe (vertices : List V) (covered : ∀ v, v ∈ vertices) (core won : V → Prop) :
    G.SafeSet won (G.localResult vertices core won) := by
  obtain ⟨n, bound, safe⟩ := G.stable_exists vertices (fun v _ => covered v) (won := won) (initial := fun v => core v ∧ ¬ won v)
  have split : vertices.length = n + (vertices.length - n) := by omega
  unfold localResult
  rw [split, pruneIter_add, pruneIter_of_safe G safe]
  exact safe

theorem localResult_fresh (vertices : List V) (core won : V → Prop) :
    ∀ v, G.localResult vertices core won v → ¬ won v := fun v inside =>
  (G.iterate_subset vertices.length v inside).2

theorem localResult_greatest (vertices : List V) (core won safe : V → Prop)
    (valid : G.SafeSet won safe) (within : ∀ v, safe v → core v ∧ ¬ won v) :
    ∀ v, safe v → G.localResult vertices core won v := G.safe_survives valid within vertices.length

/-- fuelは証明用の上界。適切な上界の下で0分岐に未完了の局所集合は残らない。 -/
noncomputable def settle (vertices : List V) (core : V → Prop) : Nat → (V → Prop) → (V → Prop)
  | 0, won => G.ordinaryClosure vertices won
  | fuel + 1, won => by
    classical
    let closed := G.ordinaryClosure vertices won
    let batchSet := G.localResult vertices core closed
    exact if ∃ v, batchSet v then settle vertices core fuel (fun v => closed v ∨ batchSet v) else closed

theorem settle_extends (vertices : List V) (core : V → Prop) (fuel : Nat) (won : V → Prop) :
    ∀ v, won v → G.settle vertices core fuel won v := by
  classical
  induction fuel generalizing won with
  | zero => exact G.ordinaryClosure_subset vertices won
  | succ fuel ih =>
    by_cases nonempty : ∃ v, G.localResult vertices core (G.ordinaryClosure vertices won) v
    · simp only [settle, if_pos nonempty]
      exact fun v inside => ih (fun v => G.ordinaryClosure vertices won v ∨
        G.localResult vertices core (G.ordinaryClosure vertices won) v) v
          (Or.inl (G.ordinaryClosure_subset vertices won v inside))
    · simp only [settle, if_neg nonempty]
      exact G.ordinaryClosure_subset vertices won

theorem population_full (vertices : List V) (covered : ∀ v, v ∈ vertices) (won : V → Prop)
    (full : vertices.length ≤ population vertices won) : ∀ v, won v := by
  classical
  have equal : (vertices.filter (fun v => decide (won v))).length = vertices.length :=
    Nat.le_antisymm (population_bound vertices won) full
  have all := List.length_filter_eq_length_iff.mp equal
  intro v
  exact of_decide_eq_true (all v (covered v))

/-- 非空分岐から新規頂点を具体的に取り出して、再帰の残予算を導く。外部の進捗仮定はない。 -/
theorem settle_stops (vertices : List V) (covered : ∀ v, v ∈ vertices) (core : V → Prop)
    (fuel : Nat) (won : V → Prop) (budget : vertices.length ≤ population vertices won + fuel) :
    G.OrdinaryClosed (G.settle vertices core fuel won) ∧
      ∀ v, ¬ G.localResult vertices core (G.settle vertices core fuel won) v := by
  classical
  induction fuel generalizing won with
  | zero =>
    have full := population_full vertices covered won (by simpa using budget)
    refine ⟨G.ordinaryClosure_closed vertices covered won, ?_⟩
    intro v inside
    exact G.localResult_fresh vertices core _ v inside (G.ordinaryClosure_subset vertices won v (full v))
  | succ fuel ih =>
    let closed := G.ordinaryClosure vertices won
    let batchSet := G.localResult vertices core closed
    by_cases nonempty : ∃ v, batchSet v
    · have witness := nonempty
      obtain ⟨v, inside⟩ := witness
      have fresh := G.localResult_fresh vertices core closed v inside
      have strict := population_strict_subset vertices closed (fun v => closed v ∨ batchSet v)
        (fun _ => Or.inl) v (covered v) (Or.inr inside) fresh
      have earlier := population_mono vertices (G.ordinaryClosure_subset vertices won)
      change population vertices won ≤ population vertices closed at earlier
      have next_budget : vertices.length ≤ population vertices (fun v => closed v ∨ batchSet v) + fuel := by omega
      change (∃ v, G.localResult vertices core (G.ordinaryClosure vertices won) v) at nonempty
      simpa only [settle, if_pos nonempty] using ih (fun v => closed v ∨ batchSet v) next_budget
    · change ¬ (∃ v, G.localResult vertices core (G.ordinaryClosure vertices won) v) at nonempty
      simp only [settle, if_neg nonempty]
      exact ⟨G.ordinaryClosure_closed vertices covered won, fun v inside => nonempty ⟨v, inside⟩⟩

theorem settle_sound (vertices : List V) (covered : ∀ v, v ∈ vertices) (core : V → Prop)
    (fuel : Nat) {won : V → Prop} (old : G.RankedRegion won) :
    Nonempty (G.RankedRegion (G.settle vertices core fuel won)) := by
  classical
  induction fuel generalizing won with
  | zero => exact G.ordinaryClosure_sound vertices old
  | succ fuel ih =>
    let closed := G.ordinaryClosure vertices won
    let batchSet := G.localResult vertices core closed
    obtain ⟨before⟩ := G.ordinaryClosure_sound vertices old
    by_cases nonempty : ∃ v, batchSet v
    · let batch := G.batchOfSafeSet (G.localResult_safe vertices covered core closed)
        (G.localResult_fresh vertices core closed)
      change (∃ v, G.localResult vertices core (G.ordinaryClosure vertices won) v) at nonempty
      simpa only [settle, if_pos nonempty] using ih (won := fun v => closed v ∨ batchSet v) (before.extend batch)
    · change ¬ (∃ v, G.localResult vertices core (G.ordinaryClosure vertices won) v) at nonempty
      simpa only [settle, if_neg nonempty] using Nonempty.intro before

noncomputable def thresholdResult (vertices : List V) (core : V → Prop) : V → Prop :=
  G.settle vertices core vertices.length (fun _ => False)

theorem thresholdResult_stops (vertices : List V) (covered : ∀ v, v ∈ vertices) (core : V → Prop) :
    G.OrdinaryClosed (G.thresholdResult vertices core) ∧
      ∀ v, ¬ G.localResult vertices core (G.thresholdResult vertices core) v :=
  G.settle_stops vertices covered core vertices.length (fun _ => False) (by omega)

theorem thresholdResult_sound (vertices : List V) (covered : ∀ v, v ∈ vertices) (core : V → Prop) :
    Nonempty (G.RankedRegion (G.thresholdResult vertices core)) :=
  G.settle_sound vertices covered core vertices.length (RankedRegion.empty (G := G))

/-- 既に保証済みの集合から開始しても、同じ固定閾値の勝利領域まで到達する。 -/
theorem settle_exact [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (fuel : Nat) {won : V → Prop} (old : G.RankedRegion won)
    (budget : vertices.length ≤ population vertices won + fuel) (root : V) :
    G.settle vertices core fuel won root ↔ G.FourfoldWinning root := by
  obtain ⟨sound⟩ := G.settle_sound vertices covered core fuel old
  obtain ⟨ordinary, empty⟩ := G.settle_stops vertices covered core fuel won budget
  exact G.stopped_exact_for_fourfold sound ordinary vertices covered core covers_core vertices.length empty root

/-- 求めた集合の停止証拠を入力せず、手続きの返却値から完全性を導く。 -/
theorem thresholdResult_exact [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v) (root : V) :
    G.thresholdResult vertices core root ↔ G.FourfoldWinning root := by
  obtain ⟨sound⟩ := G.thresholdResult_sound vertices covered core
  obtain ⟨ordinary, empty⟩ := G.thresholdResult_stops vertices covered core
  exact G.stopped_exact_for_fourfold sound ordinary vertices covered core covers_core vertices.length empty root

/-- 疎な閾値走査が要求していた停止証拠を、集合制御の返却値から生成する。 -/
noncomputable def computedThresholdStop (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate) : G.StoppedThreshold level positive bounded where
  won := (G.retune level positive bounded).thresholdResult vertices core
  sound := Classical.choice ((G.retune level positive bounded).thresholdResult_sound vertices covered core)
  ordinary := ((G.retune level positive bounded).thresholdResult_stops vertices covered core).1
  core := core
  covers_core := covers_core
  rounds := vertices.length
  empty := ((G.retune level positive bounded).thresholdResult_stops vertices covered core).2

theorem computedThresholdStop_correct [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate) (root : V) :
    (G.computedThresholdStop vertices covered core covers_core level positive bounded).won root ↔
      G.LowerGuarantee root level :=
  StoppedThreshold.correct _ vertices covered root

end PetaProof.ThresholdGame
