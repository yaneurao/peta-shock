import PetaProof.StableBuckets

/-! 一回分配したleaf表を順に読む走査と、帯filterによる既存仕様の一致。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable (ctx : QueueContext G E)

def bandSelect (lo hi : Int) (edge : E) : Bool := match ctx.indexed.move edge with
  | .node _ => false
  | .leaf score => decide (lo ≤ score ∧ score < hi)

def initialSelect (edge : E) : Bool := match ctx.indexed.move edge with
  | .node _ => false
  | .leaf score => decide (G.threshold ≤ score)

theorem bandSelect_spec (lo hi : Int) (edge : E) : ctx.bandSelect lo hi edge = true ↔
    ∃ score, ctx.indexed.move edge = .leaf score ∧ lo ≤ score ∧ score < hi := by
  cases move : ctx.indexed.move edge <;> simp [bandSelect, move]

def bandSelectors : Int → List Int → List (E → Bool)
  | _, [] => []
  | hi, lo :: rest => ctx.bandSelect lo hi :: bandSelectors lo rest

theorem bandSelectors_below (hi : Int) (levels : List Int)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ hi)
    (select : E → Bool) (member : select ∈ ctx.bandSelectors hi levels) (edge : E)
    (active : select edge = true) : ∃ score, ctx.indexed.move edge = .leaf score ∧ score < hi := by
  induction levels generalizing hi with
  | nil => cases member
  | cons lo rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst select
      obtain ⟨score, move, _, upper⟩ := (ctx.bandSelect_spec lo hi edge).mp active
      exact ⟨score, move, upper⟩
    · obtain ⟨score, move, upper⟩ := ih lo descending.of_cons
        (fun t present => Int.le_of_lt (List.rel_of_pairwise_cons descending present)) tail
      exact ⟨score, move, Int.lt_of_lt_of_le upper (below lo (by simp))⟩

theorem bandSelectors_disjoint (hi : Int) (levels : List Int)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ hi) :
    StableBuckets.Disjoint (ctx.bandSelectors hi levels) := by
  induction levels generalizing hi with
  | nil => exact List.Pairwise.nil
  | cons lo rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih lo descending.of_cons (fun t present => Int.le_of_lt (List.rel_of_pairwise_cons descending present))⟩
    intro select member edge active
    cases other : select edge with
    | false => rfl
    | true =>
      obtain ⟨a, ha, lower, _⟩ := (ctx.bandSelect_spec lo hi edge).mp active
      obtain ⟨b, hb, upper⟩ := ctx.bandSelectors_below lo rest descending.of_cons
        (fun t present => Int.le_of_lt (List.rel_of_pairwise_cons descending present)) select member edge other
      have same := Move.leaf.inj (ha.symm.trans hb)
      omega

def leafSelectors (levels : List Int) : List (E → Bool) := ctx.initialSelect :: ctx.bandSelectors G.threshold levels

theorem leafSelectors_disjoint (levels : List Int)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    StableBuckets.Disjoint (ctx.leafSelectors levels) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, ctx.bandSelectors_disjoint G.threshold levels descending below⟩
  intro select member edge active
  cases other : select edge with
  | false => rfl
  | true =>
    obtain ⟨score, move, upper⟩ := ctx.bandSelectors_below G.threshold levels descending below select member edge other
    have lower : G.threshold ≤ score := by simpa [initialSelect, move] using active
    omega

def bandBatches : Int → List Int → List (List E)
  | _, [] => []
  | hi, lo :: rest => ctx.leafBand lo hi :: bandBatches lo rest

theorem bandBatches_retune (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (hi : Int) (levels : List Int) :
    (ctx.atLevel t positive bounded).bandBatches hi levels = ctx.bandBatches hi levels := by
  induction levels generalizing hi with
  | nil => rfl
  | cons lo rest ih => simp only [bandBatches, ih]; rfl

theorem bandSelectors_filters (hi : Int) (levels : List Int) :
    (ctx.bandSelectors hi levels).map (fun select => ctx.allEdges.filter select) = ctx.bandBatches hi levels := by
  induction levels generalizing hi with
  | nil => rfl
  | cons lo rest ih => simp only [bandSelectors, List.map_cons, bandBatches, ih]; rfl

/-- 表は入力辺を一回走査して構築する。routeのキー判定費用は別に数える。 -/
def leafTable (levels : List Int) : Nat → List E := StableBuckets.table (ctx.leafSelectors levels) ctx.allEdges

def leafBatches (levels : List Int) : List (List E) :=
  StableBuckets.collect (levels.length + 1) (ctx.leafTable levels)

theorem bandSelectors_length (hi : Int) (levels : List Int) :
    (ctx.bandSelectors hi levels).length = levels.length := by
  induction levels generalizing hi with
  | nil => rfl
  | cons lo rest ih => simp only [bandSelectors, List.length_cons, ih]

theorem leafBatches_eq (levels : List Int)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.leafBatches levels = ctx.goodLeaves :: ctx.bandBatches G.threshold levels := by
  have collected := StableBuckets.collect_table (ctx.leafSelectors levels) ctx.allEdges
    (ctx.leafSelectors_disjoint levels descending below)
  have count : (ctx.leafSelectors levels).length = levels.length + 1 := by
    simp only [leafSelectors, List.length_cons, bandSelectors_length]
  rw [count] at collected
  simpa only [leafBatches, leafTable, leafSelectors, List.map_cons, bandSelectors_filters] using collected

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- 各閾値では構築済みの次の行を消費し、元辺一覧へ戻らない。 -/
def scanFromBatches : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → List (List E) →
    PropagationState V E → (V → Int) → PropagationState V E × (V → Int)
  | _, _, [], _, _, state, values => (state, values)
  | G, ctx, t :: rest, valid, batches, state, values =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    let prepared := state.notifyMany low.indexed (batches.headD [])
    let next := low.settleQueue ctx.vertices.length prepared
    scanFromBatches (G.retune t positive bounded) low rest
      (fun s member => valid s (by simp [member])) batches.tail next
      (latchValues values t (fun vertex => (next.counters vertex).admitted))

theorem scanFromBatches_eq (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) (values : V → Int) :
    scanFromBatches G ctx levels valid (ctx.bandBatches G.threshold levels) state values =
      scanQueues G ctx levels valid state values := by
  induction levels generalizing G state values with
  | nil => rfl
  | cons t rest ih =>
    simp only [QueueContext.bandBatches, scanFromBatches, List.headD_cons, List.tail_cons, scanQueues]
    simpa only [QueueContext.phase, QueueContext.prepare, QueueContext.bandBatches_retune] using
      ih (G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
        (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2)
        (fun s member => valid s (by simp [member])) (ctx.phase t (valid t (by simp)).1 (valid t (by simp)).2 state)
        (latchValues values t (fun vertex => ((ctx.phase t (valid t (by simp)).1 (valid t (by simp)).2 state).counters vertex).admitted))

theorem bucketedScan_eq (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (values : V → Int) :
    let batches := ctx.leafBatches levels
    scanFromBatches G ctx levels valid batches.tail
      ((PropagationState.initial ctx.indexed).notifyMany ctx.indexed (batches.headD [])) values =
      scanQueues G ctx levels valid ctx.seeded values := by
  rw [ctx.leafBatches_eq levels descending below]
  exact scanFromBatches_eq G ctx levels valid ctx.seeded values

end PetaProof.ThresholdGame

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

omit [DecidableEq V] [DecidableEq E] in
theorem bandBatches_flatten (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    (ctx.bandBatches G.threshold levels).flatten = scanLeafLog G ctx levels valid := by
  induction levels generalizing G with
  | nil => rfl
  | cons t rest ih =>
    have tailResult := ih (G := G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
      (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2)
      (fun s member => valid s (by simp [member]))
    rw [bandBatches_retune] at tailResult
    exact congrArg (fun edges => ctx.leafBand t G.threshold ++ edges) tailResult

omit [DecidableEq V] [DecidableEq E] in
theorem leafBatches_flatten (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.leafBatches levels).flatten = ctx.leafLog levels valid := by
  rw [ctx.leafBatches_eq levels descending below, List.flatten_cons, ctx.bandBatches_flatten levels valid]
  rfl

omit [DecidableEq V] in
theorem leafBatches_notifications_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.leafBatches levels).flatten.length ≤ ctx.allEdges.length := by
  rw [ctx.leafBatches_flatten levels valid descending below]
  exact DistinctWork.length_le _ _ (ctx.leafLog_unique levels valid descending below) (fun edge _ => ctx.allEdges_contains edge)

omit [DecidableEq V] [DecidableEq E] in
theorem leafTable_from_key (levels : List Int) (key : E → Option Nat)
    (correct : ∀ edge, key edge = StableBuckets.route (ctx.leafSelectors levels) edge) :
    StableBuckets.buildKey key ctx.allEdges (fun _ => []) = ctx.leafTable levels :=
  StableBuckets.buildKey_correct _ key correct _ _

omit [DecidableEq V] [DecidableEq E] in
theorem leafTable_registrations_bound (levels : List Int) :
    StableBuckets.registrations (StableBuckets.route (ctx.leafSelectors levels)) ctx.allEdges ≤ ctx.allEdges.length :=
  StableBuckets.registrations_bound _ _

omit [DecidableEq V] [DecidableEq E] in
theorem leafBatches_length (levels : List Int) : (ctx.leafBatches levels).length = levels.length + 1 :=
  StableBuckets.collect_length _ _

/-- 行の初期化・読出し、入力辺訪問、登録、通知を数える。キー算出と格納の演算時間は別。 -/
def bucketEventWork (levels : List Int) : Nat :=
  2 * (levels.length + 1) + ctx.allEdges.length +
    StableBuckets.registrations (StableBuckets.route (ctx.leafSelectors levels)) ctx.allEdges +
    (ctx.leafBatches levels).flatten.length

omit [DecidableEq V] in
theorem bucketEventWork_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.bucketEventWork levels ≤ 3 * ctx.allEdges.length + 2 * (levels.length + 1) := by
  have registrations := ctx.leafTable_registrations_bound levels
  have notifications := ctx.leafBatches_notifications_bound levels valid descending below
  unfold bucketEventWork
  omega

end PetaProof.ThresholdGame.QueueContext
