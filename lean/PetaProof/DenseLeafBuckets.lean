import PetaProof.DenseThresholdKeys

/-! 一度構築した整数キー配列をleaf分配へ接続する。高域・非正域は境界判定で処理する。 -/
namespace PetaProof.ThresholdKeys

theorem find_none (levels : List Int) (score : Int) (below : ∀ t ∈ levels, score < t) :
    find levels score = none := by
  induction levels with
  | nil => rfl
  | cons threshold rest ih =>
    have lower := below threshold (by simp)
    simp only [find, if_neg (show ¬ threshold ≤ score by omega)]
    rw [ih (fun t member => below t (by simp [member]))]
    rfl

end PetaProof.ThresholdKeys

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable (ctx : QueueContext G E)

theorem band_route_node (hi : Int) (levels : List Int) (edge : E) (target : V)
    (move : ctx.indexed.move edge = .node target) :
    StableBuckets.route (ctx.bandSelectors hi levels) edge = none := by
  induction levels generalizing hi with
  | nil => rfl
  | cons threshold rest ih => simp [bandSelectors, StableBuckets.route, bandSelect, move, ih]

theorem band_route_leaf (hi : Int) (levels : List Int) (edge : E) (score : Int)
    (move : ctx.indexed.move edge = .leaf score) (below : score < hi) :
    StableBuckets.route (ctx.bandSelectors hi levels) edge = ThresholdKeys.find levels score := by
  induction levels generalizing hi with
  | nil => rfl
  | cons threshold rest ih =>
    by_cases hit : threshold ≤ score
    · simp [bandSelectors, StableBuckets.route, bandSelect, move, hit, below, ThresholdKeys.find]
    · have lower : score < threshold := by omega
      simp [bandSelectors, StableBuckets.route, bandSelect, move, hit, below, ThresholdKeys.find, ih threshold lower]

theorem route_leaf_find (levels : List Int) (edge : E) (score : Int)
    (move : ctx.indexed.move edge = .leaf score) :
    StableBuckets.route (ctx.leafSelectors levels) edge = ThresholdKeys.find (G.threshold :: levels) score := by
  by_cases high : G.threshold ≤ score
  · simp [leafSelectors, StableBuckets.route, initialSelect, move, ThresholdKeys.find, high]
  · have below : score < G.threshold := by omega
    simp [leafSelectors, StableBuckets.route, initialSelect, move, ThresholdKeys.find, high,
      ctx.band_route_leaf G.threshold levels edge score move below]

/-- tableは全辺の分配前に一度構築済み。leafごとの再構築をしない。 -/
def directKey (table : Array (Option Nat)) (edge : E) : Option Nat :=
  match ctx.indexed.move edge with
  | .node _ => none
  | .leaf score =>
    if G.threshold ≤ score then some 0
    else if score ≤ 0 then none
    else
      let index := (G.mate - score).toNat
      if valid : index < table.size then table[index] else none

def scoreKeyTable (_ctx : QueueContext G E) (levels : List Int) : Array (Option Nat) :=
  ThresholdKeys.dense (G.threshold :: levels) G.mate (G.mate.toNat + 1)

theorem directKey_correct (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (edge : E) :
    ctx.directKey (ctx.scoreKeyTable levels) edge = StableBuckets.route (ctx.leafSelectors levels) edge := by
  cases move : ctx.indexed.move edge with
  | node target =>
    simp [directKey, move, leafSelectors, StableBuckets.route, initialSelect, ctx.band_route_node G.threshold levels edge target move]
  | leaf score =>
    rw [ctx.route_leaf_find levels edge score move]
    by_cases high : G.threshold ≤ score
    · simp [directKey, move, high, ThresholdKeys.find]
    · by_cases low : score ≤ 0
      · have absent := ThresholdKeys.find_none (G.threshold :: levels) score (by
          intro threshold member
          rcases List.mem_cons.mp member with same | later
          · subst threshold; have positive := G.positive; omega
          · have positive := (valid threshold later).1; omega)
        simpa [directKey, move, high, low] using absent.symm
      · let index := (G.mate - score).toNat
        have nonnegative : 0 ≤ G.mate - score := by have bounded := G.bounded; omega
        have restored : G.mate - Int.ofNat index = score := by
          dsimp [index]
          rw [Int.toNat_of_nonneg nonnegative]
          omega
        have indexBound : index < G.mate.toNat + 1 := by
          have matePositive := G.mate_positive
          dsimp [index]
          omega
        have inTable : index < (ctx.scoreKeyTable levels).size := by
          simpa only [scoreKeyTable, ThresholdKeys.dense_size] using indexBound
        simp only [directKey, move, if_neg high, if_neg low]
        change (if h : index < (ctx.scoreKeyTable levels).size then (ctx.scoreKeyTable levels)[index] else none) = _
        rw [dif_pos inTable]
        change (ThresholdKeys.dense (G.threshold :: levels) G.mate (G.mate.toNat + 1))[index]'inTable = _
        rw [ThresholdKeys.dense_at _ _ _ index indexBound, restored]

/-- キー表を一度作り、次に全元辺を一度分配する。 -/
def denseLeafTable (levels : List Int) : Nat → List E :=
  let keys := ctx.scoreKeyTable levels
  StableBuckets.buildKey (ctx.directKey keys) ctx.allEdges (fun _ => [])

theorem denseLeafTable_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    ctx.denseLeafTable levels = ctx.leafTable levels :=
  ctx.leafTable_from_key levels _ (ctx.directKey_correct levels valid)

theorem scoreKeyTable_size (levels : List Int) :
    (ctx.scoreKeyTable levels).size = G.mate.toNat + 1 := ThresholdKeys.dense_size _ _ _

theorem scoreKeyTable_comparisons (levels : List Int) :
    ThresholdKeys.comparisons (G.threshold :: levels)
      (ThresholdKeys.scoreRange G.mate (G.mate.toNat + 1)) ≤ levels.length + 1 + (G.mate.toNat + 1) :=
  ThresholdKeys.dense_comparisons_bound _ _ _

def denseLeafBatches (levels : List Int) : List (List E) :=
  StableBuckets.collect (levels.length + 1) (ctx.denseLeafTable levels)

theorem denseLeafBatches_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    ctx.denseLeafBatches levels = ctx.leafBatches levels := by
  simp only [denseLeafBatches, ctx.denseLeafTable_eq levels valid, leafBatches]

/-- 型分岐・境界比較・範囲検査・一回の配列参照を数える。 -/
def directKeyWork (table : Array (Option Nat)) (edge : E) : Nat :=
  match ctx.indexed.move edge with
  | .node _ => 1
  | .leaf score => 2 + if G.threshold ≤ score then 0 else
      1 + if score ≤ 0 then 0 else 1 + if (G.mate - score).toNat < table.size then 1 else 0

theorem directKeyWork_bound (table : Array (Option Nat)) (edge : E) : ctx.directKeyWork table edge ≤ 5 := by
  cases move : ctx.indexed.move edge with
  | node _ => simp [directKeyWork, move]
  | leaf score =>
    simp only [directKeyWork, move]
    split <;> (try split) <;> (try split) <;> omega

def inputKeyWork (table : Array (Option Nat)) : List E → Nat
  | [] => 0
  | edge :: rest => ctx.directKeyWork table edge + inputKeyWork table rest

theorem inputKeyWork_bound (table : Array (Option Nat)) (edges : List E) :
    ctx.inputKeyWork table edges ≤ 5 * edges.length := by
  induction edges with
  | nil => simp [inputKeyWork]
  | cons edge rest ih =>
    have one := ctx.directKeyWork_bound table edge
    simp only [inputKeyWork, List.length_cons]
    omega

theorem directRegistrations_eq (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    StableBuckets.registrations (ctx.directKey (ctx.scoreKeyTable levels)) ctx.allEdges =
      StableBuckets.registrations (StableBuckets.route (ctx.leafSelectors levels)) ctx.allEdges := by
  have same : ctx.directKey (ctx.scoreKeyTable levels) = StableBuckets.route (ctx.leafSelectors levels) :=
    funext (ctx.directKey_correct levels valid)
  rw [same]

/-- 評価値列・merge出力・キー抽出・配列化の四走査と、比較・入力キー参照の会計。 -/
def keyPreparationWork (levels : List Int) : Nat :=
  ThresholdKeys.comparisons (G.threshold :: levels)
      (ThresholdKeys.scoreRange G.mate (G.mate.toNat + 1)) +
    4 * (G.mate.toNat + 1) + ctx.inputKeyWork (ctx.scoreKeyTable levels) ctx.allEdges

theorem keyPreparationWork_bound (levels : List Int) :
    ctx.keyPreparationWork levels ≤ levels.length + 1 + 5 * (G.mate.toNat + 1) + 5 * ctx.allEdges.length := by
  have comparisons := scoreKeyTable_comparisons (G := G) levels
  have lookups := ctx.inputKeyWork_bound (ctx.scoreKeyTable levels) ctx.allEdges
  unfold keyPreparationWork
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

theorem denseBucketedScan_eq (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (values : V → Int) :
    let batches := ctx.denseLeafBatches levels
    scanFromBatches G ctx levels valid batches.tail
      ((PropagationState.initial ctx.indexed).notifyMany ctx.indexed (batches.headD [])) values =
      scanQueues G ctx levels valid ctx.seeded values := by
  rw [ctx.denseLeafBatches_eq levels valid]
  exact bucketedScan_eq G ctx levels valid descending below values

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

omit [DecidableEq V] in
theorem denseBucketEvents_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.keyPreparationWork levels + ctx.bucketEventWork levels ≤
      8 * ctx.allEdges.length + 5 * (G.mate.toNat + 1) + 3 * (levels.length + 1) := by
  have keys := ctx.keyPreparationWork_bound levels
  have buckets := ctx.bucketEventWork_bound levels valid descending below
  omega

end QueueContext

end PetaProof.ThresholdGame
