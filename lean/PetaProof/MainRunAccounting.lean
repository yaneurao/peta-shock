import PetaProof.StreamingRecords

/-! 主値計算のイベント会計を統合する。leaf通知は通常伝播へ一度だけ課金する。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v}

/-- 正の相異なる整数閾値は上限Mの個数を超えない。 -/
theorem level_count_bound (G : ThresholdGame V) (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) : levels.length ≤ G.mate.toNat := by
  let domain := (List.range G.mate.toNat).map (fun (index : Nat) => (index : Int) + 1)
  have unique : levels.Nodup := descending.imp (by intro a b less same; omega)
  have bound := DistinctWork.length_le levels domain unique (by
    intro level member
    have range := valid level member
    let index := (level - 1).toNat
    have nonnegative : 0 ≤ level - 1 := by omega
    have equal : (index : Int) + 1 = level := by
      dsimp [index]
      rw [Int.toNat_of_nonneg nonnegative]
      omega
    have inside : index < G.mate.toNat := by
      have positive := G.mate_positive
      dsimp [index]
      omega
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr inside, equal⟩)
  simpa only [domain, List.length_map, List.length_range] using bound

/-- 別々の種類の操作を混ぜず、重複計上の有無を項ごとに検査できる帳簿。 -/
structure MainLedger where
  initialization : Nat
  keys : Nat
  bucketPreparation : Nat
  ordinary : Nat
  localAnalysis : Nat
  batchInsertions : Nat
  records : Nat
  thresholdControl : Nat
  localControl : Nat

def MainLedger.total (ledger : MainLedger) : Nat :=
  ledger.initialization + ledger.keys + ledger.bucketPreparation + ledger.ordinary + ledger.localAnalysis +
    ledger.batchInsertions + ledger.records + ledger.thresholdControl + ledger.localControl

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

/-- 行初期化・値の0初期化・core一覧作成の各N件と、全出次数の一回走査。 -/
def initializationWork : Nat :=
  ctx.vertices.length + (ctx.vertices.map (fun vertex => (ctx.indexed.outgoing vertex).length)).sum +
    ctx.vertices.length + ctx.vertices.length

theorem initializationWork_eq : ctx.initializationWork = 3 * ctx.vertices.length + ctx.allEdges.length := by
  have edges : (ctx.vertices.map (fun vertex => (ctx.indexed.outgoing vertex).length)).sum = ctx.allEdges.length := by
    simp only [allEdges, List.length_flatMap]
  unfold initializationWork
  omega

/-- 通知そのものは含めない。leaf通知はordinaryの通知ログに既に含まれる。 -/
def bucketPreparationWork (levels : List Int) : Nat :=
  2 * (levels.length + 1) + ctx.allEdges.length +
    StableBuckets.registrations (StableBuckets.route (ctx.leafSelectors levels)) ctx.allEdges

theorem bucketEventWork_split (levels : List Int) :
    ctx.bucketEventWork levels = ctx.bucketPreparationWork levels + (ctx.leafBatches levels).flatten.length := rfl

theorem bucketPreparationWork_bound (levels : List Int) :
    ctx.bucketPreparationWork levels ≤ 2 * ctx.allEdges.length + 2 * (levels.length + 1) := by
  have registrations := ctx.leafTable_registrations_bound levels
  unfold bucketPreparationWork
  omega

theorem coreSize_bound : ctx.coreSize ≤ ctx.vertices.length := List.length_filter_le _ _

theorem coreEdges_bound : ctx.coreEdges.length ≤ ctx.allEdges.length := List.length_filter_le _ _

theorem coreEdges_empty (empty : ctx.coreSize = 0) : ctx.coreEdges = [] := by
  have verticesEmpty : ctx.vertices.filter ctx.core = [] := List.length_eq_zero_iff.mp empty
  have outside : ∀ vertex, ctx.core vertex = false := by
    intro vertex
    cases inside : ctx.core vertex with
    | false => rfl
    | true =>
      have member := List.mem_filter.mpr ⟨ctx.covered vertex, inside⟩
      rw [verticesEmpty] at member
      cases member
  simp [coreEdges, outside]

variable [DecidableEq V] [DecidableEq E]

def mainLedger (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : MainLedger where
  initialization := ctx.initializationWork
  keys := ctx.keyPreparationWork levels
  bucketPreparation := ctx.bucketPreparationWork levels
  ordinary := ctx.ordinaryWork levels valid
  localAnalysis := scanPreparedWork G ctx levels valid ctx.seeded
  batchInsertions := (scanLocalCalls G ctx levels valid ctx.seeded).flatten.length
  records := (ctx.denseStreamingResult levels valid).attempts
  thresholdControl := levels.length
  localControl := (scanLocalCalls G ctx levels valid ctx.seeded).length

def mainWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  (ctx.mainLedger levels valid).total

def localTerm (levels : List Int) : Nat :=
  (ctx.coreSize + levels.length) * (3 * ctx.coreSize + 4 * ctx.coreEdges.length)

def mainBudget (levels : List Int) : Nat :=
  5 * ctx.vertices.length + 9 * ctx.allEdges.length + 2 * ctx.coreSize + 5 * (G.mate.toNat + 1) +
    5 * levels.length + 3 + ctx.localTerm levels

theorem mainWork_split (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    ctx.mainWork levels valid = ctx.initializationWork + ctx.keyPreparationWork levels +
      ctx.bucketPreparationWork levels + ctx.preparedPropagationWork levels valid +
      (ctx.denseStreamingResult levels valid).attempts + levels.length +
      (scanLocalCalls G ctx levels valid ctx.seeded).length := by
  simp only [mainWork, mainLedger, MainLedger.total, preparedPropagationWork]
  omega

theorem mainLedger_records (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.mainLedger levels valid).records = (ctx.ordinaryLog levels valid).pops.length := by
  simp only [mainLedger, ctx.denseStreamingResult_eq levels valid descending below, ctx.streamingResult_attempts]

theorem mainWork_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.mainWork levels valid ≤ ctx.mainBudget levels := by
  have initialization := ctx.initializationWork_eq
  have keys := ctx.keyPreparationWork_bound levels
  have buckets := ctx.bucketPreparationWork_bound levels
  have propagation := ctx.preparedPropagationWork_bound levels valid descending below
  have records := ctx.denseStreamingResult_attempts_bound levels valid descending below
  have calls := ctx.scanLocalCalls_bound levels valid ctx.seeded
  rw [ctx.mainWork_split]
  unfold mainBudget localTerm
  omega

/-- K≤N、D≤Mを使い、線形項と王手循環に局限した反復項へ分離する。 -/
theorem mainWork_linear_part_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.mainWork levels valid ≤ 7 * ctx.vertices.length + 9 * ctx.allEdges.length +
      13 * (G.mate.toNat + 1) + ctx.localTerm levels := by
  have work := ctx.mainWork_bound levels valid descending below
  have core := ctx.coreSize_bound
  have thresholds := G.level_count_bound levels valid descending
  unfold mainBudget at work
  omega

theorem mainWork_without_core (empty : ctx.coreSize = 0)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.mainWork levels valid ≤ 7 * ctx.vertices.length + 9 * ctx.allEdges.length +
      13 * (G.mate.toNat + 1) := by
  have work := ctx.mainWork_linear_part_bound levels valid descending below
  simpa only [localTerm, empty, ctx.coreEdges_empty empty, List.length_nil, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero] using work

/-- 値計算と同じ上限から開始する片側の主処理会計。 -/
def positiveMainWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  (ctx.atLevel G.mate G.mate_positive (Int.le_refl _)).mainWork levels valid

theorem positiveMainWork_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) :
    ctx.positiveMainWork levels valid ≤ 7 * ctx.vertices.length + 9 * ctx.allEdges.length +
      13 * (G.mate.toNat + 1) + ctx.localTerm levels :=
  (ctx.atLevel G.mate G.mate_positive (Int.le_refl _)).mainWork_linear_part_bound levels valid descending
    (fun t member => (valid t member).2)

/-- 両側の値を一度ずつ求めた後、各頂点で差を一回求める。 -/
def valueWork (otherCore : V → Bool)
    (ownLevels : List Int) (ownValid : ∀ t ∈ ownLevels, 0 < t ∧ t ≤ G.mate)
    (otherLevels : List Int) (otherValid : ∀ t ∈ otherLevels, 0 < t ∧ t ≤ G.mate) : Nat :=
  ctx.positiveMainWork ownLevels ownValid + (ctx.opposite otherCore).positiveMainWork otherLevels otherValid + ctx.vertices.length

theorem valueWork_bound (otherCore : V → Bool)
    (ownLevels : List Int) (ownValid : ∀ t ∈ ownLevels, 0 < t ∧ t ≤ G.mate)
    (ownDescending : ownLevels.Pairwise (fun a b => b < a))
    (otherLevels : List Int) (otherValid : ∀ t ∈ otherLevels, 0 < t ∧ t ≤ G.mate)
    (otherDescending : otherLevels.Pairwise (fun a b => b < a)) :
    ctx.valueWork otherCore ownLevels ownValid otherLevels otherValid ≤
      15 * ctx.vertices.length + 18 * ctx.allEdges.length + 26 * (G.mate.toNat + 1) +
      ctx.localTerm ownLevels + (ctx.opposite otherCore).localTerm otherLevels := by
  have own := ctx.positiveMainWork_bound ownLevels ownValid ownDescending
  have other := (ctx.opposite otherCore).positiveMainWork_bound otherLevels otherValid otherDescending
  change (ctx.opposite otherCore).positiveMainWork otherLevels otherValid ≤
    7 * ctx.vertices.length + 9 * ctx.allEdges.length + 13 * (G.mate.toNat + 1) +
      (ctx.opposite otherCore).localTerm otherLevels at other
  unfold valueWork
  omega

end QueueContext
end PetaProof.ThresholdGame

namespace PetaProof

universe u
variable {V : Type u}

/-- 二つの配列を計算済みとして受け取り、各頂点で差を一回だけ求める。 -/
def assembleValueRows (vertices : List V) (own other : V → Int) : List (V × Int) :=
  vertices.map (fun vertex => (vertex, own vertex - other vertex))

theorem assembleValueRows_length (vertices : List V) (own other : V → Int) :
    (assembleValueRows vertices own other).length = vertices.length := List.length_map _

theorem assembleValueRows_ids (vertices : List V) (own other : V → Int) :
    (assembleValueRows vertices own other).map Prod.fst = vertices := by
  simp [assembleValueRows, List.map_map, Function.comp_def]

end PetaProof

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

noncomputable def computedValueRows (otherCore : V → Bool) : List (V × Int) :=
  let own := ctx.computedPositiveStreamingValues
  let other := (ctx.opposite otherCore).computedPositiveStreamingValues
  assembleValueRows ctx.vertices own other

theorem computedValueRows_length (otherCore : V → Bool) :
    (ctx.computedValueRows otherCore).length = ctx.vertices.length := assembleValueRows_length _ _ _

theorem computedValueRows_unique_ids (otherCore : V → Bool) :
    ((ctx.computedValueRows otherCore).map Prod.fst).Nodup := by
  rw [computedValueRows, assembleValueRows_ids]
  exact ctx.unique

theorem computedValueRows_cover (otherCore : V → Bool) (vertex : V) :
    (vertex, ctx.computedStreamingValue otherCore vertex) ∈ ctx.computedValueRows otherCore :=
  List.mem_map.mpr ⟨vertex, ctx.covered vertex, rfl⟩

/-- 出力行の差の計算まで、既証の整数ゲーム値の保証を保つ。 -/
theorem computedValueRows_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (row : V × Int) (member : row ∈ ctx.computedValueRows otherCore) : G.ExactValue row.1 row.2 := by
  obtain ⟨vertex, _, same⟩ := List.mem_map.mp member
  subst row
  exact ctx.computedStreamingValue_exact otherCore leaves own_covers other_covers vertex

/-- 出力行と同じ生成済み閾値列を使う会計。閾値列自体の生成費用は含めない。 -/
noncomputable def computedValueWork (otherCore : V → Bool) : Nat :=
  ctx.valueWork otherCore G.setLevels (fun t member =>
    ⟨((G.setLevels_critical_iff t).mp member).1, ((G.setLevels_critical_iff t).mp member).2.1⟩)
    G.opposite.setLevels (fun t member =>
      ⟨((G.opposite.setLevels_critical_iff t).mp member).1, ((G.opposite.setLevels_critical_iff t).mp member).2.1⟩)

theorem computedValueWork_bound (otherCore : V → Bool) :
    ctx.computedValueWork otherCore ≤
      15 * ctx.vertices.length + 18 * ctx.allEdges.length + 26 * (G.mate.toNat + 1) +
      ctx.localTerm G.setLevels + (ctx.opposite otherCore).localTerm G.opposite.setLevels :=
  ctx.valueWork_bound otherCore _ _ (processedLevels_ordered _ _) _ _ (processedLevels_ordered _ _)

theorem computedRows_and_work (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    (∀ row ∈ ctx.computedValueRows otherCore, G.ExactValue row.1 row.2) ∧
      ctx.computedValueWork otherCore ≤
        15 * ctx.vertices.length + 18 * ctx.allEdges.length + 26 * (G.mate.toNat + 1) +
        ctx.localTerm G.setLevels + (ctx.opposite otherCore).localTerm G.opposite.setLevels :=
  ⟨ctx.computedValueRows_exact otherCore leaves own_covers other_covers, ctx.computedValueWork_bound otherCore⟩

end PetaProof.ThresholdGame.QueueContext
