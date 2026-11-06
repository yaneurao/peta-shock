import PetaProof.LocalWorkAccounting
import PetaProof.SafetyInitializedRun

/-! coreだけの初期化・一回の出辺分類・返却集合列挙を、既存の局所解へ接続する。 -/
namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
/-- core外ではinitVertexは何もしないので、事前に作ったcore列だけで初期化できる。 -/
theorem initializeRows_core (input : Input G E) (vertices : List V) (arrays : InitArrays V E) :
    initializeRows input (vertices.filter input.core) arrays = initializeRows input vertices arrays := by
  induction vertices generalizing arrays with
  | nil => rfl
  | cons vertex rest ih =>
    cases core : input.core vertex <;>
      simp [List.filter_cons, core, initializeRows, initVertex, eligible, ih]

omit [DecidableEq V] [DecidableEq E] in
theorem allInternal_core (input : Input G E) (vertices : List V) :
    allInternal input (vertices.filter input.core) = allInternal input vertices := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
    simp only [allInternal] at ih
    cases core : input.core vertex <;>
      simp [allInternal, List.filter_cons, core, internalEdges, eligible, ih]

def activeOutgoing (input : Input G E) (vertex : V) : List E :=
  if eligible input vertex then input.indexed.outgoing vertex else []

/-- initVertexがinitRowへ渡す出辺のログ。一辺処理はinitEdgeそのものである。 -/
def preparationEdges (input : Input G E) (vertices : List V) : List E :=
  vertices.flatMap (activeOutgoing input)

omit [DecidableEq V] [DecidableEq E] in
theorem mem_preparationEdges (input : Input G E) (vertices : List V) (edge : E)
    (member : edge ∈ preparationEdges input vertices) :
    ∃ vertex ∈ vertices, eligible input vertex = true ∧ edge ∈ input.indexed.outgoing vertex := by
  obtain ⟨vertex, present, inside⟩ := List.mem_flatMap.mp member
  refine ⟨vertex, present, ?_⟩
  cases active : eligible input vertex <;> simp_all [activeOutgoing]

omit [DecidableEq V] [DecidableEq E] in
theorem preparationEdges_unique (input : Input G E) (vertices : List V) (unique : vertices.Nodup) :
    (preparationEdges input vertices).Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons vertex rest ih =>
    have parts := List.nodup_cons.mp unique
    change (activeOutgoing input vertex ++ preparationEdges input rest).Nodup
    apply List.pairwise_append.mpr
    refine ⟨?_, ih parts.2, ?_⟩
    · cases active : eligible input vertex with
      | false => simp [activeOutgoing, active]
      | true => simpa only [activeOutgoing, active, ite_true] using input.indexed.unique vertex
    · intro a first b second same
      obtain ⟨other, member, _, internal⟩ := mem_preparationEdges input rest b second
      have first_mem : a ∈ input.indexed.outgoing vertex := by
        cases active : eligible input vertex <;> simp_all [activeOutgoing]
      have equal : vertex = other := (input.indexed.source_of_mem vertex a first_mem).symm.trans
        ((congrArg input.indexed.source same).trans (input.indexed.source_of_mem other b internal))
      exact parts.1 (equal ▸ member)

end PetaProof.SafetyClassification

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

/-- この一覧は閾値走査の前に一回だけ作る。各呼び出しで全頂点をfilterし直す必要はない。 -/
def coreVertices : List V := ctx.vertices.filter ctx.core

omit [DecidableEq E] in
theorem coreInitialization_eq (state : PropagationState V E) :
    SafetyClassification.initializeRows (ctx.localInput state) ctx.coreVertices SafetyClassification.emptyArrays =
      SafetyClassification.initializeRows (ctx.localInput state) ctx.vertices SafetyClassification.emptyArrays :=
  SafetyClassification.initializeRows_core _ _ _

omit [DecidableEq E] in
theorem coreExecution_eq (state : PropagationState V E) :
    SafetyClassification.executionOf (ctx.localInput state)
      (SafetyClassification.initializeRows (ctx.localInput state) ctx.coreVertices SafetyClassification.emptyArrays) =
      SafetyExecution.initial (ctx.localGraph state) ctx.vertices := by
  rw [ctx.coreInitialization_eq]
  exact SafetyClassification.initialize_state_eq _ _ ctx.unique ctx.covered

omit [DecidableEq V] [DecidableEq E] in
theorem coreInternal_eq (state : PropagationState V E) :
    SafetyClassification.allInternal (ctx.localInput state) ctx.coreVertices =
      SafetyClassification.allInternal (ctx.localInput state) ctx.vertices :=
  SafetyClassification.allInternal_core _ _

/-- 返却列の順序も含め、coreだけの列挙は全頂点の列挙と一致する。 -/
theorem coreLocalMembers_eq (state : PropagationState V E) :
    ctx.coreVertices.filter (fun vertex => !(ctx.localState state).deleted vertex) = ctx.localMembers state := by
  have restrict : ∀ vertex, (!(ctx.localState state).deleted vertex) = true → ctx.core vertex = true := by
    intro vertex live
    apply ctx.localMembers_core state vertex
    simp only [localMembers, List.mem_filter, ctx.covered vertex, true_and]
    exact live
  unfold coreVertices localMembers
  rw [List.filter_filter]
  congr 1
  funext vertex
  cases core : ctx.core vertex <;> cases live : !(ctx.localState state).deleted vertex <;>
    simp_all

def classificationEdges (state : PropagationState V E) : List E :=
  SafetyClassification.preparationEdges (ctx.localInput state) ctx.coreVertices

omit [DecidableEq V] in
theorem classificationEdges_bound (state : PropagationState V E) :
    (ctx.classificationEdges state).length ≤ ctx.coreEdges.length := by
  apply DistinctWork.length_le _ _
    (SafetyClassification.preparationEdges_unique _ _ (ctx.unique.filter _))
  intro edge member
  obtain ⟨vertex, _, active, present⟩ := SafetyClassification.mem_preparationEdges _ _ edge member
  change (ctx.core vertex && !(state.counters vertex).admitted) = true at active
  simp only [Bool.and_eq_true] at active
  exact List.mem_filter.mpr ⟨ctx.allEdges_contains edge,
    (ctx.indexed.source_of_mem vertex edge present) ▸ active.1⟩

omit [DecidableEq V] in
theorem registrations_bound (state : PropagationState V E) :
    (SafetyClassification.allInternal (ctx.localInput state) ctx.coreVertices).length ≤ ctx.coreEdges.length := by
  rw [ctx.coreInternal_eq state]
  apply DistinctWork.length_le _ _ (SafetyClassification.allInternal_unique _ _ ctx.unique)
  intro edge member
  have internal := (SafetyClassification.mem_allInternal (ctx.localInput state) ctx.vertices ctx.covered edge).mp member
  have active := ((SafetyClassification.mem_internal _ _ edge).mp internal).1
  change (ctx.core (ctx.indexed.source edge) && !(state.counters (ctx.indexed.source edge)).admitted) = true at active
  simp only [Bool.and_eq_true] at active
  exact List.mem_filter.mpr ⟨ctx.allEdges_contains edge, active.1⟩

/-- 一回のcore行初期化・出辺分類・逆辺登録・削除・core返却走査のイベント数。 -/
def preparedLocalWork (state : PropagationState V E) : Nat :=
  ctx.coreVertices.length + (ctx.classificationEdges state).length +
    (SafetyClassification.allInternal (ctx.localInput state) ctx.coreVertices).length +
    ctx.localWork state + ctx.coreVertices.length

theorem preparedLocalWork_bound (state : PropagationState V E) :
    ctx.preparedLocalWork state ≤ 3 * ctx.coreSize + 4 * ctx.coreEdges.length := by
  have edges := ctx.classificationEdges_bound state
  have registrations := ctx.registrations_bound state
  have deletion := ctx.localWork_bound state
  have vertices : ctx.coreVertices.length = ctx.coreSize := rfl
  unfold preparedLocalWork
  omega

def settlePreparedWork : Nat → PropagationState V E → Nat
  | 0, _ => 0
  | fuel + 1, state =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    ctx.preparedLocalWork closed +
      if members = [] then 0 else settlePreparedWork fuel (closed.addMany members)

theorem settlePreparedWork_bound (fuel : Nat) (state : PropagationState V E) :
    ctx.settlePreparedWork fuel state ≤
      (ctx.localCalls fuel state).length * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) := by
  induction fuel generalizing state with
  | zero => simp [settlePreparedWork, localCalls]
  | succ fuel ih =>
    have first := ctx.preparedLocalWork_bound (ctx.drain state)
    by_cases empty : ctx.localMembers (ctx.drain state) = []
    · simpa only [settlePreparedWork, localCalls, if_pos empty, Nat.add_zero,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using first
    · have tailWork := ih ((ctx.drain state).addMany (ctx.localMembers (ctx.drain state)))
      simp only [settlePreparedWork, localCalls, if_neg empty, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanPreparedWork : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → PropagationState V E → Nat
  | _, _, [], _, _ => 0
  | G, ctx, t :: rest, valid, state =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    low.settlePreparedWork ctx.vertices.length (ctx.prepare t positive bounded state) +
      scanPreparedWork (G.retune t positive bounded) low rest
        (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)

theorem scanPreparedWork_per_call (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    scanPreparedWork G ctx levels valid state ≤
      (scanLocalCalls G ctx levels valid state).length * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) := by
  induction levels generalizing G state with
  | nil => simp [scanPreparedWork, scanLocalCalls]
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    have first := low.settlePreparedWork_bound ctx.vertices.length (ctx.prepare t positive bounded state)
    have tailWork := ih (G.retune t positive bounded) low
      (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)
    change low.settlePreparedWork _ _ ≤ _ * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) at first
    change scanPreparedWork _ low rest _ _ ≤ _ * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) at tailWork
    simp only [scanPreparedWork, scanLocalCalls, List.length_append, Nat.add_mul]
    exact Nat.add_le_add first tailWork

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

theorem scanPreparedWork_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    scanPreparedWork G ctx levels valid state ≤
      (ctx.coreSize + levels.length) * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) :=
  Nat.le_trans (scanPreparedWork_per_call G ctx levels valid state)
    (Nat.mul_le_mul_right _ (ctx.scanLocalCalls_bound levels valid state))

/-- 通常伝播・局所準備と削除・非空返却集合の一括追加を合わせたイベント会計。 -/
def preparedPropagationWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  ctx.ordinaryWork levels valid + scanPreparedWork G ctx levels valid ctx.seeded +
    (scanLocalCalls G ctx levels valid ctx.seeded).flatten.length

theorem preparedPropagationWork_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.preparedPropagationWork levels valid ≤ ctx.vertices.length + ctx.allEdges.length + ctx.coreSize +
      (ctx.coreSize + levels.length) * (3 * ctx.coreSize + 4 * ctx.coreEdges.length) := by
  have normal := ctx.ordinaryWork_bound levels valid descending below
  have prepared := ctx.scanPreparedWork_bound levels valid ctx.seeded
  have insertion := ctx.scanLocalCalls_vertices_bound levels valid ctx.seeded
  unfold preparedPropagationWork
  omega

end QueueContext
end PetaProof.ThresholdGame
