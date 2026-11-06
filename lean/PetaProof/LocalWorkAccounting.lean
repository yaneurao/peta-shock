import PetaProof.LocalCallAccounting

/-! 局所削除の非停止tickを数え、実際の全閾値制御へ作業上界を接続する。 -/
namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- 逆辺通知または待機項目のpopを一作業とする。重複popも数える。 -/
def tickWork (state : State V E) : Nat :=
  match state.work, state.pending with
  | [], [] => 0
  | _, _ => 1

def executionWork (graph : Graph V E) : Nat → State V E → Nat
  | 0, _ => 0
  | fuel + 1, state => tickWork state + executionWork graph fuel (tick graph state)

theorem executionWork_budget (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (fuel : Nat) (state : State V E) :
    executionWork graph fuel state + budget graph vertices (ticks graph fuel state) ≤
      budget graph vertices state := by
  induction fuel generalizing state with
  | zero => simp [executionWork, ticks]
  | succ fuel ih =>
    have tailWork := ih (tick graph state)
    by_cases stopped : Stopped state
    · have zero : tickWork state = 0 := by simp [tickWork, stopped.1, stopped.2]
      have same : tick graph state = state := by simp [tick, stopped.1, stopped.2]
      simpa only [executionWork, ticks, zero, Nat.zero_add, same] using tailWork
    · have decrease := tick_budget graph vertices unique covered state stopped
      have one : tickWork state = 1 := by
        cases work : state.work with
        | cons edge rest => simp [tickWork, work]
        | nil =>
          cases pending : state.pending with
          | nil => exact False.elim (stopped ⟨work, pending⟩)
          | cons vertex rest => simp [tickWork, work, pending]
      simp only [executionWork, ticks, one]
      omega

omit [DecidableEq V] [DecidableEq E] in
theorem incoming_flat_unique (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup) :
    (vertices.flatMap graph.incoming).Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons target rest ih =>
    have parts := List.nodup_cons.mp unique
    apply List.pairwise_append.mpr
    refine ⟨graph.incoming_unique target, ih parts.2, ?_⟩
    intro a first b second same
    obtain ⟨other, member, present⟩ := List.mem_flatMap.mp second
    have ha := ((graph.incoming_spec target a).mp first).2
    have hb := ((graph.incoming_spec other b).mp present).2
    exact parts.1 ((ha.symm.trans ((congrArg graph.target same).trans hb)) ▸ member)

end PetaProof.SafetyExecution

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

/-- 候補集合から出る元辺。leafと候補外への辺も含む。 -/
def coreEdges : List E := ctx.allEdges.filter (fun edge => ctx.core (ctx.indexed.source edge))

def localGraph (state : PropagationState V E) : SafetyExecution.Graph V E :=
  SafetyClassification.graph (ctx.localInput state) ctx.vertices ctx.unique ctx.covered

omit [DecidableEq E] in
theorem local_pending_bound (state : PropagationState V E) :
    (SafetyExecution.initial (ctx.localGraph state) ctx.vertices).pending.length ≤ ctx.coreSize := by
  apply DistinctWork.length_le _ _ (ctx.unique.filter _)
  intro vertex member
  simp only [SafetyExecution.initial, List.mem_filter, Bool.and_eq_true] at member
  have active := member.2.1
  change (ctx.core vertex && !(state.counters vertex).admitted) = true at active
  simp only [Bool.and_eq_true] at active
  exact List.mem_filter.mpr ⟨member.1, active.1⟩

theorem local_incoming_bound (state : PropagationState V E) :
    (ctx.vertices.map (fun vertex => ((ctx.localGraph state).incoming vertex).length)).sum ≤
      ctx.coreEdges.length := by
  have bound := DistinctWork.length_le
    (ctx.vertices.flatMap (ctx.localGraph state).incoming) ctx.coreEdges
    (SafetyExecution.incoming_flat_unique _ _ ctx.unique) (by
      intro edge member
      obtain ⟨target, _, present⟩ := List.mem_flatMap.mp member
      have internal := (((ctx.localGraph state).incoming_spec target edge).mp present).1
      have active := (ctx.localGraph state).source_eligible _ edge internal
      change (ctx.core (ctx.indexed.source edge) && !(state.counters (ctx.indexed.source edge)).admitted) = true at active
      simp only [Bool.and_eq_true] at active
      exact List.mem_filter.mpr ⟨ctx.allEdges_contains edge, active.1⟩)
  simpa only [List.length_flatMap] using bound

theorem local_initial_budget_bound (state : PropagationState V E) :
    SafetyExecution.budget (ctx.localGraph state) ctx.vertices
      (SafetyExecution.initial (ctx.localGraph state) ctx.vertices) ≤
      ctx.coreSize + 2 * ctx.coreEdges.length := by
  have base := SafetyExecution.initial_budget_bound (ctx.localGraph state) ctx.vertices
  have pending := ctx.local_pending_bound state
  have incoming := ctx.local_incoming_bound state
  omega

/-- localStateと同じ初期状態・予算・tick列に対する作業数。 -/
def localWork (state : PropagationState V E) : Nat :=
  let graph := ctx.localGraph state
  let initial := SafetyExecution.initial graph ctx.vertices
  SafetyExecution.executionWork graph (SafetyExecution.budget graph ctx.vertices initial) initial

theorem localWork_bound (state : PropagationState V E) :
    ctx.localWork state ≤ ctx.coreSize + 2 * ctx.coreEdges.length := by
  have budget := SafetyExecution.executionWork_budget (ctx.localGraph state) ctx.vertices ctx.unique ctx.covered
    (SafetyExecution.budget (ctx.localGraph state) ctx.vertices
      (SafetyExecution.initial (ctx.localGraph state) ctx.vertices))
    (SafetyExecution.initial (ctx.localGraph state) ctx.vertices)
  have bound := ctx.local_initial_budget_bound state
  change ctx.localWork state + _ ≤ _ at budget
  omega

/-- 局所解析の内部作業を呼び出しごとに加算する。空返却の解析も含む。 -/
def settleLocalWork : Nat → PropagationState V E → Nat
  | 0, _ => 0
  | fuel + 1, state =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    ctx.localWork closed +
      if members = [] then 0 else settleLocalWork fuel (closed.addMany members)

theorem settleLocalWork_bound (fuel : Nat) (state : PropagationState V E) :
    ctx.settleLocalWork fuel state ≤
      (ctx.localCalls fuel state).length * (ctx.coreSize + 2 * ctx.coreEdges.length) := by
  induction fuel generalizing state with
  | zero => simp [settleLocalWork, localCalls]
  | succ fuel ih =>
    have first := ctx.localWork_bound (ctx.drain state)
    by_cases empty : ctx.localMembers (ctx.drain state) = []
    · simpa only [settleLocalWork, localCalls, if_pos empty, Nat.add_zero,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using first
    · have tailWork := ih ((ctx.drain state).addMany (ctx.localMembers (ctx.drain state)))
      simp only [settleLocalWork, localCalls, if_neg empty, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanLocalWork : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → PropagationState V E → Nat
  | _, _, [], _, _ => 0
  | G, ctx, t :: rest, valid, state =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    low.settleLocalWork ctx.vertices.length (ctx.prepare t positive bounded state) +
      scanLocalWork (G.retune t positive bounded) low rest
        (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)

theorem scanLocalWork_per_call (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    scanLocalWork G ctx levels valid state ≤
      (scanLocalCalls G ctx levels valid state).length * (ctx.coreSize + 2 * ctx.coreEdges.length) := by
  induction levels generalizing G state with
  | nil => simp [scanLocalWork, scanLocalCalls]
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    have first := low.settleLocalWork_bound ctx.vertices.length (ctx.prepare t positive bounded state)
    have tailWork := ih (G.retune t positive bounded) low
      (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)
    change low.settleLocalWork _ _ ≤ _ * (ctx.coreSize + 2 * ctx.coreEdges.length) at first
    change scanLocalWork _ low rest _ _ ≤ _ * (ctx.coreSize + 2 * ctx.coreEdges.length) at tailWork
    simp only [scanLocalWork, scanLocalCalls, List.length_append, Nat.add_mul]
    exact Nat.add_le_add first tailWork

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

theorem scanLocalWork_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    scanLocalWork G ctx levels valid state ≤
      (ctx.coreSize + levels.length) * (ctx.coreSize + 2 * ctx.coreEdges.length) :=
  Nat.le_trans (scanLocalWork_per_call G ctx levels valid state)
    (Nat.mul_le_mul_right _ (ctx.scanLocalCalls_bound levels valid state))

/-- 通常pop・元辺通知と局所削除の内部tickを合算。分類や列挙はまだ含めない。 -/
def propagationWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  ctx.ordinaryWork levels valid + scanLocalWork G ctx levels valid ctx.seeded

theorem propagationWork_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.propagationWork levels valid ≤ ctx.vertices.length + ctx.allEdges.length +
      (ctx.coreSize + levels.length) * (ctx.coreSize + 2 * ctx.coreEdges.length) :=
  Nat.add_le_add (ctx.ordinaryWork_bound levels valid descending below)
    (ctx.scanLocalWork_bound levels valid ctx.seeded)

end QueueContext
end PetaProof.ThresholdGame
