import PetaProof.QueueWorkBudget

/-!
空pop・空の局所追加・同じ辺の再通知を除いた、進捗を持つ制御操作の有限上界。
停止条件への進捗仕様を別に与えれば停止点が存在するが、C++のその仕様への対応は未証明。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

structure WorkConfiguration (V : Type u) (E : Type v) where
  state : PropagationState V E
  levelsLeft : Nat

namespace WorkConfiguration

def potential (vertices : List V) (edges : List E) (config : WorkConfiguration V E) : Nat :=
  config.state.workBudget vertices edges + config.levelsLeft

end WorkConfiguration

/-- 数えるのは制御イベント。safety内部の走査・削除や別途のSCC計算の費用は、この1歩にまとめて評価しない。 -/
inductive ProductiveStep (indexed : G.IndexedMoves E) (edges : List E) :
    WorkConfiguration V E → WorkConfiguration V E → Prop
  | notify {state levels} (edge : E) (member : edge ∈ edges) (fresh : state.notified edge = false) :
      ProductiveStep indexed edges ⟨state, levels⟩ ⟨state.notify indexed edge, levels⟩
  | pop {state levels} (nonempty : state.queue.pending ≠ []) :
      ProductiveStep indexed edges ⟨state, levels⟩ ⟨state.pop, levels⟩
  | batch {state levels} (vertices : List V) (nonempty : vertices ≠ [])
      (fresh : ∀ vertex ∈ vertices, state.queue.admitted vertex = false) :
      ProductiveStep indexed edges ⟨state, levels⟩ ⟨state.addMany vertices, levels⟩
  | advance {state levels} : ProductiveStep indexed edges ⟨state, levels + 1⟩ ⟨state, levels⟩

namespace ProductiveStep

theorem decreases (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    {before after : WorkConfiguration V E} (step : ProductiveStep indexed edges before after) :
    after.potential vertices edges < before.potential vertices edges := by
  cases step with
  | @notify state levels edge member fresh =>
    have decrease := PropagationState.notify_work indexed vertices unique covered edges edges_unique state edge member fresh
    change (state.notify indexed edge).workBudget vertices edges + levels < state.workBudget vertices edges + levels
    omega
  | @pop state levels nonempty =>
    have decrease := PropagationState.pop_work vertices edges state nonempty
    change state.pop.workBudget vertices edges + levels < state.workBudget vertices edges + levels
    omega
  | @batch state levels batch nonempty fresh =>
    have decrease := PropagationState.addMany_work vertices unique covered edges state batch nonempty fresh
    change (state.addMany batch).workBudget vertices edges + levels < state.workBudget vertices edges + levels
    omega
  | advance =>
    simp only [WorkConfiguration.potential]
    omega

omit [DecidableEq V] [DecidableEq E] in
/-- 安全な局所集合のfresh条件は、全体状態の確定フラグ対応からキュー側の新規性にもなる。 -/
theorem fresh_queue_of_batch (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : state.Invariant indexed) (vertices : List V)
    (batch : G.SafeBatch state.won (fun vertex => vertex ∈ vertices)) :
    ∀ vertex ∈ vertices, state.queue.admitted vertex = false := by
  intro vertex member
  rw [← inv.agrees]
  cases flag : (state.counters vertex).admitted with
  | false => rfl
  | true => exact False.elim (batch.fresh vertex member flag)

end ProductiveStep

/-- 連続した制御イベントの有限な列。長さは局面や経路の数ではない。 -/
inductive ProductiveRun (indexed : G.IndexedMoves E) (edges : List E) :
    WorkConfiguration V E → Nat → WorkConfiguration V E → Prop
  | done (state : WorkConfiguration V E) : ProductiveRun indexed edges state 0 state
  | step {before middle after n} : ProductiveStep indexed edges before middle →
      ProductiveRun indexed edges middle n after → ProductiveRun indexed edges before (n + 1) after

namespace ProductiveRun

theorem budget_bound (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    {before after : WorkConfiguration V E} {n : Nat} (run : ProductiveRun indexed edges before n after) :
    after.potential vertices edges + n ≤ before.potential vertices edges := by
  induction run with
  | done => exact Nat.le_refl _
  | step step _ ih =>
    have decrease := step.decreases indexed vertices unique covered edges edges_unique
    omega

theorem initial_bound (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    (levels : Nat) {after : WorkConfiguration V E} {n : Nat}
    (run : ProductiveRun indexed edges ⟨PropagationState.initial indexed, levels⟩ n after) :
    n ≤ edges.length + 2 * vertices.length + levels := by
  have bound := run.budget_bound indexed vertices unique covered edges edges_unique
  simp only [WorkConfiguration.potential, PropagationState.initial_work] at bound
  omega

end ProductiveRun

/-- 実際の制御仕様に合う操作だけを選ぶ列。allowedで通知順や閾値進行の条件を制限できる。 -/
inductive ControlledRun (indexed : G.IndexedMoves E) (edges : List E)
    (allowed : WorkConfiguration V E → WorkConfiguration V E → Prop) :
    WorkConfiguration V E → Nat → WorkConfiguration V E → Prop
  | done (state : WorkConfiguration V E) : ControlledRun indexed edges allowed state 0 state
  | step {before middle after n} : ProductiveStep indexed edges before middle → allowed before middle →
      ControlledRun indexed edges allowed middle n after → ControlledRun indexed edges allowed before (n + 1) after

theorem ControlledRun.erase (indexed : G.IndexedMoves E) (edges : List E)
    (allowed : WorkConfiguration V E → WorkConfiguration V E → Prop)
    {before after : WorkConfiguration V E} {n : Nat} (run : ControlledRun indexed edges allowed before n after) :
    ProductiveRun indexed edges before n after := by
  induction run with
  | done state => exact ProductiveRun.done state
  | step step _ _ ih => exact ProductiveRun.step step ih

/-- どの次の操作を選んでも、生産的な制御イベントだけの無限実行は存在しない。 -/
theorem no_infinite_productive_run (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    (trace : Nat → WorkConfiguration V E) : ¬ (∀ n, ProductiveStep indexed edges (trace n) (trace (n + 1))) := by
  intro steps
  have bound : ∀ n, (trace n).potential vertices edges + n ≤ (trace 0).potential vertices edges := by
    intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
      have decrease := (steps n).decreases indexed vertices unique covered edges edges_unique
      omega
  have impossible := bound ((trace 0).potential vertices edges + 1)
  omega

/-- 未停止なら上記イベントが一つ進める、という仕様を与えた場合の条件付き停止定理。 -/
theorem productive_stops (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (edges : List E) (edges_unique : edges.Nodup)
    (allowed : WorkConfiguration V E → WorkConfiguration V E → Prop) (stopped : WorkConfiguration V E → Prop)
    (progress : ∀ state, ¬ stopped state → ∃ next, ProductiveStep indexed edges state next ∧ allowed state next)
    (initial : WorkConfiguration V E) :
    ∃ n final, ControlledRun indexed edges allowed initial n final ∧ stopped final ∧ n ≤ initial.potential vertices edges := by
  classical
  have go : ∀ budget : Nat, ∀ state : WorkConfiguration V E, state.potential vertices edges = budget →
      ∃ n final, ControlledRun indexed edges allowed state n final ∧ stopped final := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
      intro state same
      by_cases done : stopped state
      · exact ⟨0, state, ControlledRun.done state, done⟩
      · obtain ⟨next, step, legal⟩ := progress state done
        have decrease := step.decreases indexed vertices unique covered edges edges_unique
        obtain ⟨n, final, run, finish⟩ := ih (next.potential vertices edges) (by omega) next rfl
        exact ⟨n + 1, final, ControlledRun.step step legal run, finish⟩
  obtain ⟨n, final, run, finish⟩ := go (initial.potential vertices edges) initial rfl
  have bound := (run.erase indexed edges allowed).budget_bound indexed vertices unique covered edges edges_unique
  exact ⟨n, final, run, finish, by omega⟩

end PetaProof.ThresholdGame
