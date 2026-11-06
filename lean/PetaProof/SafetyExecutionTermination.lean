import PetaProof.SafetyExecutionSemantics

namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def budget (graph : Graph V E) (vertices : List V) (state : State V E) : Nat :=
  state.pending.length + 2 * (DeletionQueue.credit (fun vertex => (graph.incoming vertex).length)
    state.deleted vertices + state.work.length)

def Stopped (state : State V E) : Prop := state.work = [] ∧ state.pending = []

theorem notify_budget (graph : Graph V E) (vertices : List V) (state : State V E)
    (edge : E) (rest : List E) (work : state.work = edge :: rest) :
    budget graph vertices (notify graph state edge rest) + 1 ≤ budget graph vertices state := by
  dsimp only [notify]
  split
  · simp only [budget, work, List.length_cons]
    omega
  · simp only [budget, work, List.length_cons]
    split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega

omit [DecidableEq E] in
theorem pop_budget (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (state : State V E) (vertex : V) (rest : List V)
    (work : state.work = []) (pending : state.pending = vertex :: rest) :
    budget graph vertices (pop graph state vertex rest) + 1 ≤ budget graph vertices state := by
  cases deleted : state.deleted vertex with
  | true =>
    simp only [pop, deleted, ite_true, budget, pending, List.length_cons]
    omega
  | false =>
    have decrement := DeletionQueue.credit_mark (fun v => (graph.incoming v).length)
      state.deleted vertex vertices unique (covered vertex) deleted
    dsimp only at decrement
    simp only [pop, deleted, Bool.false_eq_true, ite_false, budget, pending, work, List.length_cons, List.length_nil]
    omega

theorem tick_budget (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (state : State V E) (running : ¬ Stopped state) :
    budget graph vertices (tick graph state) + 1 ≤ budget graph vertices state := by
  cases work : state.work with
  | cons edge rest => simpa only [tick, work] using notify_budget graph vertices state edge rest work
  | nil =>
    cases pending : state.pending with
    | nil => exact False.elim (running ⟨work, pending⟩)
    | cons vertex rest =>
      simpa only [tick, work, pending] using pop_budget graph vertices unique covered state vertex rest work pending

/-- tickは具体的な決定的操作。未停止なら進めるという外部仕様を要求せず、停止実行を構成する。 -/
theorem halts (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (start : State V E) :
    ∃ n finish, Run graph start n finish ∧ Stopped finish ∧ n ≤ budget graph vertices start := by
  suffices ∀ b state, budget graph vertices state = b →
      ∃ n finish, Run graph state n finish ∧ Stopped finish ∧ n ≤ budget graph vertices state by
    exact this _ start rfl
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro state same
    by_cases stopped : Stopped state
    · exact ⟨0, state, Run.done state, stopped, Nat.zero_le _⟩
    · have decrease := tick_budget graph vertices unique covered state stopped
      obtain ⟨n, finish, tail, ended, bound⟩ := ih (budget graph vertices (tick graph state)) (by omega) _ rfl
      exact ⟨n + 1, finish, Run.next tail, ended, by omega⟩

omit [DecidableEq V] [DecidableEq E] in
theorem initial_budget_bound (graph : Graph V E) (vertices : List V) :
    budget graph vertices (initial graph vertices) ≤
      (initial graph vertices).pending.length + 2 * (vertices.map (fun v => (graph.incoming v).length)).sum := by
  have bound := DeletionQueue.credit_le_total vertices (fun v => (graph.incoming v).length)
    (initial graph vertices).deleted
  simp only [budget, initial, List.length_nil, Nat.add_zero] at *
  omega

/-- 局所グラフの初期分類から、有限な実行と最大安全集合を同時に得る。 -/
theorem solves (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    ∃ n finish, Run graph (initial graph vertices) n finish ∧ Stopped finish ∧
      n ≤ (initial graph vertices).pending.length +
        2 * (vertices.map (fun v => (graph.incoming v).length)).sum ∧
      graph.SafeSet (alive finish) ∧ (∀ vertex, alive finish vertex → graph.eligible vertex = true) ∧
      ∀ kept, graph.SafeSet kept → (∀ vertex, kept vertex → graph.eligible vertex = true) →
        ∀ vertex, kept vertex → alive finish vertex := by
  obtain ⟨n, finish, run, stopped, bound⟩ := halts graph vertices unique covered (initial graph vertices)
  have initial_bound := initial_budget_bound graph vertices
  have greatest := greatest_at_halt graph vertices covered run stopped.1 stopped.2
  exact ⟨n, finish, run, stopped, by omega, greatest⟩

end PetaProof.SafetyExecution
