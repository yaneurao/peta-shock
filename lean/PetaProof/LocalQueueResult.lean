import PetaProof.SafetyReturnedChoice
import PetaProof.ThresholdSetSolver

/-! 局所削除の決定的tickを有限予算まで実行し、集合版の最大安全集合へ接続する。 -/
namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def ticks (graph : Graph V E) : Nat → State V E → State V E
  | 0, state => state
  | fuel + 1, state => ticks graph fuel (tick graph state)

theorem ticks_add (graph : Graph V E) (a b : Nat) (state : State V E) :
    ticks graph (a + b) state = ticks graph b (ticks graph a state) := by
  induction a generalizing state with
  | zero => simp only [Nat.zero_add, ticks]
  | succ a ih => simpa only [Nat.succ_add, ticks] using ih (tick graph state)

theorem ticks_run (graph : Graph V E) (fuel : Nat) (state : State V E) :
    Run graph state fuel (ticks graph fuel state) := by
  induction fuel generalizing state with
  | zero => exact .done _
  | succ fuel ih => exact .next (ih _)

theorem Run.ticks_eq (graph : Graph V E) {start finish : State V E} {n : Nat}
    (run : Run graph start n finish) : ticks graph n start = finish := by
  induction run with
  | done => rfl
  | next _ ih => exact ih

theorem ticks_stopped (graph : Graph V E) (fuel : Nat) (state : State V E) (stopped : Stopped state) :
    ticks graph fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [ticks, tick, stopped.1, stopped.2] using ih

/-- 未停止なら予算が減る既証定理から、予算回の実行が停止していることを導く。 -/
theorem budget_ticks_stopped (graph : Graph V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (state : State V E) :
    Stopped (ticks graph (budget graph vertices state) state) := by
  obtain ⟨n, finish, run, stopped, bound⟩ := halts graph vertices unique covered state
  have split : budget graph vertices state = n + (budget graph vertices state - n) := by omega
  rw [split, ticks_add, run.ticks_eq graph, ticks_stopped graph _ finish stopped]
  exact stopped

end PetaProof.SafetyExecution

namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

/-- 入力から分類した局所グラフを、停止上界まで決定的に実行する。 -/
def queueResult (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) : SafetyExecution.State V E :=
  let gr := graph input vertices unique covered
  SafetyExecution.ticks gr (SafetyExecution.budget gr vertices (SafetyExecution.initial gr vertices))
    (SafetyExecution.initial gr vertices)

theorem queueResult_stopped (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) : SafetyExecution.Stopped (queueResult input vertices unique covered) :=
  SafetyExecution.budget_ticks_stopped _ vertices unique covered _

/-- 返却集合の安全性・候補内性・最大性は、実際のtick列の終点から得る。 -/
theorem queueResult_greatest (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    G.SafeSet (fun vertex => input.won vertex = true) (SafetyExecution.alive (queueResult input vertices unique covered)) ∧
      (∀ vertex, SafetyExecution.alive (queueResult input vertices unique covered) vertex → eligible input vertex = true) ∧
      ∀ kept, G.SafeSet (fun vertex => input.won vertex = true) kept →
        (∀ vertex, kept vertex → eligible input vertex = true) →
          ∀ vertex, kept vertex → SafetyExecution.alive (queueResult input vertices unique covered) vertex := by
  let gr := graph input vertices unique covered
  have stopped := queueResult_stopped input vertices unique covered
  have run := SafetyExecution.ticks_run gr
    (SafetyExecution.budget gr vertices (SafetyExecution.initial gr vertices)) (SafetyExecution.initial gr vertices)
  have result := SafetyExecution.greatest_at_halt gr vertices covered run stopped.1 stopped.2
  have model := gameModel input vertices unique covered
  refine ⟨(model.safeSet_iff gr input.indexed _ _ result.2.1).mp result.1, result.2.1, ?_⟩
  intro kept safe within
  exact result.2.2 kept ((model.safeSet_iff gr input.indexed _ kept within).mpr safe) within

/-- 局所キューで得る集合は、同期集合反復で定義したlocalResultと厳密に一致する。 -/
theorem queueResult_eq (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    SafetyExecution.alive (queueResult input vertices unique covered) =
      G.localResult vertices (fun vertex => input.core vertex = true) (fun vertex => input.won vertex = true) := by
  have result := queueResult_greatest input vertices unique covered
  have within : ∀ vertex, eligible input vertex = true ↔ input.core vertex = true ∧ ¬ input.won vertex = true := by
    intro vertex
    simp [eligible]
  funext vertex
  apply propext
  constructor
  · exact G.localResult_greatest vertices _ _ _ result.1
      (fun vertex live => (within vertex).mp (result.2.1 vertex live)) vertex
  · apply result.2.2 _ (G.localResult_safe vertices covered _ _)
    intro vertex inside
    exact (within vertex).mpr (G.iterate_subset vertices.length vertex inside)

/-- 返却した実際の指し手を使い、外側の通常FIFOへ追加する安全バッチを構成する。 -/
def queueResult_batch (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    G.SafeBatch (fun vertex => input.won vertex = true) (SafetyExecution.alive (queueResult input vertices unique covered)) :=
  returnedBatch input vertices unique covered (SafetyExecution.ticks_run _ _ _)
    (queueResult_stopped input vertices unique covered)

end PetaProof.SafetyClassification
