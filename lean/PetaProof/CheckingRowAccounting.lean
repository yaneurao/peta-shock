import PetaProof.ReverseVisitCharge
import PetaProof.CountedRowOps

/-! 王手継続グラフの逆辺選別・格納と自己辺検出を、生成coreの会計へ加える。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (ctx : G.QueueContext E)

def selectionProbe (vertex : V) : List V × Nat :=
  CountedRowOps.select ctx.checkingAllow ctx.indexed.source (ctx.parents.incoming vertex)

omit [DecidableEq V] [DecidableEq E] in
theorem selectionProbe_spec (vertex : V) :
    (ctx.selectionProbe vertex).1 = ctx.checkingParents vertex ∧
      (ctx.selectionProbe vertex).2 = (ctx.parents.incoming vertex).length + 3 * (ctx.checkingParents vertex).length := by
  have spec := CountedRowOps.select_spec ctx.checkingAllow ctx.indexed.source (ctx.parents.incoming vertex)
  simpa only [selectionProbe, checkingParents, List.length_map] using spec

/-- 一回の選別結果を、そのまま逆辺通知へ渡す計測付きvisit。 -/
def selectionVisit (id : Nat) (state : ReverseDfsStack.State V) : ReverseDfsStack.State V × Nat :=
  match state.pending with
  | [] => (state, 0)
  | vertex :: _ =>
    let selected := ctx.selectionProbe vertex
    (ReverseDfsStack.scan id selected.1 (ReverseDfsStack.pop state), selected.2)

omit [DecidableEq E] in
theorem selectionVisit_spec (id : Nat) (state : ReverseDfsStack.State V) :
    (ctx.selectionVisit id state).1 = ReverseDfsStack.visit id ctx.checkingParents state ∧
      (ctx.selectionVisit id state).2 =
        ReverseVisitCharge.visitCharge (fun vertex => (ctx.selectionProbe vertex).2) state := by
  cases pending : state.pending with
  | nil => exact ⟨by simp [selectionVisit, ReverseDfsStack.visit, pending],
      by simp [selectionVisit, ReverseVisitCharge.visitCharge, pending]⟩
  | cons vertex rest =>
    simp [selectionVisit, ReverseDfsStack.visit, pending, (ctx.selectionProbe_spec vertex).1,
      ReverseVisitCharge.visitCharge]

/-- 同じ第二DFSのpop列に課す選別費用。会計のために探索を追加実行する指定ではない。 -/
def selectionWork : Nat :=
  ReverseVisitCharge.passCharge ctx.vertices (fun vertex => (ctx.selectionProbe vertex).2) ctx.checkingParents
    (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut) ComponentNumbering.initial

omit [DecidableEq E] in
theorem selectionWork_eq : ctx.selectionWork =
    (ctx.vertices.map (fun vertex => (ctx.parents.incoming vertex).length)).sum +
      3 * (ctx.vertices.map (fun vertex => (ctx.checkingParents vertex).length)).sum := by
  rw [selectionWork, ReverseVisitCharge.finish_charge ctx.vertices ctx.unique ctx.covered _ _ _
    (ForwardDfs.order_covers ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut)]
  have same : ctx.vertices.map (fun vertex => (ctx.selectionProbe vertex).2) =
      ctx.vertices.map (fun vertex => (ctx.parents.incoming vertex).length + 3 * (ctx.checkingParents vertex).length) :=
    List.map_congr_left (fun vertex _ => (ctx.selectionProbe_spec vertex).2)
  rw [same, CountedRowOps.sum_linear]

theorem selectionWork_bound : ctx.selectionWork ≤ 4 * ctx.allEdges.length := by
  have raw := ctx.incoming_total_bound
  rw [List.length_flatMap] at raw
  have selected := ctx.checkingParents_total_bound
  rw [ctx.selectionWork_eq]
  omega

def selfProbe (vertex : V) : Bool × Nat :=
  CountedRowOps.any (fun edge => decide (ctx.indexed.source edge = vertex) && ctx.checkingAllow edge)
    (ctx.parents.incoming vertex)

omit [DecidableEq E] in
theorem selfProbe_spec (vertex : V) :
    (ctx.selfProbe vertex).1 = ctx.checkingSelf vertex ∧
      (ctx.selfProbe vertex).2 ≤ (ctx.parents.incoming vertex).length :=
  CountedRowOps.any_spec _ _

def chargedAggregation : LinearCycleFlags.State × Nat :=
  LinearCycleFlags.scanCharged ctx.checkingComponent ctx.selfProbe ctx.vertices
    (LinearCycleFlags.initial ctx.vertices.length)

omit [DecidableEq E] in
theorem chargedAggregation_state : ctx.chargedAggregation.1 =
    LinearCycleFlags.build ctx.vertices ctx.checkingComponent ctx.checkingSelf := by
  have spec := LinearCycleFlags.scanCharged_spec ctx.checkingComponent ctx.selfProbe ctx.vertices
    (LinearCycleFlags.initial ctx.vertices.length)
  have same : (fun vertex => (ctx.selfProbe vertex).1) = ctx.checkingSelf :=
    funext (fun vertex => (ctx.selfProbe_spec vertex).1)
  simpa only [chargedAggregation, LinearCycleFlags.build, same] using spec.1

omit [DecidableEq E] in
theorem chargedAggregation_work : ctx.chargedAggregation.2 =
    (ctx.vertices.map (fun vertex => (ctx.selfProbe vertex).2)).sum :=
  (LinearCycleFlags.scanCharged_spec ctx.checkingComponent ctx.selfProbe ctx.vertices
    (LinearCycleFlags.initial ctx.vertices.length)).2

theorem selfWork_bound : ctx.chargedAggregation.2 ≤ ctx.allEdges.length := by
  have raw := ctx.incoming_total_bound
  rw [List.length_flatMap] at raw
  have work := CountedRowOps.sum_mono ctx.vertices (fun vertex => (ctx.selfProbe vertex).2)
    (fun vertex => (ctx.parents.incoming vertex).length) (fun vertex => (ctx.selfProbe_spec vertex).2)
  rw [ctx.chargedAggregation_work]
  omega

/-- 自己辺probeを一度ずつ実行した表からも、同じ循環候補を得る。 -/
def chargedCore : V → Bool :=
  let component := ctx.checkingComponent
  let table := (LinearCycleFlags.scanCharged component ctx.selfProbe ctx.vertices
    (LinearCycleFlags.initial ctx.vertices.length)).1
  fun vertex => LinearCycleFlags.flag table (component vertex)

omit [DecidableEq E] in
theorem chargedCore_eq : ctx.chargedCore = ctx.builtCheckingCore := by
  funext vertex
  change LinearCycleFlags.flag ctx.chargedAggregation.1 (ctx.checkingComponent vertex) = _
  rw [ctx.chargedAggregation_state]
  rfl

omit [DecidableEq E] in
theorem chargedCore_correct (vertex : V) :
    ctx.chargedCore vertex = true ↔ CyclicVertex G.OpponentChecking vertex := by
  rw [ctx.chargedCore_eq]
  exact ctx.builtCheckingCore_correct vertex

/-- 両DFSに加え、逆辺選別・結果格納・自己辺検査・成分表集計を数える。
DFSの訪問表等の初期化・終了順格納などはまだ含めない。 -/
def rowDfsWork : Nat := ctx.checkingDfsWork + ctx.selectionWork + ctx.chargedAggregation.2 +
  LinearCycleFlags.aggregationWork ctx.vertices

theorem rowDfsWork_bound : ctx.rowDfsWork ≤ 10 * ctx.vertices.length + 7 * ctx.allEdges.length := by
  have dfs := ctx.checkingDfsWork_bound
  have selection := ctx.selectionWork_bound
  have self := ctx.selfWork_bound
  unfold rowDfsWork
  rw [LinearCycleFlags.aggregationWork_eq]
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame.CoreGraphInput

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (input : CoreGraphInput G E)

/-- 選別・自己辺・成分集計込みの部分会計。DFS補助表等の費用は未統合。 -/
def rowMainWork : Nat :=
  input.forward.parentConstructionWork + input.prepared.1.generatedWork input.prepared.2 +
    input.prepared.1.rowDfsWork + (input.prepared.1.opposite input.prepared.2).rowDfsWork

theorem rowMainWork_bound : input.rowMainWork ≤
    39 * input.vertices.length + 44 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels := by
  have construction := input.forward.parentConstructionWork_bound
  have main := input.prepared.1.generatedWork_bound input.prepared.2
  have first := input.prepared.1.rowDfsWork_bound
  have other := (input.prepared.1.opposite input.prepared.2).rowDfsWork_bound
  change input.forward.parentConstructionWork ≤ 4 * input.vertices.length + 4 * input.forward.allEdges.length at construction
  change input.prepared.1.generatedWork input.prepared.2 ≤
    15 * input.vertices.length + 26 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels at main
  change input.prepared.1.rowDfsWork ≤ 10 * input.vertices.length + 7 * input.forward.allEdges.length at first
  change (input.prepared.1.opposite input.prepared.2).rowDfsWork ≤
    10 * input.vertices.length + 7 * input.forward.allEdges.length at other
  unfold rowMainWork
  omega

theorem rows_and_row_work (leaves : G.BoundedLeaves) :
    (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) ∧
      input.rowMainWork ≤ 39 * input.vertices.length + 44 * input.forward.allEdges.length +
        42 * (G.mate.toNat + 1) + input.prepared.1.localTerm input.prepared.1.generatedLevels +
        (input.prepared.1.opposite input.prepared.2).localTerm
          (input.prepared.1.opposite input.prepared.2).generatedLevels :=
  ⟨input.valueRows_exact leaves, input.rowMainWork_bound⟩

end PetaProof.ThresholdGame.CoreGraphInput
