import PetaProof.ReverseDfsWork

/-! 構築済み王手継続グラフの両DFSに、頂点数・元辺数による上界を接続する。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (ctx : G.QueueContext E)

omit [DecidableEq V] [DecidableEq E] in
theorem incoming_rows_unique : (ctx.vertices.flatMap ctx.parents.incoming).Nodup := by
  have generic : ∀ selected : List V, selected.Nodup → (selected.flatMap ctx.parents.incoming).Nodup := by
    intro selected unique
    induction selected with
    | nil => exact List.nodup_nil
    | cons vertex rest ih =>
      have parts := List.nodup_cons.mp unique
      apply List.pairwise_append.mpr
      refine ⟨ctx.parents.unique vertex, ih parts.2, ?_⟩
      intro a first b second equal
      obtain ⟨other, member, found⟩ := List.mem_flatMap.mp second
      have firstMove := (ctx.parents.exact vertex a).mp first
      have otherMove := (ctx.parents.exact other b).mp found
      have same := Move.node.inj (firstMove.symm.trans ((congrArg ctx.indexed.move equal).trans otherMove))
      exact parts.1 (same ▸ member)
  exact generic ctx.vertices ctx.unique

omit [DecidableEq V] in
theorem incoming_total_bound : (ctx.vertices.flatMap ctx.parents.incoming).length ≤ ctx.allEdges.length :=
  DistinctWork.length_le _ _ ctx.incoming_rows_unique (fun edge _ => ctx.allEdges_contains edge)

omit [DecidableEq V] [DecidableEq E] in
theorem checkingOut_slots : (ctx.vertices.map (fun vertex => (ctx.checkingOut vertex).length)).sum =
    ctx.allEdges.length := by
  simp only [allEdges, List.length_flatMap, checkingOut, SccIndexedView.outgoing,
    SccIndexedView.ofIndexed, List.length_map]

omit [DecidableEq E] in
/-- 不許可辺とleafもnoneの枠として一度消費する第一DFSの実tick数。 -/
theorem checking_forward_run :
    ForwardDfs.ForestRun ctx.vertices ctx.checkingOut ctx.vertices ForwardDfs.initial
      (ctx.vertices.length + ctx.allEdges.length)
      (ForwardDfs.finish ctx.vertices ctx.vertices ctx.checkingOut) := by
  have run := ForwardDfs.finish_work ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut
  rw [ctx.checkingOut_slots] at run
  exact run

omit [DecidableEq V] in
theorem checkingParents_total_bound :
    (ctx.vertices.map (fun vertex => (ctx.checkingParents vertex).length)).sum ≤ ctx.allEdges.length := by
  have comparison : ∀ selected : List V,
      (selected.map (fun vertex => (ctx.checkingParents vertex).length)).sum ≤
        (selected.map (fun vertex => (ctx.parents.incoming vertex).length)).sum := by
    intro selected
    induction selected with
    | nil => exact Nat.le_refl _
    | cons vertex rest ih =>
      have row := List.length_filter_le ctx.checkingAllow (ctx.parents.incoming vertex)
      simp only [checkingParents, List.length_map, List.map_cons, List.sum_cons] at *
      omega
  have bound := ctx.incoming_total_bound
  rw [List.length_flatMap] at bound
  exact Nat.le_trans (comparison ctx.vertices) bound

def checkingReverseWork : Nat :=
  ReverseDfsWork.passWork ctx.vertices ctx.checkingParents
    (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut) ComponentNumbering.initial

omit [DecidableEq E] in
theorem checkingReverseWork_eq : ctx.checkingReverseWork = ctx.vertices.length +
    (ctx.vertices.map (fun vertex => (ctx.checkingParents vertex).length)).sum :=
  ReverseDfsWork.finish_work ctx.vertices ctx.unique ctx.covered ctx.checkingParents _
    (ForwardDfs.order_covers ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut)

theorem checkingReverseWork_bound : ctx.checkingReverseWork ≤ ctx.vertices.length + ctx.allEdges.length := by
  rw [ctx.checkingReverseWork_eq]
  have bound := ctx.checkingParents_total_bound
  omega

omit [DecidableEq E] in
theorem checking_order_length : (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut).length = ctx.vertices.length := by
  have perm := ForwardDfs.finish_perm ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut
  simpa only [ForwardDfs.order, List.length_reverse] using perm.length_eq

/-- 両根走査、第一DFSの実tick、第二DFSの実popと許可逆辺項目。
逆辺filterの不許可項目、自己辺検出、表の初期化等は含めない。 -/
def checkingDfsWork : Nat :=
  ctx.vertices.length + (ctx.vertices.length + ctx.allEdges.length) +
    (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut).length + ctx.checkingReverseWork

theorem checkingDfsWork_bound : ctx.checkingDfsWork ≤ 4 * ctx.vertices.length + 2 * ctx.allEdges.length := by
  have reverse := ctx.checkingReverseWork_bound
  unfold checkingDfsWork
  rw [ctx.checking_order_length]
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame.CoreGraphInput

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (input : CoreGraphInput G E)

/-- 証明済みの主処理と両DFSイベントだけを足す部分会計。前処理全費用ではない。 -/
def dfsMainWork : Nat :=
  input.forward.parentConstructionWork + input.prepared.1.generatedWork input.prepared.2 +
    input.prepared.1.checkingDfsWork + (input.prepared.1.opposite input.prepared.2).checkingDfsWork

theorem dfsMainWork_bound : input.dfsMainWork ≤
    27 * input.vertices.length + 34 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels := by
  have construction := input.forward.parentConstructionWork_bound
  have main := input.prepared.1.generatedWork_bound input.prepared.2
  have first := input.prepared.1.checkingDfsWork_bound
  have other := (input.prepared.1.opposite input.prepared.2).checkingDfsWork_bound
  change input.forward.parentConstructionWork ≤ 4 * input.vertices.length + 4 * input.forward.allEdges.length at construction
  change input.prepared.1.generatedWork input.prepared.2 ≤
    15 * input.vertices.length + 26 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels at main
  change input.prepared.1.checkingDfsWork ≤ 4 * input.vertices.length + 2 * input.forward.allEdges.length at first
  change (input.prepared.1.opposite input.prepared.2).checkingDfsWork ≤
    4 * input.vertices.length + 2 * input.forward.allEdges.length at other
  unfold dfsMainWork
  omega

theorem rows_and_dfs_work (leaves : G.BoundedLeaves) :
    (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) ∧
      input.dfsMainWork ≤ 27 * input.vertices.length + 34 * input.forward.allEdges.length +
        42 * (G.mate.toNat + 1) + input.prepared.1.localTerm input.prepared.1.generatedLevels +
        (input.prepared.1.opposite input.prepared.2).localTerm
          (input.prepared.1.opposite input.prepared.2).generatedLevels :=
  ⟨input.valueRows_exact leaves, input.dfsMainWork_bound⟩

end PetaProof.ThresholdGame.CoreGraphInput
