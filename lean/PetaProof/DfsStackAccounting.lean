import PetaProof.ForwardFrameAccounting

/-! 両DFSのスタック操作を、同じ実行上の初回発見・書込・popへ対応させる。 -/
namespace PetaProof.ReverseDfsStores

universe u
variable {V : Type u} [DecidableEq V]

theorem push_stack_growth (id : Nat) (state : ReverseDfsStack.State V) (vertex : V) :
    (ReverseDfsStack.push id state vertex).pending.length = state.pending.length + pushStores state vertex := by
  cases found : state.result vertex <;> simp [ReverseDfsStack.push, pushStores, found]

omit [DecidableEq V] in
theorem pop_stack_shrink (state : ReverseDfsStack.State V) (active : state.pending ≠ []) :
    (ReverseDfsStack.pop state).pending.length + 1 = state.pending.length := by
  cases pending : state.pending with
  | nil => exact False.elim (active pending)
  | cons vertex rest => simp [ReverseDfsStack.pop, pending]

end PetaProof.ReverseDfsStores

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (ctx : G.QueueContext E)

def forwardFrameWork : Nat :=
  ForwardFrameAccounting.frameWork ctx.vertices ctx.checkingOut ctx.vertices

omit [DecidableEq E] in
theorem forwardFrameWork_eq : ctx.forwardFrameWork = 4 * ctx.vertices.length + 4 * ctx.allEdges.length := by
  have work := ForwardFrameAccounting.finish_frame_work ctx.vertices ctx.unique ctx.covered ctx.checkingOut ctx.vertices ctx.covered
  rw [ctx.checkingOut_slots] at work
  exact work

omit [DecidableEq E] in
theorem forward_cursor_updates :
    ForwardFrameAccounting.forestTrims ctx.vertices ctx.checkingOut ctx.vertices ForwardDfs.initial = ctx.allEdges.length := by
  have trims := ForwardFrameAccounting.finish_trims ctx.vertices ctx.unique ctx.covered ctx.checkingOut ctx.vertices ctx.covered
  rw [ctx.checkingOut_slots] at trims
  exact trims

def reverseStackPops : Nat :=
  ReverseVisitCharge.passCharge ctx.vertices (fun _ => 1) ctx.checkingParents
    (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut) ComponentNumbering.initial

omit [DecidableEq E] in
theorem reverseStackPops_eq : ctx.reverseStackPops = ctx.vertices.length := by
  rw [reverseStackPops, ReverseVisitCharge.finish_charge ctx.vertices ctx.unique ctx.covered _ _ _
    (ForwardDfs.order_covers ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut)]
  have generic : ∀ selected : List V, (selected.map (fun _ => 1)).sum = selected.length := by
    intro selected
    induction selected with
    | nil => rfl
    | cons vertex rest ih => simp [ih, Nat.add_comm]
  exact generic ctx.vertices

/-- push・pop・非空pop時の先頭参照を数える。番号書込は既存のstorageWorkで別に数える。 -/
def reverseStackWork : Nat := ctx.reverseStores.1 + 2 * ctx.reverseStackPops

omit [DecidableEq E] in
theorem reverseStackWork_eq : ctx.reverseStackWork = 3 * ctx.vertices.length := by
  have stores := ctx.reverseStores_bounds
  unfold reverseStackWork
  rw [ctx.reverseStackPops_eq]
  omega

omit [DecidableEq E] in
theorem forward_stack_bound (state : ForwardDfs.State V) (valid : ForwardDfs.Invariant state) :
    state.stack.length ≤ ctx.vertices.length := by
  have bound := DistinctWork.length_le state.total ctx.vertices valid.unique (fun vertex _ => ctx.covered vertex)
  simp only [ForwardDfs.State.total, ForwardDfs.State.active, List.length_append, List.length_map] at bound
  omega

omit [DecidableEq E] in
theorem reverse_stack_bound (id : Nat) (state : ReverseDfsStack.State V) (valid : ReverseDfsStack.Invariant id state) :
    state.pending.length ≤ ctx.vertices.length := by
  have bound := ReverseDfsStack.total_bound ctx.vertices ctx.unique ctx.covered id state valid
  simp only [ReverseDfsStack.State.total, List.length_append] at bound
  omega

omit [DecidableEq E] in
theorem forward_push_room (state : ForwardDfs.State V) (valid : ForwardDfs.Invariant state)
    (vertex : V) (fresh : state.seen vertex = false) : state.stack.length < ctx.vertices.length := by
  have next := ctx.forward_stack_bound (ForwardDfs.discover ctx.checkingOut state vertex)
    (ForwardDfs.discover_preserves ctx.checkingOut state valid vertex)
  simp only [ForwardDfs.discover, fresh, Bool.false_eq_true, ite_false, List.length_cons] at next
  omega

omit [DecidableEq E] in
theorem reverse_push_room (id : Nat) (state : ReverseDfsStack.State V)
    (valid : ReverseDfsStack.Invariant id state) (vertex : V) (fresh : state.result vertex = none) :
    state.pending.length < ctx.vertices.length := by
  have next := ctx.reverse_stack_bound id (ReverseDfsStack.push id state vertex)
    (ReverseDfsStack.push_preserves id state valid vertex)
  simp only [ReverseDfsStack.push, fresh, List.length_cons] at next
  omega

/-- 第一DFS用フレーム表と第二DFS用頂点表を長さNで先に初期化する費用。 -/
def stackInitializationWork : Nat :=
  (Array.replicate ctx.vertices.length (none : Option (ForwardDfs.Frame V))).size +
    (Array.replicate ctx.vertices.length (none : Option V)).size

omit [DecidableEq V] [DecidableEq E] in
theorem stackInitializationWork_eq : ctx.stackInitializationWork = 2 * ctx.vertices.length := by
  simp only [stackInitializationWork, Array.size_replicate]
  omega

def stackDfsWork : Nat := ctx.generatedDfsWork + ctx.forwardFrameWork + ctx.reverseStackWork + ctx.stackInitializationWork

theorem stackDfsWork_bound : ctx.stackDfsWork ≤ 28 * ctx.vertices.length + 13 * ctx.allEdges.length := by
  have generated := ctx.generatedDfsWork_bound
  unfold stackDfsWork
  rw [ctx.forwardFrameWork_eq, ctx.reverseStackWork_eq, ctx.stackInitializationWork_eq]
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame.CoreGraphInput

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (input : CoreGraphInput G E)

def stackMainWork : Nat :=
  input.forward.parentConstructionWork + input.prepared.1.generatedWork input.prepared.2 +
    input.prepared.1.stackDfsWork + (input.prepared.1.opposite input.prepared.2).stackDfsWork

theorem stackMainWork_bound : input.stackMainWork ≤
    75 * input.vertices.length + 56 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels := by
  have construction := input.forward.parentConstructionWork_bound
  have main := input.prepared.1.generatedWork_bound input.prepared.2
  have first := input.prepared.1.stackDfsWork_bound
  have other := (input.prepared.1.opposite input.prepared.2).stackDfsWork_bound
  change input.forward.parentConstructionWork ≤ 4 * input.vertices.length + 4 * input.forward.allEdges.length at construction
  change input.prepared.1.generatedWork input.prepared.2 ≤
    15 * input.vertices.length + 26 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels at main
  change input.prepared.1.stackDfsWork ≤ 28 * input.vertices.length + 13 * input.forward.allEdges.length at first
  change (input.prepared.1.opposite input.prepared.2).stackDfsWork ≤
    28 * input.vertices.length + 13 * input.forward.allEdges.length at other
  unfold stackMainWork
  omega

theorem rows_and_stack_work (leaves : G.BoundedLeaves) :
    (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) ∧
      input.stackMainWork ≤ 75 * input.vertices.length + 56 * input.forward.allEdges.length +
        42 * (G.mate.toNat + 1) + input.prepared.1.localTerm input.prepared.1.generatedLevels +
        (input.prepared.1.opposite input.prepared.2).localTerm
          (input.prepared.1.opposite input.prepared.2).generatedLevels :=
  ⟨input.valueRows_exact leaves, input.stackMainWork_bound⟩

end PetaProof.ThresholdGame.CoreGraphInput
