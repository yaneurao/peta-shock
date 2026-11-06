import PetaProof.FixedOutputBuffer

/-! DFS補助表の初期化、成功時の書込、固定長出力表を主値計算の会計へ接続する。 -/
namespace PetaProof.DfsStorage

universe u

structure Buffers (V : Type u) where
  seen : Array Bool
  labels : Array (Option Nat)
  finished : FixedOutputBuffer.Buffer V
  representatives : FixedOutputBuffer.Buffer V

def initial (V : Type u) (n : Nat) : Buffers V :=
  ⟨Array.replicate n false, Array.replicate n none, FixedOutputBuffer.initial n, FixedOutputBuffer.initial n⟩

theorem initial_sizes (V : Type u) (n : Nat) :
    (initial V n).seen.size = n ∧ (initial V n).labels.size = n ∧
      (initial V n).finished.data.size = n ∧ (initial V n).representatives.data.size = n := by
  simp [initial, FixedOutputBuffer.initial]

theorem initial_entries (V : Type u) (n index : Nat) (inside : index < n) :
    (initial V n).seen[index]? = some false ∧ (initial V n).labels[index]? = some none ∧
      (initial V n).finished.data[index]? = some none ∧
      (initial V n).representatives.data[index]? = some none ∧
      (initial V n).finished.used = 0 ∧ (initial V n).representatives.used = 0 := by
  simp [initial, FixedOutputBuffer.initial, Array.getElem?_replicate, inside]

def initializationWork (V : Type u) (n : Nat) : Nat :=
  let buffers := initial V n
  buffers.seen.size + buffers.labels.size + buffers.finished.data.size + buffers.representatives.data.size

theorem initializationWork_eq (V : Type u) (n : Nat) : initializationWork V n = 4 * n := by
  simp only [initializationWork, (initial_sizes V n).1, (initial_sizes V n).2.1,
    (initial_sizes V n).2.2.1, (initial_sizes V n).2.2.2]
  omega

end PetaProof.DfsStorage

namespace PetaProof.ForwardDfsStores

universe u
variable {V : Type u} [DecidableEq V]

theorem finished_prefix_bound (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (state : ForwardDfs.State V) (valid : ForwardDfs.Invariant state) : state.finished.length ≤ vertices.length :=
  DistinctWork.length_le _ _ (List.pairwise_append.mp valid.unique).1 (fun vertex _ => covered vertex)

theorem finishing_room (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (state : ForwardDfs.State V) (valid : ForwardDfs.Invariant state) (active : state.stack ≠ []) :
    state.finished.length < vertices.length := by
  have total := DistinctWork.length_le state.total vertices valid.unique (fun vertex _ => covered vertex)
  have positive : 0 < state.stack.length := List.length_pos_iff.mpr active
  simp only [ForwardDfs.State.total, ForwardDfs.State.active, List.length_append, List.length_map] at total
  omega

end PetaProof.ForwardDfsStores

namespace PetaProof.ReverseDfsStores

universe u
variable {V : Type u} [DecidableEq V]

theorem representative_room (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state)
    (root : V) (fresh : state.result root = none) : state.roots.length < vertices.length := by
  have next := ComponentNumbering.step_preserves vertices.length parents state valid root
  have bound := ComponentNumbering.roots_bound vertices unique covered _ next
  simp only [ComponentNumbering.step, if_pos fresh, List.length_append, List.length_singleton] at bound
  omega

end PetaProof.ReverseDfsStores

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (ctx : G.QueueContext E)

def forwardStores : Nat × Nat :=
  ForwardDfsStores.forestStores ctx.vertices ctx.checkingOut ctx.vertices ForwardDfs.initial

omit [DecidableEq E] in
theorem forwardStores_eq : ctx.forwardStores = (ctx.vertices.length, ctx.vertices.length) :=
  ForwardDfsStores.finish_stores ctx.vertices ctx.unique ctx.covered ctx.checkingOut ctx.vertices ctx.covered

def reverseStores : Nat × Nat :=
  ReverseDfsStores.passStores ctx.vertices ctx.checkingParents
    (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut) ComponentNumbering.initial

omit [DecidableEq E] in
theorem reverseStores_bounds : ctx.reverseStores.1 = ctx.vertices.length ∧ ctx.reverseStores.2 ≤ ctx.vertices.length := by
  have stores := ReverseDfsStores.finish_stores ctx.vertices ctx.unique ctx.covered ctx.checkingParents _
    (ForwardDfs.order_covers ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut)
  exact ⟨stores.1, stores.2.2⟩

def finishingSequence : List V := (ForwardDfs.finish ctx.vertices ctx.vertices ctx.checkingOut).finished

omit [DecidableEq E] in
theorem finishingSequence_length : ctx.finishingSequence.length = ctx.vertices.length :=
  (ForwardDfs.finish_perm ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut).length_eq

def representativeSequence : List V :=
  (ComponentNumbering.finish ctx.vertices (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut) ctx.checkingParents).roots

omit [DecidableEq E] in
theorem representativeSequence_length : ctx.representativeSequence.length ≤ ctx.vertices.length :=
  ComponentNumbering.roots_bound ctx.vertices ctx.unique ctx.covered _ (ComponentNumbering.finish_invariant _ _ _)

omit [DecidableEq E] in
theorem fixed_outputs_safe :
    FixedOutputBuffer.SafeFill ctx.finishingSequence (FixedOutputBuffer.initial ctx.vertices.length) ∧
      FixedOutputBuffer.SafeFill ctx.representativeSequence (FixedOutputBuffer.initial ctx.vertices.length) :=
  ⟨(FixedOutputBuffer.output_safe _ _ (Nat.le_of_eq ctx.finishingSequence_length)).1,
    (FixedOutputBuffer.output_safe _ _ ctx.representativeSequence_length).1⟩

omit [DecidableEq E] in
/-- 末尾からのN回の直接読出しは、別の逆順列を構築しなくても同じ根を返す。 -/
theorem finishing_reverse_read (index : Nat) (inside : index < ctx.vertices.length) :
    (FixedOutputBuffer.fill ctx.finishingSequence (FixedOutputBuffer.initial ctx.vertices.length)).data[ctx.vertices.length - 1 - index]? =
      (ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut)[index]?.map some := by
  have length := ctx.finishingSequence_length
  have bounded : ctx.vertices.length - 1 - index < ctx.finishingSequence.length := by omega
  have enough : (FixedOutputBuffer.initial ctx.vertices.length : FixedOutputBuffer.Buffer V).used +
      ctx.finishingSequence.length ≤ (FixedOutputBuffer.initial ctx.vertices.length : FixedOutputBuffer.Buffer V).data.size := by
    simp [FixedOutputBuffer.initial, length]
  have read := FixedOutputBuffer.fill_lookup ctx.finishingSequence (FixedOutputBuffer.initial ctx.vertices.length)
    enough (ctx.vertices.length - 1 - index) bounded
  change _ = (ctx.finishingSequence.reverse)[index]?.map some
  rw [List.getElem?_reverse (by omega)]
  simpa only [FixedOutputBuffer.initial, Nat.zero_add, length] using read

/-- 4表の初期化、訪問・終了・番号・代表の書込と終了順の逆順読出し。 -/
def storageWork : Nat := DfsStorage.initializationWork V ctx.vertices.length +
  ctx.forwardStores.1 + ctx.forwardStores.2 + ctx.reverseStores.1 + ctx.reverseStores.2 + ctx.finishingSequence.length

omit [DecidableEq E] in
theorem storageWork_bound : ctx.storageWork ≤ 9 * ctx.vertices.length := by
  have reverse := ctx.reverseStores_bounds
  unfold storageWork
  rw [DfsStorage.initializationWork_eq, ctx.forwardStores_eq, ctx.finishingSequence_length]
  dsimp only
  omega

/-- rowDfsWorkの対象へ、補助表と出力格納の費用を追加する。 -/
def storedDfsWork : Nat := ctx.rowDfsWork + ctx.storageWork

theorem storedDfsWork_bound : ctx.storedDfsWork ≤ 19 * ctx.vertices.length + 7 * ctx.allEdges.length := by
  have rows := ctx.rowDfsWork_bound
  have storage := ctx.storageWork_bound
  unfold storedDfsWork
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame.CoreGraphInput

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (input : CoreGraphInput G E)

/-- 補助表・出力格納まで加えた会計。識別子の表参照は定数時間とする。 -/
def storedMainWork : Nat :=
  input.forward.parentConstructionWork + input.prepared.1.generatedWork input.prepared.2 +
    input.prepared.1.storedDfsWork + (input.prepared.1.opposite input.prepared.2).storedDfsWork

theorem storedMainWork_bound : input.storedMainWork ≤
    57 * input.vertices.length + 44 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels := by
  have construction := input.forward.parentConstructionWork_bound
  have main := input.prepared.1.generatedWork_bound input.prepared.2
  have first := input.prepared.1.storedDfsWork_bound
  have other := (input.prepared.1.opposite input.prepared.2).storedDfsWork_bound
  change input.forward.parentConstructionWork ≤ 4 * input.vertices.length + 4 * input.forward.allEdges.length at construction
  change input.prepared.1.generatedWork input.prepared.2 ≤
    15 * input.vertices.length + 26 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels at main
  change input.prepared.1.storedDfsWork ≤ 19 * input.vertices.length + 7 * input.forward.allEdges.length at first
  change (input.prepared.1.opposite input.prepared.2).storedDfsWork ≤
    19 * input.vertices.length + 7 * input.forward.allEdges.length at other
  unfold storedMainWork
  omega

theorem rows_and_stored_work (leaves : G.BoundedLeaves) :
    (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) ∧
      input.storedMainWork ≤ 57 * input.vertices.length + 44 * input.forward.allEdges.length +
        42 * (G.mate.toNat + 1) + input.prepared.1.localTerm input.prepared.1.generatedLevels +
        (input.prepared.1.opposite input.prepared.2).localTerm
          (input.prepared.1.opposite input.prepared.2).generatedLevels :=
  ⟨input.valueRows_exact leaves, input.storedMainWork_bound⟩

end PetaProof.ThresholdGame.CoreGraphInput
