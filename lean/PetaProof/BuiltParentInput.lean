import PetaProof.ReverseAdjacency

/-! 逆辺を入力に要求しない有限グラフから、既証の主値計算へ接続する。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v}

/-- coreフラグはまだ入力するが、ParentListsは入力しない。 -/
structure ForwardInput (G : ThresholdGame V) (E : Type v) where
  vertices : List V
  unique : vertices.Nodup
  covered : ∀ vertex, vertex ∈ vertices
  indexed : G.IndexedMoves E
  core : V → Bool
  checked : V → V → Bool
  check_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace ForwardInput

variable {G : ThresholdGame V} (input : ForwardInput G E)

def allEdges : List E := input.vertices.flatMap input.indexed.outgoing

theorem allEdges_contains (edge : E) : edge ∈ input.allEdges :=
  List.mem_flatMap.mpr ⟨input.indexed.source edge, input.covered _, input.indexed.at_source edge⟩

theorem allEdges_unique : input.allEdges.Nodup := by
  have generic : ∀ vertices : List V, vertices.Nodup → (vertices.flatMap input.indexed.outgoing).Nodup := by
    intro vertices unique
    induction vertices with
    | nil => exact List.nodup_nil
    | cons vertex rest ih =>
      have parts := List.nodup_cons.mp unique
      apply List.pairwise_append.mpr
      refine ⟨input.indexed.unique vertex, ih parts.2, ?_⟩
      intro a first b second equal
      obtain ⟨other, member, present⟩ := List.mem_flatMap.mp second
      have same := (input.indexed.source_of_mem vertex a first).symm.trans
        ((congrArg input.indexed.source equal).trans (input.indexed.source_of_mem other b present))
      exact parts.1 (same ▸ member)
  exact generic input.vertices input.unique

variable [DecidableEq V]

def parents : ParentLists input.indexed where
  incoming := ReverseAdjacency.build input.indexed.move input.vertices input.allEdges
  unique := by
    intro vertex
    rw [ReverseAdjacency.build_row _ _ _ vertex (input.covered vertex)]
    exact input.allEdges_unique.filter _
  exact := by
    intro vertex edge
    rw [ReverseAdjacency.build_row _ _ _ vertex (input.covered vertex)]
    simp only [List.mem_filter, input.allEdges_contains edge, true_and, ReverseAdjacency.targets_spec]

/-- 構築済みの逆辺表は両側で共有でき、leafの符号反転では変わらない。 -/
def context : G.QueueContext E where
  vertices := input.vertices
  unique := input.unique
  covered := input.covered
  indexed := input.indexed
  parents := input.parents
  core := input.core
  checked := input.checked
  check_correct := input.check_correct

theorem incoming_row (vertex : V) :
    input.parents.incoming vertex = input.allEdges.filter (ReverseAdjacency.targets input.indexed.move vertex) :=
  ReverseAdjacency.build_row _ _ _ vertex (input.covered vertex)

theorem opposite_shares_parents (otherCore : V → Bool) :
    (input.context.opposite otherCore).parents.incoming = input.parents.incoming := rfl

variable [DecidableEq E]

def parentConstructionWork : Nat :=
  ReverseAdjacency.constructionWork input.indexed.move input.vertices input.allEdges

theorem parentConstructionWork_bound : input.parentConstructionWork ≤
    4 * input.vertices.length + 4 * input.allEdges.length :=
  ReverseAdjacency.constructionWork_bound _ _ input.unique _ input.allEdges_unique

/-- 正方向の入力から逆辺を一度構築し、両側の閾値生成と主処理へ進む。 -/
def valueRows (otherCore : V → Bool) : List (V × Int) :=
  let ctx := input.context
  ctx.generatedValueRows otherCore

def preparedValueWork (otherCore : V → Bool) : Nat :=
  input.parentConstructionWork + input.context.generatedWork otherCore

theorem valueRows_length (otherCore : V → Bool) : (input.valueRows otherCore).length = input.vertices.length := by
  rw [valueRows, input.context.generatedValueRows_eq]
  exact input.context.computedValueRows_length otherCore

theorem valueRows_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → input.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (row : V × Int) (member : row ∈ input.valueRows otherCore) : G.ExactValue row.1 row.2 := by
  rw [valueRows, input.context.generatedValueRows_eq] at member
  exact input.context.computedValueRows_exact otherCore leaves own_covers other_covers row member

theorem preparedValueWork_bound (otherCore : V → Bool) :
    input.preparedValueWork otherCore ≤ 19 * input.vertices.length + 30 * input.allEdges.length +
      42 * (G.mate.toNat + 1) + input.context.localTerm input.context.generatedLevels +
      (input.context.opposite otherCore).localTerm (input.context.opposite otherCore).generatedLevels := by
  have reverse := input.parentConstructionWork_bound
  have main := input.context.generatedWork_bound otherCore
  change input.context.generatedWork otherCore ≤ 15 * input.vertices.length + 26 * input.allEdges.length +
    42 * (G.mate.toNat + 1) + input.context.localTerm input.context.generatedLevels +
      (input.context.opposite otherCore).localTerm (input.context.opposite otherCore).generatedLevels at main
  unfold preparedValueWork
  omega

theorem rows_and_work (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → input.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    (∀ row ∈ input.valueRows otherCore, G.ExactValue row.1 row.2) ∧
      input.preparedValueWork otherCore ≤ 19 * input.vertices.length + 30 * input.allEdges.length +
        42 * (G.mate.toNat + 1) + input.context.localTerm input.context.generatedLevels +
        (input.context.opposite otherCore).localTerm (input.context.opposite otherCore).generatedLevels :=
  ⟨input.valueRows_exact otherCore leaves own_covers other_covers, input.preparedValueWork_bound otherCore⟩

end ForwardInput
end PetaProof.ThresholdGame
