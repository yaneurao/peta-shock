import PetaProof.ComponentCycleFlags

namespace PetaProof.SccSelfLoop

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] {G : ThresholdGame V}

/-- allowで残した内部辺が作るグラフ。leafはグラフの辺に含めない。 -/
def relation (indexed : G.IndexedMoves E) (allow : E → Bool) (vertex child : V) : Prop :=
  ∃ edge, edge ∈ indexed.outgoing vertex ∧ indexed.move edge = .node child ∧ allow edge = true

def reachesChild (indexed : G.IndexedMoves E) (edge : E) (child : V) : Bool :=
  match indexed.move edge with
  | .leaf _ => false
  | .node target => target == child

theorem reachesChild_correct (indexed : G.IndexedMoves E) (edge : E) (child : V) :
    reachesChild indexed edge child = true ↔ indexed.move edge = .node child := by
  cases move : indexed.move edge <;> simp [reachesChild, move]

def fromOutgoing (indexed : G.IndexedMoves E) (allow : E → Bool) (vertex : V) : Bool :=
  (indexed.outgoing vertex).any (fun edge => reachesChild indexed edge vertex && allow edge)

theorem outgoing_correct (indexed : G.IndexedMoves E) (allow : E → Bool) (vertex : V) :
    fromOutgoing indexed allow vertex = true ↔ relation indexed allow vertex vertex := by
  simp [fromOutgoing, relation, List.any_eq_true, reachesChild_correct]

/-- parentsの仕様を表す逆辺列。実装への全辺再走査の追加ではない。 -/
def parents (indexed : G.IndexedMoves E) (vertices : List V) (child : V) : List E :=
  (vertices.flatMap indexed.outgoing).filter (fun edge => reachesChild indexed edge child)

theorem mem_parents (indexed : G.IndexedMoves E) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (child : V) (edge : E) : edge ∈ parents indexed vertices child ↔ indexed.move edge = .node child := by
  simp only [parents, List.mem_filter, reachesChild_correct]
  constructor
  · exact And.right
  · intro move
    exact ⟨List.mem_flatMap.mpr ⟨indexed.source edge, covered _, indexed.at_source edge⟩, move⟩

/-- C++の逆辺callbackで、親==子かつallowの辺を検出する処理。 -/
def fromParents (indexed : G.IndexedMoves E) (allow : E → Bool) (incoming : V → List E) (vertex : V) : Bool :=
  (incoming vertex).any (fun edge => decide (indexed.source edge = vertex) && allow edge)

theorem parents_correct (indexed : G.IndexedMoves E) (allow : E → Bool) (incoming : V → List E)
    (complete : ∀ child edge, edge ∈ incoming child ↔ indexed.move edge = .node child) (vertex : V) :
    fromParents indexed allow incoming vertex = true ↔ relation indexed allow vertex vertex := by
  simp only [fromParents, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨edge, member, same, allowed⟩
    refine ⟨edge, ?_, (complete vertex edge).mp member, allowed⟩
    simpa only [same] using indexed.at_source edge
  · rintro ⟨edge, member, self, allowed⟩
    exact ⟨edge, (complete vertex edge).mpr self, indexed.source_of_mem vertex edge member, allowed⟩

theorem parents_eq_outgoing (indexed : G.IndexedMoves E) (allow : E → Bool) (incoming : V → List E)
    (complete : ∀ child edge, edge ∈ incoming child ↔ indexed.move edge = .node child) (vertex : V) :
    fromParents indexed allow incoming vertex = fromOutgoing indexed allow vertex := by
  have same := (parents_correct indexed allow incoming complete vertex).trans (outgoing_correct indexed allow vertex).symm
  cases left : fromParents indexed allow incoming vertex <;>
    cases right : fromOutgoing indexed allow vertex <;> simp_all

theorem constructed_parents_correct (indexed : G.IndexedMoves E) (allow : E → Bool) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    fromParents indexed allow (parents indexed vertices) vertex = true ↔ relation indexed allow vertex vertex :=
  parents_correct indexed allow _ (mem_parents indexed vertices covered) vertex

/-- SCC分割を証拠として受け取り、実際の自己ループ判定から抽出したcoreを循環頂点へ接続する。 -/
theorem extracted_core (indexed : G.IndexedMoves E) (allow : E → Bool) (vertices : List V)
    (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (partition : SccPartition (relation indexed allow))
    (bounded : ∀ vertex, partition.component vertex < vertices.length) (vertex : V) :
    vertex ∈ CoreEnumeration.core
      (ComponentCycleFlags.keep vertices partition.component (fromParents indexed allow (parents indexed vertices))) vertices ↔
      CyclicVertex (relation indexed allow) vertex := by
  exact ComponentCycleFlags.extracted_core_iff vertices unique covered partition bounded _
    (constructed_parents_correct indexed allow vertices covered) vertex

end PetaProof.SccSelfLoop
