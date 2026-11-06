import PetaProof.KosarajuPartition
import PetaProof.SafetyIncomingBuild
import PetaProof.SccSelfLoop

/-!
辺IDを保った出辺列から、許可辺のDFSスロットと逆辺callbackを構築する。
逆辺は全内部辺を登録し、callback側で元の辺IDのallowを評価する。
CSRの物理配列ではなく、子ごとの逐次appendで表した構築モデルを扱う。
-/
namespace PetaProof.SccIndexedView

universe u v

/-- source/childは辺IDの属性。異なる辺IDが同じ親子を持つ場合も区別する。 -/
structure View (V : Type u) (E : Type v) where
  outgoing : V → List E
  source : E → V
  child : E → Option V
  at_source : ∀ edge, edge ∈ outgoing (source edge)
  source_of_mem : ∀ vertex edge, edge ∈ outgoing vertex → source edge = vertex

variable {V : Type u} {E : Type v} [DecidableEq V]

def internal (view : View V E) (edge : E) : Bool := (view.child edge).isSome

/-- leafの仮targetは登録時に参照されない。 -/
def target (view : View V E) (edge : E) : V := (view.child edge).getD (view.source edge)

def allInternal (view : View V E) (vertices : List V) : List E :=
  (vertices.flatMap view.outgoing).filter (internal view)

def incoming (view : View V E) (vertices : List V) : V → List E :=
  SafetyClassification.buildBuckets (target view) id (allInternal view vertices) (fun _ => [])

/-- 登録列の順序と重複回数も保つ。所属関係だけの仕様ではない。 -/
theorem incoming_spec (view : View V E) (vertices : List V) (child : V) :
    incoming view vertices child = (allInternal view vertices).filter (fun edge => target view edge == child) := by
  rw [incoming, SafetyClassification.buildBuckets_spec]
  simp

omit [DecidableEq V] in
theorem allInternal_member (view : View V E) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (edge : E) :
    edge ∈ allInternal view vertices ↔ internal view edge = true := by
  simp only [allInternal, List.mem_filter]
  constructor
  · exact And.right
  · intro inside
    exact ⟨List.mem_flatMap.mpr ⟨view.source edge, covered _, view.at_source edge⟩, inside⟩

omit [DecidableEq V] in
theorem internal_target (view : View V E) (edge : E) (child : V) :
    (internal view edge = true ∧ target view edge = child) ↔ view.child edge = some child := by
  cases found : view.child edge <;> simp [internal, target, found]

/-- 全内部辺の逐次登録から、逆辺の完全性・健全性を導く。 -/
theorem incoming_member (view : View V E) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (child : V) (edge : E) :
    edge ∈ incoming view vertices child ↔ view.child edge = some child := by
  rw [incoming, SafetyClassification.buildBuckets_spec]
  simp only [List.nil_append, List.map_id, List.mem_filter, beq_iff_eq,
    allInternal_member view vertices covered]
  exact internal_target view edge child

/-- 不許可の手とleafもスロットとして残し、DFSではnoneとして飛ばす。 -/
def outgoing (view : View V E) (allow : E → Bool) (vertex : V) : List (Option V) :=
  (view.outgoing vertex).map (fun edge => if allow edge then view.child edge else none)

def relation (view : View V E) (allow : E → Bool) (vertex child : V) : Prop :=
  ∃ edge, edge ∈ view.outgoing vertex ∧ view.child edge = some child ∧ allow edge = true

omit [DecidableEq V] in
theorem slot_some (view : View V E) (allow : E → Bool) (edge : E) (child : V) :
    (if allow edge then view.child edge else none) = some child ↔
      view.child edge = some child ∧ allow edge = true := by
  cases permitted : allow edge <;> simp [permitted]

omit [DecidableEq V] in
theorem outgoing_correct (view : View V E) (allow : E → Bool) (vertex child : V) :
    ForwardDfs.Edge (outgoing view allow) vertex child ↔ relation view allow vertex child := by
  change some child ∈ outgoing view allow vertex ↔ _
  simp only [outgoing, List.mem_map, slot_some, relation]

/-- 許可条件は親IDではなく、逆辺に保存した元の辺IDについて判定する。 -/
def parents (view : View V E) (vertices : List V) (allow : E → Bool) (child : V) : List V :=
  ((incoming view vertices child).filter allow).map view.source

theorem parents_transpose (view : View V E) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (child parent : V) :
    parent ∈ parents view vertices allow child ↔ ForwardDfs.Edge (outgoing view allow) parent child := by
  rw [outgoing_correct]
  simp only [parents, List.mem_map, List.mem_filter, incoming_member view vertices covered]
  constructor
  · rintro ⟨edge, ⟨found, permitted⟩, source⟩
    exact ⟨edge, source ▸ view.at_source edge, found, permitted⟩
  · rintro ⟨edge, member, found, permitted⟩
    exact ⟨edge, ⟨found, permitted⟩, view.source_of_mem parent edge member⟩

/-- 逆辺callbackが自己辺を見つける条件。未割当判定とは独立に評価する。 -/
def selfLoop (view : View V E) (vertices : List V) (allow : E → Bool) (vertex : V) : Bool :=
  (incoming view vertices vertex).any (fun edge => decide (view.source edge = vertex) && allow edge)

theorem selfLoop_correct (view : View V E) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (vertex : V) :
    selfLoop view vertices allow vertex = true ↔ ForwardDfs.Edge (outgoing view allow) vertex vertex := by
  rw [outgoing_correct]
  simp only [selfLoop, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    incoming_member view vertices covered]
  constructor
  · rintro ⟨edge, found, source, permitted⟩
    exact ⟨edge, source ▸ view.at_source edge, found, permitted⟩
  · rintro ⟨edge, member, found, permitted⟩
    exact ⟨edge, found, view.source_of_mem vertex edge member, permitted⟩

def component (view : View V E) (vertices roots : List V) (allow : E → Bool) : V → Nat :=
  ComponentNumbering.component vertices (ForwardDfs.order vertices roots (outgoing view allow))
    (parents view vertices allow)

/-- 転置一致の前提を外から渡さず、逆辺構築から得て両DFSへ接続する。 -/
theorem component_eq_iff (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots)
    (allow : E → Bool) (a b : V) :
    component view vertices roots allow a = component view vertices roots allow b ↔
      ForwardDfs.Mutual (outgoing view allow) a b :=
  KosarajuStep.component_eq_iff_mutual vertices unique covered roots roots_cover _ _
    (parents_transpose view vertices covered allow) a b

def computedPartition (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots)
    (allow : E → Bool) : SccPartition (ForwardDfs.Edge (outgoing view allow)) :=
  KosarajuStep.computedPartition vertices unique covered roots roots_cover _ _
    (parents_transpose view vertices covered allow)

def core (view : View V E) (vertices roots : List V) (allow : E → Bool) : List V :=
  CoreEnumeration.core (ComponentCycleFlags.keep vertices (component view vertices roots allow)
    (selfLoop view vertices allow)) vertices

theorem core_correct (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots)
    (allow : E → Bool) (vertex : V) :
    vertex ∈ core view vertices roots allow ↔ CyclicVertex (ForwardDfs.Edge (outgoing view allow)) vertex :=
  KosarajuStep.computed_core_correct vertices unique covered roots roots_cover _ _
    (parents_transpose view vertices covered allow) _ (selfLoop_correct view vertices covered allow) vertex

omit [DecidableEq V] in
theorem cyclic_relation (view : View V E) (allow : E → Bool) (vertex : V) :
    CyclicVertex (ForwardDfs.Edge (outgoing view allow)) vertex ↔ CyclicVertex (relation view allow) vertex := by
  constructor
  · rintro ⟨child, edge, ⟨path⟩⟩
    exact ⟨child, (outgoing_correct view allow vertex child).mp edge,
      ⟨path.map (fun a b found => (outgoing_correct view allow a b).mp found)⟩⟩
  · rintro ⟨child, edge, ⟨path⟩⟩
    exact ⟨child, (outgoing_correct view allow vertex child).mpr edge,
      ⟨path.map (fun a b found => (outgoing_correct view allow a b).mpr found)⟩⟩

theorem core_relation_correct (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots)
    (allow : E → Bool) (vertex : V) :
    vertex ∈ core view vertices roots allow ↔ CyclicVertex (relation view allow) vertex :=
  (core_correct view vertices unique covered roots roots_cover allow vertex).trans (cyclic_relation view allow vertex)

/-- 既存のゲームモデルの辺IDをそのまま受け取り、leafだけをnoneへ写す。 -/
def ofIndexed {G : ThresholdGame V} (indexed : G.IndexedMoves E) : View V E where
  outgoing := indexed.outgoing
  source := indexed.source
  child := fun edge => match indexed.move edge with
    | .node child => some child
    | .leaf _ => none
  at_source := indexed.at_source
  source_of_mem := indexed.source_of_mem

omit [DecidableEq V] in
theorem ofIndexed_child {G : ThresholdGame V} (indexed : G.IndexedMoves E) (edge : E) (child : V) :
    (ofIndexed indexed).child edge = some child ↔ indexed.move edge = .node child := by
  cases found : indexed.move edge <;> simp [ofIndexed, found]

omit [DecidableEq V] in
theorem ofIndexed_relation {G : ThresholdGame V} (indexed : G.IndexedMoves E) (allow : E → Bool) (a b : V) :
    relation (ofIndexed indexed) allow a b ↔ SccSelfLoop.relation indexed allow a b := by
  simp only [relation, ofIndexed_child, SccSelfLoop.relation]
  rfl

theorem indexed_core_correct {G : ThresholdGame V} (indexed : G.IndexedMoves E)
    (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (roots : List V) (roots_cover : ∀ vertex, vertex ∈ roots) (allow : E → Bool) (vertex : V) :
    vertex ∈ core (ofIndexed indexed) vertices roots allow ↔ CyclicVertex (SccSelfLoop.relation indexed allow) vertex := by
  have same : relation (ofIndexed indexed) allow = SccSelfLoop.relation indexed allow :=
    funext (fun a => funext (fun b => propext (ofIndexed_relation indexed allow a b)))
  rw [← same]
  exact core_relation_correct (ofIndexed indexed) vertices unique covered roots roots_cover allow vertex

end PetaProof.SccIndexedView
