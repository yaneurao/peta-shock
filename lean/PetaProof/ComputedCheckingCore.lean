import PetaProof.BuiltParentInput
import PetaProof.SccIndexedView
import PetaProof.LinearCycleFlags

/-! 構築した逆辺を使って王手継続グラフを分解し、core包含条件を生成する。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

namespace QueueContext

variable (ctx : G.QueueContext E)

/-- 相手手番では王手だけを残す。leafはSCCの内部辺にはならない。 -/
def checkingAllow (edge : E) : Bool :=
  match ctx.indexed.move edge with
  | .leaf _ => false
  | .node child => decide (G.owner (ctx.indexed.source edge) = G.player) ||
      ctx.checked (ctx.indexed.source edge) child

def checkingOut : V → List (Option V) :=
  SccIndexedView.outgoing (SccIndexedView.ofIndexed ctx.indexed) ctx.checkingAllow

omit [DecidableEq V] [DecidableEq E] in
theorem checkingEdge (vertex child : V) :
    ForwardDfs.Edge ctx.checkingOut vertex child ↔ G.OpponentChecking vertex child := by
  rw [checkingOut, SccIndexedView.outgoing_correct, SccIndexedView.ofIndexed_relation]
  constructor
  · rintro ⟨edge, member, move, permitted⟩
    have source := ctx.indexed.source_of_mem vertex edge member
    refine ⟨?_, ?_⟩
    · simpa only [move] using ctx.indexed.legal vertex edge member
    · simpa only [checkingAllow, move, source, Bool.or_eq_true, decide_eq_true_eq,
        ctx.check_correct] using permitted
  · rintro ⟨legal, allowed⟩
    obtain ⟨edge, member, move⟩ := ctx.indexed.covers vertex (.node child) legal
    refine ⟨edge, member, move, ?_⟩
    have source := ctx.indexed.source_of_mem vertex edge member
    simpa only [checkingAllow, move, source, Bool.or_eq_true, decide_eq_true_eq,
      ctx.check_correct] using allowed

/-- 通常伝播と同じ構築済み逆辺を、元辺IDの許可条件で選別する。 -/
def checkingParents (child : V) : List V :=
  ((ctx.parents.incoming child).filter ctx.checkingAllow).map ctx.indexed.source

omit [DecidableEq V] [DecidableEq E] in
theorem checkingTranspose (child parent : V) :
    parent ∈ ctx.checkingParents child ↔ ForwardDfs.Edge ctx.checkingOut parent child := by
  rw [checkingOut, SccIndexedView.outgoing_correct, SccIndexedView.ofIndexed_relation]
  simp only [checkingParents, List.mem_map, List.mem_filter, ctx.parents.exact]
  constructor
  · rintro ⟨edge, ⟨move, allowed⟩, source⟩
    exact ⟨edge, source ▸ ctx.indexed.at_source edge, move, allowed⟩
  · rintro ⟨edge, member, move, allowed⟩
    exact ⟨edge, ⟨move, allowed⟩, ctx.indexed.source_of_mem parent edge member⟩

def checkingSelf : V → Bool :=
  SccSelfLoop.fromParents ctx.indexed ctx.checkingAllow ctx.parents.incoming

omit [DecidableEq E] in
theorem checkingSelf_correct (vertex : V) :
    ctx.checkingSelf vertex = true ↔ ForwardDfs.Edge ctx.checkingOut vertex vertex := by
  rw [checkingOut, SccIndexedView.outgoing_correct, SccIndexedView.ofIndexed_relation]
  exact SccSelfLoop.parents_correct ctx.indexed ctx.checkingAllow ctx.parents.incoming ctx.parents.exact vertex

def checkingComponent : V → Nat :=
  let order := ForwardDfs.order ctx.vertices ctx.vertices ctx.checkingOut
  let result := ComponentNumbering.finish ctx.vertices order ctx.checkingParents
  fun vertex => (result.result vertex).getD 0

omit [DecidableEq E] in
theorem checkingComponent_bound (vertex : V) : ctx.checkingComponent vertex < ctx.vertices.length :=
  ComponentNumbering.component_bound ctx.vertices ctx.unique ctx.covered _
    (ForwardDfs.order_covers ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered ctx.checkingOut)
    ctx.checkingParents vertex

def checkingPartition : SccPartition (ForwardDfs.Edge ctx.checkingOut) :=
  KosarajuStep.computedPartition ctx.vertices ctx.unique ctx.covered ctx.vertices ctx.covered
    ctx.checkingOut ctx.checkingParents ctx.checkingTranspose

/-- 成分番号と集計表は一度構築し、頂点ごとの参照では再構築しない。 -/
def builtCheckingCore : V → Bool :=
  let component := ctx.checkingComponent
  let aggregate := LinearCycleFlags.build ctx.vertices component ctx.checkingSelf
  fun vertex => LinearCycleFlags.flag aggregate (component vertex)

omit [DecidableEq E] in
theorem builtCheckingCore_correct (vertex : V) :
    ctx.builtCheckingCore vertex = true ↔ CyclicVertex G.OpponentChecking vertex := by
  change LinearCycleFlags.flag (LinearCycleFlags.build ctx.vertices ctx.checkingComponent ctx.checkingSelf)
    (ctx.checkingComponent vertex) = true ↔ _
  rw [LinearCycleFlags.flag_eq _ _ _ _ (ctx.checkingComponent_bound vertex)]
  have exact_flag := ComponentCycleFlags.flag_iff_cyclic ctx.vertices ctx.unique ctx.covered
    ctx.checkingPartition ctx.checkingSelf ctx.checkingSelf_correct vertex
  change ComponentCycleFlags.flag ctx.vertices ctx.checkingComponent ctx.checkingSelf
    (ctx.checkingComponent vertex) = true ↔ _ at exact_flag
  rw [exact_flag]
  have same : ForwardDfs.Edge ctx.checkingOut = G.OpponentChecking :=
    funext (fun a => funext (fun b => propext (ctx.checkingEdge a b)))
  rw [same]

end QueueContext

/-- 入力には候補集合・逆辺・SCCの正解を含めない。 -/
structure CoreGraphInput (G : ThresholdGame V) (E : Type v) where
  vertices : List V
  unique : vertices.Nodup
  covered : ∀ vertex, vertex ∈ vertices
  indexed : G.IndexedMoves E
  checked : V → V → Bool
  check_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace CoreGraphInput

variable (input : CoreGraphInput G E)

def forward : ForwardInput G E where
  vertices := input.vertices
  unique := input.unique
  covered := input.covered
  indexed := input.indexed
  core := fun _ => false
  checked := input.checked
  check_correct := input.check_correct

/-- 二つの王手継続グラフは許可条件だけを変え、同じ逆辺表を使う。 -/
def prepared : G.QueueContext E × (V → Bool) :=
  let ctx := input.forward.context
  let ownCore := ctx.builtCheckingCore
  let otherCore := (ctx.opposite (fun _ => false)).builtCheckingCore
  ({ ctx with core := ownCore }, otherCore)

omit [DecidableEq E] in
theorem ownCore_correct (vertex : V) :
    input.prepared.1.core vertex = true ↔ CyclicVertex G.OpponentChecking vertex :=
  input.forward.context.builtCheckingCore_correct vertex

omit [DecidableEq E] in
theorem otherCore_correct (vertex : V) :
    input.prepared.2 vertex = true ↔ CyclicVertex G.opposite.OpponentChecking vertex :=
  (input.forward.context.opposite (fun _ => false)).builtCheckingCore_correct vertex

def valueRows : List (V × Int) :=
  let prepared := input.prepared
  prepared.1.generatedValueRows prepared.2

theorem valueRows_length : input.valueRows.length = input.vertices.length := by
  rw [valueRows, input.prepared.1.generatedValueRows_eq]
  exact input.prepared.1.computedValueRows_length input.prepared.2

theorem valueRows_unique_ids : (input.valueRows.map Prod.fst).Nodup := by
  rw [valueRows, input.prepared.1.generatedValueRows_eq]
  exact input.prepared.1.computedValueRows_unique_ids input.prepared.2

theorem valueRows_cover (vertex : V) : ∃ value, (vertex, value) ∈ input.valueRows := by
  rw [valueRows, input.prepared.1.generatedValueRows_eq]
  exact ⟨_, input.prepared.1.computedValueRows_cover input.prepared.2 vertex⟩

/-- coreの包含性は呼出側の仮定ではなく、二つのSCC計算から得る。 -/
theorem valueRows_exact (leaves : G.BoundedLeaves) (row : V × Int)
    (member : row ∈ input.valueRows) : G.ExactValue row.1 row.2 := by
  rw [valueRows, input.prepared.1.generatedValueRows_eq] at member
  exact input.prepared.1.computedValueRows_exact input.prepared.2 leaves
    (fun vertex cyclic => (input.ownCore_correct vertex).mpr cyclic)
    (fun vertex cyclic => (input.otherCore_correct vertex).mpr cyclic) row member

theorem rows_correct (leaves : G.BoundedLeaves) :
    input.valueRows.length = input.vertices.length ∧
      (input.valueRows.map Prod.fst).Nodup ∧
      (∀ vertex, ∃ value, (vertex, value) ∈ input.valueRows) ∧
      (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) :=
  ⟨input.valueRows_length, input.valueRows_unique_ids, input.valueRows_cover, input.valueRows_exact leaves⟩

end CoreGraphInput
end PetaProof.ThresholdGame
