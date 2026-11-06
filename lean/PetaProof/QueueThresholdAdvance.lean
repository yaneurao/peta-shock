import PetaProof.QueueThresholdControl
import PetaProof.IncrementalThreshold
import PetaProof.ThresholdSetScan

/-! 通常状態を初期化し直さず、新leaf帯の通知から低い閾値のキュー制御へ接続する。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

/-- 閾値だけを変える。頂点番号・元辺・逆辺・core・王手ラベルは同じである。 -/
def atLevel (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) : (G.retune t positive bounded).QueueContext E where
  vertices := ctx.vertices
  unique := ctx.unique
  covered := ctx.covered
  indexed := {
    outgoing := ctx.indexed.outgoing
    source := ctx.indexed.source
    move := ctx.indexed.move
    unique := ctx.indexed.unique
    at_source := ctx.indexed.at_source
    source_of_mem := ctx.indexed.source_of_mem
    legal := ctx.indexed.legal
    covers := ctx.indexed.covers
  }
  parents := { incoming := ctx.parents.incoming, unique := ctx.parents.unique, exact := ctx.parents.exact }
  core := ctx.core
  checked := ctx.checked
  check_correct := ctx.check_correct

def allEdges : List E := ctx.vertices.flatMap ctx.indexed.outgoing

omit [DecidableEq V] [DecidableEq E] in
theorem allEdges_contains (edge : E) : edge ∈ ctx.allEdges :=
  List.mem_flatMap.mpr ⟨ctx.indexed.source edge, ctx.covered _, ctx.indexed.at_source edge⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem outgoing_unique (indexed : G.IndexedMoves E) (vertices : List V) (unique : vertices.Nodup) :
    (vertices.flatMap indexed.outgoing).Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons vertex rest ih =>
    have parts := List.nodup_cons.mp unique
    apply List.pairwise_append.mpr
    refine ⟨indexed.unique vertex, ih parts.2, ?_⟩
    intro a first b second same
    obtain ⟨other, member, present⟩ := List.mem_flatMap.mp second
    have equal := (indexed.source_of_mem vertex a first).symm.trans
      ((congrArg indexed.source same).trans (indexed.source_of_mem other b present))
    exact parts.1 (equal ▸ member)

omit [DecidableEq V] [DecidableEq E] in
theorem allEdges_unique : ctx.allEdges.Nodup := outgoing_unique ctx.indexed ctx.vertices ctx.unique

/-- 辺列のfilterは通知対象の数学的定義。毎閾値の全辺再走査を実装へ要求しない。 -/
def leafBand (lo hi : Int) : List E := ctx.allEdges.filter (fun edge =>
  match ctx.indexed.move edge with
  | .node _ => false
  | .leaf score => decide (lo ≤ score ∧ score < hi))

omit [DecidableEq V] [DecidableEq E] in
theorem leafBand_spec (lo hi : Int) (edge : E) : edge ∈ ctx.leafBand lo hi ↔
    ∃ score, ctx.indexed.move edge = .leaf score ∧ lo ≤ score ∧ score < hi := by
  simp only [leafBand, List.mem_filter, ctx.allEdges_contains edge, true_and]
  cases move : ctx.indexed.move edge <;> simp [move]

omit [DecidableEq V] [DecidableEq E] in
theorem leafBand_unique (lo hi : Int) : (ctx.leafBand lo hi).Nodup := ctx.allEdges_unique.filter _

def goodLeaves : List E := ctx.allEdges.filter (fun edge => match ctx.indexed.move edge with
  | .node _ => false
  | .leaf score => decide (G.threshold ≤ score))

omit [DecidableEq V] [DecidableEq E] in
theorem goodLeaves_spec (edge : E) : edge ∈ ctx.goodLeaves ↔
    ∃ score, ctx.indexed.move edge = .leaf score ∧ G.threshold ≤ score := by
  simp only [goodLeaves, List.mem_filter, ctx.allEdges_contains edge, true_and]
  cases move : ctx.indexed.move edge <;> simp [move]

/-- 初期化は一度だけ行い、開始閾値の良いleafを通知する。 -/
def seeded : PropagationState V E :=
  (PropagationState.initial ctx.indexed).notifyMany ctx.indexed ctx.goodLeaves

noncomputable def seeded_certificate : StateCertificate ctx.indexed ctx.seeded := by
  apply StateCertificate.notifyMany ctx.indexed _ (StateCertificate.initial ctx.indexed)
    ctx.goodLeaves (ctx.allEdges_unique.filter _)
  · intro _ _; rfl
  · intro edge member
    obtain ⟨score, same, good⟩ := (ctx.goodLeaves_spec edge).mp member
    simpa only [same, GoodExit] using good

theorem seeded_boundary : ctx.Boundary ctx.seeded := by
  constructor
  · intro edge score same good
    exact (PropagationState.notifyMany_history ctx.indexed _ ctx.goodLeaves edge).mpr
      (Or.inr ((ctx.goodLeaves_spec edge).mpr ⟨score, same, good⟩))
  · intro child popped
    unfold seeded at popped
    rw [PropagationState.notifyMany_popped] at popped
    cases popped

/-- 新しいleaf帯だけを通知する。同じカウンター・FIFO・履歴を引き継ぐ。 -/
def prepare (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) (state : PropagationState V E) :
    PropagationState V E := state.notifyMany (ctx.atLevel t positive bounded).indexed (ctx.leafBand t G.threshold)

noncomputable def prepare_certificate (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    StateCertificate (ctx.atLevel t positive (Int.le_trans lower G.bounded)).indexed
      (ctx.prepare t positive (Int.le_trans lower G.bounded) state) := by
  exact StateCertificate.advanceLeaves ctx.indexed state certificate t positive lower
    (ctx.leafBand t G.threshold) (ctx.leafBand_unique t G.threshold)
    (fun edge member => (ctx.leafBand_spec t G.threshold edge).mp member)

theorem prepare_boundary (state : PropagationState V E) (boundary : ctx.Boundary state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (ctx.atLevel t positive (Int.le_trans lower G.bounded)).Boundary
      (ctx.prepare t positive (Int.le_trans lower G.bounded) state) := by
  constructor
  · exact StateCertificate.advanceLeaves_complete ctx.indexed state t positive lower _ boundary.leaves
      (fun edge score same good below => (ctx.leafBand_spec t G.threshold edge).mpr ⟨score, same, good, below⟩)
  · exact StateCertificate.advanceLeaves_nodes_complete ctx.indexed state t positive lower _ boundary.nodes

omit [DecidableEq V] [DecidableEq E] in
theorem leafBand_fresh (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (t : Int) (edge : E) (member : edge ∈ ctx.leafBand t G.threshold) : state.notified edge = false := by
  obtain ⟨score, same, _, below⟩ := (ctx.leafBand_spec t G.threshold edge).mp member
  exact StateCertificate.lower_leaf_fresh ctx.indexed state certificate edge score same below

def phase (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) (state : PropagationState V E) :
    PropagationState V E :=
  (ctx.atLevel t positive bounded).settleQueue ctx.vertices.length (ctx.prepare t positive bounded state)

theorem phase_certified (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    Nonempty (StateCertificate (ctx.atLevel t positive (Int.le_trans lower G.bounded)).indexed
      (ctx.phase t positive (Int.le_trans lower G.bounded) state)) :=
  (ctx.atLevel t positive _).settleQueue_certified ctx.vertices.length _
    (ctx.prepare_certificate state certificate t positive lower)

theorem phase_boundary (state : PropagationState V E) (boundary : ctx.Boundary state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (ctx.atLevel t positive (Int.le_trans lower G.bounded)).Boundary
      (ctx.phase t positive (Int.le_trans lower G.bounded) state) :=
  (ctx.atLevel t positive _).settleQueue_boundary ctx.vertices.length _ (ctx.prepare_boundary state boundary t positive lower)

theorem phase_exact (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state)
    (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) (root : V) :
    (ctx.phase t positive (Int.le_trans lower G.bounded) state).won root ↔ G.LowerGuarantee root t :=
  ((ctx.atLevel t positive _).settleQueue_exact _ (ctx.prepare_certificate state certificate t positive lower)
    (ctx.prepare_boundary state boundary t positive lower) covers_core root).trans
      (G.retune_winning_iff t positive (Int.le_trans lower G.bounded) root)

end PetaProof.ThresholdGame.QueueContext
