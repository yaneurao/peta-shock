import PetaProof.FiniteGame
import PetaProof.QueueThresholdAdvance

/-! 停止済みの確定領域を変えずに、補集合全体を一つの反証方策・順位で覆う。 -/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 既に完全性が分かる確定領域を吸収モデルへ移す。別の最大領域を選び直さない。 -/
theorem exact_region_lift_maximal [DecidableEq V] {won : V → Prop}
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (exactness : ∀ vertex, won vertex ↔ G.FourfoldWinning vertex) :
    G.absorbedArena.PolicyMaximal (extendWon won) := by
  intro other policy state inside
  cases state with
  | success => trivial
  | failure => exact False.elim (G.failure_not_in_policy policy inside)
  | node vertex =>
    apply (exactness vertex).mpr
    apply (G.fourfold_winning_iff_absorbed_history vertices covered vertex).mpr
    exact policy.history_winning (G.absorbedVertices vertices) (G.absorbedVertices_cover vertices covered)
      (.node vertex) inside

/-- 同期削除で使う補集合の列挙数は、元の列挙数以下。 -/
theorem trap_vertices_length {W : Type u} (A : HistoryArena W) {domain : W → Prop}
    (trap : A.Trap domain) (vertices : List W) : (trap.vertices vertices).length ≤ vertices.length := by
  classical
  exact List.length_filterMap_le _ _

/-- 反証の共通順位とその有限上界。値そのものや局面ごとの勝敗を追加の仮定にはしない。 -/
structure ComplementWitness (won : V → Prop) (cap : Nat) where
  region : G.RefutationRegion (fun vertex => ¬ won vertex)
  rank_bound : ∀ vertex, ¬ won vertex → region.rank vertex ≤ cap

/-- 確定領域の補集合全体を同じ削除回順位で覆う。rootごとの証拠の合併ではない。 -/
theorem exact_complement_witness [DecidableEq V] {won : V → Prop}
    (region : G.RankedRegion won) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (exactness : ∀ vertex, won vertex ↔ G.FourfoldWinning vertex) :
    Nonempty (G.ComplementWitness won (vertices.length + 2)) := by
  classical
  let lifted := G.liftRankedRegion region
  have maximal := G.exact_region_lift_maximal vertices covered exactness
  let ordinary := G.absorbedArena.maximal_policy_ordinary lifted maximal
  let trap := G.absorbedArena.complementTrap ordinary
  let states := G.absorbedVertices vertices
  obtain ⟨n, bounded, empty⟩ := G.absorbedArena.residual_deletion_empty lifted maximal ordinary
    states (G.absorbedVertices_cover vertices covered)
  let counter := trap.restricted.counterstrategyOfEmpty n empty
  let negative := G.extractRefutationRegion ordinary (show extendWon won .success from trivial) counter
  have count : (trap.vertices states).length ≤ vertices.length + 2 := by
    have shorter := trap_vertices_length G.absorbedArena trap states
    simpa only [states, G.absorbedVertices_length] using shorter
  refine ⟨⟨negative, ?_⟩⟩
  intro vertex outside
  have absent : ¬ extendWon won (.node vertex) := outside
  have rankBound := (trap.restricted.deletionTime_spec n empty ⟨.node vertex, absent⟩).1
  have same : negative.rank vertex = trap.restricted.deletionTime n empty ⟨.node vertex, absent⟩ := by
    simp only [negative, extractRefutationRegion, dif_pos absent, counter, HistoryArena.counterstrategyOfEmpty]
  rw [same]
  omega

/-- 停止条件から、同じ確定集合の全補集合に対する反証証明書を得る。 -/
theorem stopped_complement_witness [DecidableEq V] {won : V → Prop}
    (region : G.RankedRegion won) (ordinary : G.OrdinaryClosed won)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (core : V → Prop) (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → core vertex)
    (n : Nat) (empty : ∀ vertex, ¬ G.pruneIter won (fun child => core child ∧ ¬ won child) n vertex) :
    Nonempty (G.ComplementWitness won (vertices.length + 2)) :=
  G.exact_complement_witness region vertices covered
    (G.stopped_exact_for_fourfold region ordinary vertices covered core covers n empty)

end PetaProof.ThresholdGame
