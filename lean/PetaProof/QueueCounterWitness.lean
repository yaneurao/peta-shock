import PetaProof.QueueThresholdWitness

/-! 相手側の実phaseから、元視点の0・負の下限を覆う反証証拠を取り出す。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

omit [DecidableEq V] [DecidableEq E] in
/-- 視点を二度反転しても王手循環候補の包含条件は元と同じ。 -/
theorem opposite_opposite_core
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) :
    ∀ vertex, CyclicVertex G.opposite.opposite.OpponentChecking vertex → ctx.core vertex = true := by
  simpa only [ThresholdGame.opposite, Bool.not_not] using covers

theorem other_generated_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) :
    G.opposite.ExactValue vertex ((ctx.opposite otherCore).generatedValue ctx.core vertex) :=
  (ctx.opposite otherCore).generatedValue_exact ctx.core (G.opposite_bounded_leaves leaves)
    otherCovers (ctx.opposite_opposite_core covers) vertex

/-- 符号反転は外部の仮定ではなく、両側の計算値の正当性と整数値の一意性から導く。 -/
theorem generated_opposite_sign (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) :
    (ctx.opposite otherCore).generatedValue ctx.core vertex = -ctx.generatedValue otherCore vertex := by
  have own := ctx.generatedValue_exact otherCore leaves covers otherCovers vertex
  have reflected := ExactValue.of_opposite G vertex _ (ctx.other_generated_exact otherCore leaves covers otherCovers vertex)
  have same := ExactValue.unique G ctx.vertices ctx.covered vertex own reflected
  omega

/-- 相手の正閾値1-bのphaseの補集合を、元視点のF>=bへ添字だけ変更する。
同じ反証手・同じ順位を保持し、元視点の値や手順を新しく探索し直さない。 -/
theorem phase_counter_region (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (state : PropagationState V E) (certificate : StateCertificate (ctx.opposite otherCore).indexed state)
    (boundary : (ctx.opposite otherCore).Boundary state)
    (bound : Int) (better : -G.mate < bound) (nonpositive : bound ≤ 0)
    (lower : 1 - bound ≤ G.threshold) :
    ∃ region : (G.counterThreshold bound better nonpositive).RefutationRegion
        (fun vertex => bound ≤ ctx.generatedValue otherCore vertex),
      ∀ vertex, bound ≤ ctx.generatedValue otherCore vertex → region.rank vertex ≤ ctx.vertices.length + 2 := by
  let other := ctx.opposite otherCore
  have positive : 0 < 1 - bound := by omega
  obtain ⟨regions⟩ := other.phase_generated_regions ctx.core (G.opposite_bounded_leaves leaves)
    otherCovers (ctx.opposite_opposite_core covers) state certificate boundary (1 - bound) positive lower
  have same (vertex : V) :
      ¬ (1 - bound ≤ other.generatedValue ctx.core vertex) ↔ bound ≤ ctx.generatedValue otherCore vertex := by
    have sign := ctx.generated_opposite_sign otherCore leaves covers otherCovers vertex
    change (ctx.opposite otherCore).generatedValue ctx.core vertex = -ctx.generatedValue otherCore vertex at sign
    change ¬ (1 - bound ≤ (ctx.opposite otherCore).generatedValue ctx.core vertex) ↔ _
    rw [sign]
    omega
  let selected := regions.negative.region.reindex same
  refine ⟨selected, ?_⟩
  intro vertex inside
  exact regions.negative.rank_bound vertex ((same vertex).mpr inside)

end PetaProof.ThresholdGame.QueueContext
