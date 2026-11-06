import PetaProof.GeneratedStratumFamily
import PetaProof.OutputPreference

/-! 安全な生の最善手の存在を、両視点の生成証拠から導く。
出力優先定理への入力として、存在を新たに仮定しない。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

def moveValue (value : V → Int) : Move V → Int
  | .leaf score => score
  | .node child => value child

theorem ValueRankTable.moveValue_lower (table : G.ValueRankTable) (vertex : V) (move : Move V)
    (safe : table.admissibleMove vertex move) : table.value vertex ≤ moveValue table.value move := by
  cases move with
  | leaf score => exact safe.2
  | node child => exact safe.2.1

/-- 反対視点が全応手を残す条件から、自分の全合法手の生の値の上界を得る。 -/
theorem StratumFamily.moveValue_upper (family : G.StratumFamily) (other : G.opposite.StratumFamily)
    (same : ∀ vertex, other.value vertex = -family.value vertex)
    (vertex : V) (own : G.owner vertex = G.player) (move : Move V) (legal : G.legal vertex move) :
    moveValue family.value move ≤ family.value vertex := by
  have otherTurn : G.opposite.owner vertex ≠ G.opposite.player := by
    change G.owner vertex ≠ !G.player
    rw [own]
    cases G.player <;> decide
  have otherLegal : G.opposite.legal vertex move.negate := by
    change G.legal vertex move.negate.negate
    simpa only [Move.negate_negate] using legal
  have condition := other.all_replies vertex move.negate otherTurn otherLegal
  cases move with
  | leaf score =>
    change other.value vertex ≤ -score at condition
    rw [same vertex] at condition
    change score ≤ family.value vertex
    omega
  | node child =>
    have bound : other.value vertex ≤ other.value child := condition.1
    rw [same vertex, same child] at bound
    change family.value child ≤ family.value vertex
    omega

namespace QueueContext

variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

theorem generated_moveValue_upper (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) (own : G.owner vertex = G.player) (move : Move V) (legal : G.legal vertex move) :
    moveValue (ctx.generatedValue otherCore) move ≤ ctx.generatedValue otherCore vertex := by
  let family := ctx.generatedFamily atTop otherCore leaves covers otherCovers
  let other := (ctx.opposite otherCore).generatedFamily atTop ctx.core
    (G.opposite_bounded_leaves leaves) otherCovers (ctx.opposite_opposite_core covers)
  exact family.moveValue_upper other (ctx.generated_opposite_sign otherCore leaves covers otherCovers)
    vertex own move legal

/-- 安全な生成候補の非空性と両側の上界から、生の最善値に等しい実辺を得る。 -/
theorem generated_safe_best (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) (own : G.owner vertex = G.player) :
    ∃ edge ∈ ctx.indexed.outgoing vertex,
      (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex (ctx.indexed.move edge) ∧
      moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge) = ctx.generatedValue otherCore vertex := by
  obtain ⟨move, safe⟩ := ctx.generatedTable_nonempty atTop otherCore leaves covers otherCovers vertex own
  have lower := (ctx.generatedTable atTop otherCore leaves covers otherCovers).moveValue_lower vertex move safe
  have upper := ctx.generated_moveValue_upper atTop otherCore leaves covers otherCovers vertex own move safe.1
  obtain ⟨edge, member, same⟩ := ctx.indexed.covers vertex move safe.1
  refine ⟨edge, member, ?_, ?_⟩
  · simpa only [same] using safe
  · rw [same]
    exact Int.le_antisymm upper lower

/-- 優先対象は、生成表の安全性・生の同点・符号別depthを全て満たす元辺。 -/
noncomputable def generatedPreferred (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) (vertex : V) : E → Prop :=
  OutputPreference.Preferred (fun edge => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge)) depth
    (fun edge => edge ∈ ctx.indexed.outgoing vertex ∧
      (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex (ctx.indexed.move edge))
    (ctx.generatedValue otherCore vertex)

theorem generatedPreferred_exists (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) (vertex : V) (own : G.owner vertex = G.player) :
    ∃ edge ∈ ctx.indexed.outgoing vertex,
      ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex edge := by
  obtain ⟨edge, member, safe, same⟩ := ctx.generated_safe_best atTop otherCore leaves covers otherCovers vertex own
  exact OutputPreference.preferred_exists
    (fun edge => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge)) depth
    (fun edge => edge ∈ ctx.indexed.outgoing vertex ∧
      (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex (ctx.indexed.move edge))
    (ctx.generatedValue otherCore vertex) (ctx.indexed.outgoing vertex) (fun _ accepted => accepted.1)
    ⟨edge, member, ⟨member, safe⟩, same⟩

/-- 入力から得た非空な優先集合の一手を実際の計画として選ぶ。 -/
noncomputable def generatedOutputPlan (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) : G.MovePlan := by
  classical
  exact {
    choose := fun _ vertex => if own : G.owner vertex = G.player then
      ctx.indexed.move (Classical.choose
        (ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth vertex own))
      else G.defaultPlan.choose [] vertex
    legal := by
      intro history vertex
      by_cases own : G.owner vertex = G.player
      · simp only [dif_pos own]
        exact ctx.indexed.legal vertex _ (Classical.choose_spec
          (ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth vertex own)).1
      · simp only [dif_neg own]
        exact G.defaultPlan.legal [] vertex
  }

theorem generatedOutputPlan_admissible (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) :
    (ctx.generatedTable atTop otherCore leaves covers otherCovers).AdmissiblePlan
      (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth) := by
  classical
  intro history vertex own
  simp only [generatedOutputPlan, dif_pos own]
  exact (Classical.choose_spec
    (ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth vertex own)).2.1.2

/-- 正解値・順位族・安全な最善手を追加の入力にせず、構成した計画の下限保証を得る。 -/
theorem generatedOutputPlan_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) (opponent : G.MovePlan) (root : V) (payoff : Int)
    (result : G.TerminalResult
      (G.combinePlans (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth) opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff :=
  ctx.generatedTable_lower atTop otherCore leaves covers otherCovers _ opponent
    (ctx.generatedOutputPlan_admissible atTop otherCore leaves covers otherCovers depth) root payoff result

theorem generatedOutputPlan_maximum (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) (history : List V) (vertex : V) (own : G.owner vertex = G.player) :
    ∃ edge ∈ ctx.indexed.outgoing vertex,
      (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth).choose history vertex = ctx.indexed.move edge ∧
      ∀ other ∈ ctx.indexed.outgoing vertex,
        OutputPreference.encoded
          (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
          (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
          (ctx.generatedValue otherCore vertex) other ≤
        OutputPreference.encoded
          (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
          (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
          (ctx.generatedValue otherCore vertex) edge := by
  classical
  let edge := Classical.choose (ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth vertex own)
  have spec := Classical.choose_spec (ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth vertex own)
  refine ⟨edge, spec.1, ?_, ?_⟩
  · simp only [generatedOutputPlan, dif_pos own, edge]
  · apply (OutputPreference.maximum_iff _ _ (ctx.indexed.outgoing vertex) (ctx.generatedValue otherCore vertex)
      _ _ ⟨edge, spec⟩ edge spec.1).mpr spec.2
    · intro other member
      exact ctx.generated_moveValue_upper atTop otherCore leaves covers otherCovers vertex own _
        (ctx.indexed.legal vertex other member)
    · intro _ _ accepted
      exact accepted.2.1

/-- 入力グラフから生成した証拠と元辺だけで、保存最大手選択の下限保証まで閉じる。 -/
theorem generated_output_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth : E → Nat) (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ ctx.indexed.outgoing vertex, self.choose history vertex = ctx.indexed.move edge ∧
        ∀ other ∈ ctx.indexed.outgoing vertex,
          OutputPreference.encoded
            (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
            (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
            (ctx.generatedValue otherCore vertex) other ≤
          OutputPreference.encoded
            (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
            (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
            (ctx.generatedValue otherCore vertex) edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff := by
  apply OutputPreference.encoded_plan_lower
    (ctx.generatedTable atTop otherCore leaves covers otherCovers)
    (ctx.generatedTable_replies atTop otherCore leaves covers otherCovers)
    ctx.indexed.outgoing ctx.indexed.move
    (fun _ edge => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge)) depth
    (ctx.generatedValue otherCore) _ _ self opponent selected root payoff result
  · intro vertex own edge member
    exact ctx.generated_moveValue_upper atTop otherCore leaves covers otherCovers vertex own _
      (ctx.indexed.legal vertex edge member)
  · exact ctx.generated_safe_best atTop otherCore leaves covers otherCovers

/-- 両視点で構成した出力計画同士の対局では、最初の終局利得が生成値に一致する。 -/
theorem generatedOutputPlans_exact (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (depth otherDepth : E → Nat) (root : V) (payoff : Int)
    (result : G.TerminalResult
      (G.combinePlans (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth)
        ((ctx.opposite otherCore).generatedOutputPlan atTop ctx.core
          (G.opposite_bounded_leaves leaves) otherCovers (ctx.opposite_opposite_core covers) otherDepth).unopposite)
      root payoff) : payoff = ctx.generatedValue otherCore root := by
  have lower := ctx.generatedOutputPlan_lower atTop otherCore leaves covers otherCovers depth _ root payoff result
  have reflected := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at reflected
  have upper := (ctx.opposite otherCore).generatedOutputPlan_lower atTop ctx.core
    (G.opposite_bounded_leaves leaves) otherCovers (ctx.opposite_opposite_core covers) otherDepth _ root (-payoff) reflected
  rw [ctx.generated_opposite_sign otherCore leaves covers otherCovers root] at upper
  omega

end QueueContext
end PetaProof.ThresholdGame
