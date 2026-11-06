import PetaProof.GeneratedOutputSafety

/-! 論文の中心主張を一つの入口へまとめる。効率的な証拠生成や全実行時間は含めない。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

/-- 値・安全候補・任意切替・符号別優先出力についての数学的な総合保証。 -/
structure MainCorrectness (atTop : G.threshold = G.mate) (otherCore : V → Bool)
    (leaves : G.BoundedLeaves)
    (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
    (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)
    (depth otherDepth : E → Nat) : Prop where
  exact_values : ∀ x, G.ExactValue x (ctx.generatedValue otherCore x)
  safe_best : ∀ x, G.owner x = G.player →
    ∃ edge ∈ ctx.indexed.outgoing x,
      (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove x (ctx.indexed.move edge) ∧
      moveValue (ctx.generatedValue otherCore) (ctx.indexed.move edge) = ctx.generatedValue otherCore x
  preferred_exists : ∀ x, G.owner x = G.player →
    ∃ edge ∈ ctx.indexed.outgoing x,
      ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth x edge
  arbitrary_safe_lower : ∀ self opponent : G.MovePlan,
    (ctx.generatedTable atTop otherCore leaves covers otherCovers).AdmissiblePlan self →
    ∀ root payoff, G.TerminalResult (G.combinePlans self opponent) root payoff →
      ctx.generatedValue otherCore root ≤ payoff
  output_lower : ∀ opponent : G.MovePlan, ∀ root payoff,
    G.TerminalResult
      (G.combinePlans (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth) opponent)
      root payoff → ctx.generatedValue otherCore root ≤ payoff
  opposite_outputs_exact : ∀ root payoff,
    G.TerminalResult
      (G.combinePlans (ctx.generatedOutputPlan atTop otherCore leaves covers otherCovers depth)
        ((ctx.opposite otherCore).generatedOutputPlan atTop ctx.core (G.opposite_bounded_leaves leaves)
          otherCovers (ctx.opposite_opposite_core covers) otherDepth).unopposite)
      root payoff → payoff = ctx.generatedValue otherCore root

/-- 主値の正解・安全な最善手・順位族を新たに仮定せず、既証結果を総合する。 -/
theorem main_correctness (atTop : G.threshold = G.mate) (otherCore : V → Bool)
    (leaves : G.BoundedLeaves)
    (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
    (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)
    (depth otherDepth : E → Nat) :
    ctx.MainCorrectness atTop otherCore leaves covers otherCovers depth otherDepth where
  exact_values := ctx.generatedValue_exact otherCore leaves covers otherCovers
  safe_best := ctx.generated_safe_best atTop otherCore leaves covers otherCovers
  preferred_exists := ctx.generatedPreferred_exists atTop otherCore leaves covers otherCovers depth
  arbitrary_safe_lower := ctx.generatedTable_lower atTop otherCore leaves covers otherCovers
  output_lower := ctx.generatedOutputPlan_lower atTop otherCore leaves covers otherCovers depth
  opposite_outputs_exact := ctx.generatedOutputPlans_exact atTop otherCore leaves covers otherCovers depth otherDepth

end PetaProof.ThresholdGame.QueueContext
