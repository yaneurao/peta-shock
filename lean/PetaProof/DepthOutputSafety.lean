import PetaProof.GeneratedOutputSafety

/-! 現行のdepth優先に必要な保証を明示する。
安全候補の生成と保存最大手の選択を前提に、depthの正確さや減少性は要求しない。
製品C++の検証器との一致や、脱出手数の最短性を主張するものではない。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)
variable (atTop : G.threshold = G.mate) (otherCore : V → Bool)
variable (leaves : G.BoundedLeaves)
variable (covers : ∀ x, CyclicVertex G.OpponentChecking x → ctx.core x = true)
variable (otherCovers : ∀ x, CyclicVertex G.opposite.OpponentChecking x → otherCore x = true)

/-- 各自分番で保存最大手を選ぶ。選択は履歴に依存してもよく、同点手を固定しない。 -/
def DepthMaximumPlan (depth : E → Nat) (self : G.MovePlan) : Prop :=
  ∀ history vertex, G.owner vertex = G.player →
    ∃ edge ∈ ctx.indexed.outgoing vertex,
      self.choose history vertex = ctx.indexed.move edge ∧
      ∀ other ∈ ctx.indexed.outgoing vertex,
        OutputPreference.encoded
          (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
          (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
          (ctx.generatedValue otherCore vertex) other ≤
        OutputPreference.encoded
          (fun e => moveValue (ctx.generatedValue otherCore) (ctx.indexed.move e))
          (ctx.generatedPreferred atTop otherCore leaves covers otherCovers depth vertex)
          (ctx.generatedValue otherCore vertex) edge

/-- depthは任意の自然数表でよい。安全候補内の符号別選好は値の保証を壊さない。 -/
theorem depth_maximum_lower (depth : E → Nat) (self opponent : G.MovePlan)
    (selected : ctx.DepthMaximumPlan atTop otherCore leaves covers otherCovers depth self)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff :=
  ctx.generated_output_lower atTop otherCore leaves covers otherCovers depth
    self opponent selected root payoff result

/-- 正の保証値から通常千日手の利得0に至ることはない。相手の応手は制限しない。 -/
theorem depth_positive_no_draw (depth : E → Nat) (self opponent : G.MovePlan)
    (selected : ctx.DepthMaximumPlan atTop otherCore leaves covers otherCovers depth self)
    (root : V) (positive : 0 < ctx.generatedValue otherCore root)
    (result : G.TerminalResult (G.combinePlans self opponent) root 0) : False := by
  have lower := ctx.depth_maximum_lower atTop otherCore leaves covers otherCovers
    depth self opponent selected root 0 result
  omega

/-- depthの大小にかかわらず、-mateより良い保証値から自分の反則負けには至らない。 -/
theorem depth_no_mate_loss (depth : E → Nat) (self opponent : G.MovePlan)
    (selected : ctx.DepthMaximumPlan atTop otherCore leaves covers otherCovers depth self)
    (root : V) (better : -G.mate < ctx.generatedValue otherCore root)
    (result : G.TerminalResult (G.combinePlans self opponent) root (-G.mate)) : False := by
  have lower := ctx.depth_maximum_lower atTop otherCore leaves covers otherCovers
    depth self opponent selected root (-G.mate) result
  omega

/-- 有限グラフでは単なる「終局したら」の条件文でなく、正利得の終局が実在する。
相手の連続王手による反則勝ちは許すため、leafへの到達そのものとは区別する。 -/
theorem depth_positive_terminates (depth : E → Nat) (self opponent : G.MovePlan)
    (selected : ctx.DepthMaximumPlan atTop otherCore leaves covers otherCovers depth self)
    (vertices : List V) (covered : ∀ x, x ∈ vertices)
    (root : V) (positive : 0 < ctx.generatedValue otherCore root) :
    ∃ payoff, ∃ result : G.TerminalResult (G.combinePlans self opponent) root payoff,
      0 < payoff ∧ result.plies ≤ 3 * vertices.length := by
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered
    (G.combinePlans self opponent) root
  have lower := ctx.depth_maximum_lower atTop otherCore leaves covers otherCovers
    depth self opponent selected root payoff result
  exact ⟨payoff, result, by omega, TerminalResult.plies_bound G vertices covered result⟩

/-- 上限で丸めたdepthにも同じ保証が成立する。丸め後の値がrankである必要はない。 -/
theorem capped_depth_positive_no_draw (depth : E → Nat) (cap : Nat)
    (self opponent : G.MovePlan)
    (selected : ctx.DepthMaximumPlan atTop otherCore leaves covers otherCovers
      (fun edge => min (depth edge) cap) self)
    (root : V) (positive : 0 < ctx.generatedValue otherCore root)
    (result : G.TerminalResult (G.combinePlans self opponent) root 0) : False :=
  ctx.depth_positive_no_draw atTop otherCore leaves covers otherCovers
    (fun edge => min (depth edge) cap) self opponent selected root positive result

end PetaProof.ThresholdGame.QueueContext
