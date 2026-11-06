import PetaProof.SignedBounds

/-!
合法手・手番・王手・利得を変えず、判定閾値だけを変更する。
戦略と最初の終局を双方向に移し、異なる閾値での保証を同じ元のゲーム上で比較する。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

def retune (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) : ThresholdGame V :=
  { G with threshold := t, positive := positive, bounded := bounded }

namespace MovePlan

variable {G} {t : Int} {positive : 0 < t} {bounded : t ≤ G.mate}

def retune (plan : G.MovePlan) : (G.retune t positive bounded).MovePlan where
  choose := plan.choose
  legal := plan.legal

def restore (plan : (G.retune t positive bounded).MovePlan) : G.MovePlan where
  choose := plan.choose
  legal := plan.legal

@[simp] theorem restore_retune (plan : G.MovePlan) :
    (plan.retune (t := t) (positive := positive) (bounded := bounded)).restore = plan := by
  apply ext
  rfl

@[simp] theorem retune_restore (plan : (G.retune t positive bounded).MovePlan) :
    plan.restore.retune = plan := by
  apply ext
  rfl

end MovePlan

theorem retune_combine (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate) (self opponent : G.MovePlan) :
    (G.combinePlans self opponent).retune =
      (G.retune t positive bounded).combinePlans self.retune opponent.retune := by
  apply MovePlan.ext
  rfl

theorem restore_combine (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (self opponent : (G.retune t positive bounded).MovePlan) :
    ((G.retune t positive bounded).combinePlans self opponent).restore =
      G.combinePlans self.restore opponent.restore := by
  apply MovePlan.ext
  rfl

def TerminalResult.retune [DecidableEq V] (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    {plan : G.MovePlan} {root : V} {payoff : Int} (result : G.TerminalResult plan root payoff) :
    (G.retune t positive bounded).TerminalResult plan.retune root payoff := by
  cases result with
  | leaf trace selected quiet score legal last =>
    exact TerminalResult.leaf (G := G.retune t positive bounded) (plan := plan.retune)
      trace selected quiet payoff legal last
  | repetition trace selected earliest stem edge back suffix original first fourth =>
    exact TerminalResult.repetition (G := G.retune t positive bounded) (plan := plan.retune)
      trace selected earliest stem edge back suffix original first fourth

def TerminalResult.restore [DecidableEq V] (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    {plan : (G.retune t positive bounded).MovePlan} {root : V} {payoff : Int}
    (result : (G.retune t positive bounded).TerminalResult plan root payoff) :
    G.TerminalResult plan.restore root payoff := by
  cases result with
  | leaf trace selected quiet score legal last =>
    exact TerminalResult.leaf (G := G) (plan := plan.restore) trace selected quiet payoff legal last
  | repetition trace selected earliest stem edge back suffix original first fourth =>
    exact TerminalResult.repetition (G := G) (plan := plan.restore)
      trace selected earliest stem edge back suffix original first fourth

theorem lower_retune_iff [DecidableEq V] (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (root : V) (bound : Int) :
    (G.retune t positive bounded).LowerGuarantee root bound ↔ G.LowerGuarantee root bound := by
  constructor
  · rintro ⟨self, lower⟩
    refine ⟨self.restore, ?_⟩
    intro opponent payoff result
    have moved := TerminalResult.retune G t positive bounded result
    rw [G.retune_combine, MovePlan.retune_restore] at moved
    exact lower opponent.retune payoff moved
  · rintro ⟨self, lower⟩
    refine ⟨self.retune, ?_⟩
    intro opponent payoff result
    have moved := TerminalResult.restore G t positive bounded result
    rw [G.restore_combine, MovePlan.restore_retune] at moved
    exact lower opponent.restore payoff moved

theorem upper_retune_iff [DecidableEq V] (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (root : V) (bound : Int) :
    (G.retune t positive bounded).UpperGuarantee root bound ↔ G.UpperGuarantee root bound := by
  constructor
  · rintro ⟨opponent, upper⟩
    refine ⟨opponent.restore, ?_⟩
    intro self payoff result
    have moved := TerminalResult.retune G t positive bounded result
    rw [G.retune_combine, MovePlan.retune_restore] at moved
    exact upper self.retune payoff moved
  · rintro ⟨opponent, upper⟩
    refine ⟨opponent.retune, ?_⟩
    intro self payoff result
    have moved := TerminalResult.restore G t positive bounded result
    rw [G.restore_combine, MovePlan.restore_retune] at moved
    exact upper self.restore payoff moved

/-- 閾値を変えたゲームの勝敗を、元のゲームの整数下限として表す。 -/
theorem retune_winning_iff [DecidableEq V] (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (root : V) : (G.retune t positive bounded).FourfoldWinning root ↔ G.LowerGuarantee root t :=
  G.lower_retune_iff t positive bounded root t

/-- 各正閾値の反証を、同じ元のゲームの整数上限へ戻す。 -/
theorem upper_of_not_lower [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (t : Int) (positive : 0 < t) (bounded : t ≤ G.mate)
    (losing : ¬ G.LowerGuarantee root t) : G.UpperGuarantee root (t - 1) := by
  have negative := (G.retune t positive bounded).upper_of_not_fourfold vertices covered root
    (fun winning => losing ((G.retune_winning_iff t positive bounded root).mp winning))
  exact (G.upper_retune_iff t positive bounded root (t - 1)).mp negative

end PetaProof.ThresholdGame
