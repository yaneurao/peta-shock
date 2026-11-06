import PetaProof.FiniteGame

/-!
固定プレイヤーを反転し、leafと反復の利得の符号を反転する。
盤面の手番と王手情報は変えず、同じ実際の手順を反対側から評価する。
-/

namespace PetaProof.Move

universe u
variable {V : Type u}

/-- 内部手の行き先は変えず、leafの固定プレイヤー視点の値だけを反転する。 -/
def negate : Move V → Move V
  | .node v => .node v
  | .leaf score => .leaf (-score)

@[simp] theorem negate_negate (move : Move V) : move.negate.negate = move := by
  cases move <;> simp [negate]

end PetaProof.Move

namespace PetaProof.Walk

universe u
variable {V : Type u} {R : V → V → Prop} {a b : V}

/-- 各選択のleaf値を反転しても、内部手をたどった履歴は変わらない。 -/
theorem selected_negate (trace : Walk R a b) (choose : List V → V → Move V) (past : List V)
    (selected : trace.Selected choose past) :
    trace.Selected (fun history v => (choose history v).negate) past := by
  induction trace generalizing past with
  | nil => trivial
  | cons _ tail ih =>
    refine ⟨?_, ih (past ++ [_]) selected.2⟩
    dsimp only
    rw [selected.1]
    rfl

end PetaProof.Walk

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 同じ盤面・手番・王手情報を、反対の固定プレイヤーから見た閾値ゲーム。 -/
def opposite : ThresholdGame V where
  legal := fun v m => G.legal v m.negate
  owner := G.owner
  check := G.check
  player := !G.player
  threshold := G.threshold
  mate := G.mate
  positive := G.positive
  bounded := G.bounded
  alternating := G.alternating
  nonempty_moves := by
    intro v
    obtain ⟨m, legal⟩ := G.nonempty_moves v
    exact ⟨m.negate, by simpa using legal⟩
  no_mutual_cycle := G.no_mutual_cycle

/-- 双方の連続王手条件が同時に成立する反復区間は入力前提に反する。 -/
theorem no_both_checks {a b : V} (edge : G.LegalNode a b) (back : Walk G.LegalNode b a)
    (own : (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w))
    (other : (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w)) : False := by
  classical
  have checks : (Walk.cons edge back).Every G.check :=
    (Walk.cons edge back).every_mono ((Walk.cons edge back).every_and own other) (by
      intro v w _ conditions
      by_cases turn : G.owner v = G.player
      · exact conditions.1 turn
      · exact conditions.2 turn)
  exact G.no_mutual_cycle a b ⟨edge, checks.1⟩ (back.withEvery G.check checks.2)

/-- 通常千日手は0のまま、連続王手の勝敗は先後反転で厳密に符号反転する。 -/
theorem opposite_repetitionValue {a b : V} (edge : G.LegalNode a b) (back : Walk G.LegalNode b a) :
    G.opposite.repetitionValue edge back = -G.repetitionValue edge back := by
  classical
  have excluded := G.no_both_checks edge back
  unfold repetitionValue
  dsimp only [opposite]
  simp only [Bool.eq_not, ne_eq, Classical.not_not]
  by_cases own : (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w)
  · have other : ¬ (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) :=
      fun h => excluded own h
    simp only [if_pos own, if_neg other, Int.neg_neg]
  · by_cases other : (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w)
    · simp only [if_neg own, if_pos other]
    · simp only [if_neg own, if_neg other, Int.neg_zero]

namespace MovePlan

variable {G}

theorem ext (left right : G.MovePlan) (same : left.choose = right.choose) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- 同じ指し手選択を反対視点へ移す。履歴・内部手は同じで、leafの値だけを反転する。 -/
def opposite (plan : G.MovePlan) : G.opposite.MovePlan where
  choose := fun history v => (plan.choose history v).negate
  legal := by
    intro history v
    change G.legal v (plan.choose history v).negate.negate
    simpa only [Move.negate_negate] using plan.legal history v

/-- 反対視点の戦略を元のゲームへ戻す。 -/
def unopposite (plan : G.opposite.MovePlan) : G.MovePlan where
  choose := fun history v => (plan.choose history v).negate
  legal := plan.legal

@[simp] theorem opposite_unopposite (plan : G.opposite.MovePlan) : plan.unopposite.opposite = plan := by
  apply ext
  funext history v
  exact Move.negate_negate _

end MovePlan

/-- 視点を反転した合成戦略は、自分と相手の役割を交換した合成と一致する。 -/
theorem opposite_combine (self opponent : G.MovePlan) :
    (G.combinePlans self opponent).opposite =
      G.opposite.combinePlans opponent.opposite self.opposite := by
  apply MovePlan.ext
  funext history v
  by_cases own : G.owner v = G.player
  · have other : ¬ G.owner v = !G.player := by simpa only [Bool.eq_not] using not_not_intro own
    simp only [combinePlans, MovePlan.opposite, opposite, if_pos own, if_neg other]
  · have other : G.owner v = !G.player := Bool.eq_not_of_ne own
    simp only [combinePlans, MovePlan.opposite, opposite, if_neg own, if_pos other]

/-- 最初の終局の位置と判定区間を保ったまま、実際の利得を反対視点へ移す。 -/
noncomputable def TerminalResult.opposite [DecidableEq V] {plan : G.MovePlan} {root : V} {payoff : Int}
    (result : G.TerminalResult plan root payoff) :
    G.opposite.TerminalResult plan.opposite root (-payoff) := by
  cases result with
  | leaf trace selected quiet score legal last =>
    refine TerminalResult.leaf (G := G.opposite) (plan := plan.opposite)
      trace (trace.selected_negate plan.choose [] selected) quiet (-payoff) ?_ ?_
    · change G.legal _ (.leaf (-(-payoff)))
      simpa using legal
    · change (plan.choose trace.visits _).negate = .leaf (-payoff)
      rw [last]
      rfl
  | repetition trace selected earliest stem edge back suffix original first fourth =>
    have reflected : G.opposite.TerminalResult plan.opposite root
        (G.opposite.repetitionValue edge back) :=
      TerminalResult.repetition (G := G.opposite) (plan := plan.opposite)
        trace (trace.selected_negate plan.choose [] selected) earliest
        stem edge back suffix original first fourth
    rw [G.opposite_repetitionValue] at reflected
    exact reflected

end PetaProof.ThresholdGame
