import PetaProof.RefutationMoveFilter

/-! 非王手での順位回復、通常千日手、王手循環の除外、0と負の下限を検査する。 -/
namespace PetaProof.RefutationMoveEnvelopeExamples

open ThresholdGame

/-- 二頂点の抽象ゲーム。trueにはleaf出口があり、その内部手だけ王手に変更できる。 -/
def game (score : Nat) (checking : Bool) : ThresholdGame Bool where
  legal := fun vertex move => move = .node (!vertex) ∨ (vertex = true ∧ move = .leaf (Int.ofNat score))
  owner := id
  player := false
  check := fun vertex _ => vertex = true ∧ checking = true
  threshold := Int.ofNat score + 1
  mate := Int.ofNat score + 100
  positive := by have nonneg : 0 ≤ Int.ofNat score := Int.ofNat_zero_le score; omega
  bounded := by omega
  alternating := by
    intro vertex child legal
    have same : child = !vertex := by simpa using legal
    subst child
    cases vertex <;> decide
  nonempty_moves := fun vertex => ⟨.node (!vertex), Or.inl rfl⟩
  no_mutual_cycle := by
    intro a b edge back
    have first : a = true := edge.2.1
    have child : b = !a := by simpa using edge.1
    subst a
    subst b
    cases back with
    | cons next _ => cases next.2.1

def region (score : Nat) (checking : Bool) : (game score checking).RefutationRegion (fun _ => True) where
  response := fun vertex => if vertex then .leaf (Int.ofNat score) else .node true
  chosen_legal := by
    intro vertex _ other
    cases vertex with
    | false => exact False.elim (other rfl)
    | true => exact Or.inr ⟨rfl, rfl⟩
  closed := by
    intro vertex _ move reply
    cases move with
    | node child => trivial
    | leaf value =>
      have leaf : vertex = true ∧ value = Int.ofNat score := by simpa [game] using reply.1
      have same := leaf.2
      change value < Int.ofNat score + 1
      omega
  rank := fun vertex => if vertex then 0 else 1
  strict_checking := by
    intro vertex child _ reply _
    have same : child = !vertex := by simpa [game] using reply.1
    subst child
    cases vertex with
    | false => decide
    | true =>
      have impossible := reply.2 (by change true ≠ false; decide)
      cases impossible

inductive Edge where
  | fNext | tNext | tLeaf
  deriving DecidableEq

def move (score : Nat) : Edge → Move Bool
  | .fNext => .node true
  | .tNext => .node false
  | .tLeaf => .leaf (Int.ofNat score)

def indexed (score : Nat) (checking : Bool) : (game score checking).IndexedMoves Edge where
  outgoing := fun vertex => if vertex then [.tNext, .tLeaf] else [.fNext]
  source := fun edge => match edge with | .fNext => false | _ => true
  move := move score
  unique := by intro vertex; cases vertex <;> decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all
  legal := by
    intro vertex edge member
    cases vertex <;> cases edge <;> simp_all [game, move]
  covers := by
    intro vertex action legal
    cases vertex with
    | false =>
      have same : action = .node true := by simpa [game] using legal
      exact ⟨.fNext, by simp, same.symm⟩
    | true =>
      rcases legal with rfl | ⟨_, rfl⟩
      · exact ⟨.tNext, by simp, rfl⟩
      · exact ⟨.tLeaf, by simp, rfl⟩

def input (score : Nat) (checking : Bool) : RefutationMoveFilter.Input (region score checking) Edge where
  indexed := indexed score checking
  member := fun _ => true
  member_correct := by intro _; simp
  checked := fun vertex _ => vertex && checking
  checked_correct := by intro vertex child; cases vertex <;> cases checking <;> simp [game]

theorem quiet_keeps_both (score : Nat) : (input score false).kept true = [.tNext, .tLeaf] := by
  simp [RefutationMoveFilter.Input.kept, RefutationMoveFilter.Input.conditionFlag,
    input, indexed, move, game, region, show (score : Int) < (score : Int) + 1 by omega]

theorem checking_keeps_only_exit (score : Nat) : (input score true).kept true = [.tLeaf] := by
  simp [RefutationMoveFilter.Input.kept, RefutationMoveFilter.Input.conditionFlag,
    input, indexed, move, game, region, show (score : Int) < (score : Int) + 1 by omega]

theorem all_opponent_replies_kept (score : Nat) (checking : Bool) :
    (input score checking).kept false = [.fNext] := by
  simp [RefutationMoveFilter.Input.kept, RefutationMoveFilter.Input.conditionFlag,
    input, indexed, move, game, region]

theorem quiet_cost (score : Nat) :
    ((input score false).counted false).2 + ((input score false).counted true).2 = 6 := by
  rw [(input score false).counted_spec false |>.2, (input score false).counted_spec true |>.2,
    quiet_keeps_both, all_opponent_replies_kept]
  rfl

theorem checking_cost (score : Nat) :
    ((input score true).counted false).2 + ((input score true).counted true).2 = 5 := by
  rw [(input score true).counted_spec false |>.2, (input score true).counted_spec true |>.2,
    checking_keeps_only_exit, all_opponent_replies_kept]
  rfl

/-- 下限側の手は履歴により通常循環とleaf出口を切り替える。 -/
def mixedPlan (score : Nat) : (game score false).opposite.MovePlan where
  choose := fun history vertex =>
    if vertex = true ∧ 4 ≤ history.length then .leaf (-Int.ofNat score) else .node (!vertex)
  legal := by
    intro history vertex
    change (game score false).legal vertex
      ((if vertex = true ∧ 4 ≤ history.length then .leaf (-Int.ofNat score) else .node (!vertex) : Move Bool).negate)
    split
    · rename_i exit
      exact Or.inr ⟨exit.1, by simp [Move.negate]⟩
    · exact Or.inl rfl

theorem mixedPlan_candidates (score : Nat) :
    (region score false).AdmissiblePlan (mixedPlan score).unopposite := by
  intro history vertex _ other
  have turn : vertex = true := by cases vertex <;> simp_all [game]
  subst vertex
  change (region score false).admissibleMove true
    ((if true = true ∧ 4 ≤ history.length then .leaf (-Int.ofNat score) else .node false : Move Bool).negate)
  split
  · simp [ThresholdGame.RefutationRegion.admissibleMove,
      ThresholdGame.RefutationRegion.candidateCondition, Move.negate, game]
    omega
  · simp [ThresholdGame.RefutationRegion.admissibleMove,
      ThresholdGame.RefutationRegion.candidateCondition, Move.negate, game, region]

theorem mixedPlan_lower (score : Nat) (opponent : (game score false).opposite.MovePlan)
    (root : Bool) (payoff : Int)
    (result : (game score false).opposite.TerminalResult
      ((game score false).opposite.combinePlans (mixedPlan score) opponent) root payoff) :
    -Int.ofNat score ≤ payoff := by
  have bound := (region score false).admissible_plan_opposite_lower (mixedPlan score) opponent
    (mixedPlan_candidates score) root trivial payoff result
  change 1 - (Int.ofNat score + 1) ≤ payoff at bound
  omega

theorem zero_lower (opponent : (game 0 false).opposite.MovePlan) (root : Bool) (payoff : Int)
    (result : (game 0 false).opposite.TerminalResult
      ((game 0 false).opposite.combinePlans (mixedPlan 0) opponent) root payoff) : 0 ≤ payoff :=
  mixedPlan_lower 0 opponent root payoff result

theorem negative_lower (opponent : (game 9 false).opposite.MovePlan) (root : Bool) (payoff : Int)
    (result : (game 9 false).opposite.TerminalResult
      ((game 9 false).opposite.combinePlans (mixedPlan 9) opponent) root payoff) : -9 ≤ payoff :=
  mixedPlan_lower 9 opponent root payoff result

theorem actual_history_switch (score : Nat) :
    (mixedPlan score).choose [] true = .node false ∧
      (mixedPlan score).choose [false, true, false, true] true = .leaf (-Int.ofNat score) := by
  constructor <;> rfl

/-- 非王手で0から1へ戻る辺を許す。全辺非増加という条件ではこの安全な辺を失う。 -/
theorem quiet_reset (score : Nat) :
    (region score false).rank true < (region score false).rank false ∧
      Edge.tNext ∈ (input score false).kept true := by
  constructor
  · change 0 < 1; decide
  · rw [quiet_keeps_both]; simp

def cyclePlan (score : Nat) : (game score false).MovePlan where
  choose := fun _ vertex => .node (!vertex)
  legal := fun _ _ => Or.inl rfl

theorem cycle_candidates (score : Nat) : (region score false).AdmissiblePlan (cyclePlan score) := by
  intro history vertex _ other
  have turn : vertex = true := by cases vertex <;> simp_all [game]
  subst vertex
  simp [ThresholdGame.RefutationRegion.admissibleMove,
    ThresholdGame.RefutationRegion.candidateCondition, cyclePlan, game, region]

def edge (score : Nat) (vertex : Bool) : (game score false).LegalNode vertex (!vertex) := Or.inl rfl

def back (score : Nat) : Walk (game score false).LegalNode true false :=
  .cons (edge score true) (.cons (edge score false) (.cons (edge score true)
    (.cons (edge score false) (.cons (edge score true) (.nil false)))))

def trace (score : Nat) : Walk (game score false).LegalNode false false :=
  .cons (edge score false) (back score)

theorem quiet_repetition_zero (score : Nat) :
    (game score false).repetitionValue (edge score false) (back score) = 0 := by
  classical
  simp [ThresholdGame.repetitionValue, back, Walk.Every, game]

/-- 通常循環を禁止し過ぎていないことを、最初の四回出現の終局証拠でも確認する。 -/
def drawTerminal (score : Nat) :
    (game score false).TerminalResult
      ((game score false).combinePlans (cyclePlan score) (cyclePlan score)) false 0 := by
  have result := TerminalResult.repetition (G := game score false)
    (plan := (game score false).combinePlans (cyclePlan score) (cyclePlan score))
    (trace score)
    (by simp [trace, back, Walk.Selected, combinePlans, cyclePlan])
    (by intro vertex; cases vertex <;> simp [trace, back, Walk.visits])
    (.nil false) (edge score false) (back score) (.nil false)
    (by rfl) (by simp [Walk.visits]) (by simp [back, Walk.visits])
  simpa only [quiet_repetition_zero] using result

theorem cycle_opposite_lower (score : Nat) (opponent : (game score false).opposite.MovePlan)
    (root : Bool) (payoff : Int)
    (result : (game score false).opposite.TerminalResult
      ((game score false).opposite.combinePlans (cyclePlan score).opposite opponent) root payoff) :
    -Int.ofNat score ≤ payoff := by
  have admissible : (region score false).AdmissiblePlan (cyclePlan score).opposite.unopposite := by
    intro history vertex inside other
    have same : (cyclePlan score).opposite.unopposite.choose history vertex =
        (cyclePlan score).choose history vertex := rfl
    rw [same]
    exact cycle_candidates score history vertex inside other
  have bound := (region score false).admissible_plan_opposite_lower (cyclePlan score).opposite opponent
    admissible root trivial payoff result
  change 1 - (Int.ofNat score + 1) ≤ payoff at bound
  omega

end PetaProof.RefutationMoveEnvelopeExamples
