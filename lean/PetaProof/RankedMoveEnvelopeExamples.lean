import PetaProof.RankedMoveFilter

/-! 個別には安全な二つの方策も、別々の順位のまま合併すると通常千日手へ逃げられる。 -/
namespace PetaProof.RankedMoveEnvelopeExamples

open ThresholdGame

inductive Node where
  | a | b | c | d
  deriving DecidableEq

def owner : Node → Bool | .a | .c => false | .b | .d => true
def next : Node → Node | .a => .b | .b => .c | .c => .d | .d => .a
def legal (vertex : Node) (move : Move Node) : Prop :=
  move = .node (next vertex) ∨ (owner vertex = false ∧ move = .leaf 20)

def game : ThresholdGame Node where
  legal := legal
  owner := owner
  check := fun _ _ => False
  player := false
  threshold := 20
  mate := 100
  positive := by decide
  bounded := by decide
  alternating := by intro vertex child law; cases vertex <;> cases child <;> simp_all [legal, next, owner]
  nonempty_moves := fun vertex => ⟨.node (next vertex), Or.inl rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def choiceOne : Node → Move Node | .c => .leaf 20 | vertex => .node (next vertex)
def choiceTwo : Node → Move Node | .a => .leaf 20 | vertex => .node (next vertex)
def rankOne : Node → Nat | .a => 3 | .b => 2 | .c => 1 | .d => 4
def rankTwo : Node → Nat | .a => 1 | .b => 4 | .c => 3 | .d => 2

def regionOne : game.RankedRegion (fun _ => True) where
  choice := choiceOne
  rank := rankOne
  stage := 4
  rank_bound := by intro vertex _; cases vertex <;> decide
  chosen_legal := by intro vertex _ _; cases vertex <;> simp [game, legal, choiceOne, next, owner]
  closed := by
    intro vertex _ move follows
    cases move with
    | node child => trivial
    | leaf score =>
      have leafLegal := follows.1
      change 20 ≤ score
      cases vertex <;> simp [game, legal, owner, next] at leafLegal <;> omega
  decreasing := by
    intro vertex child _ follows
    cases vertex <;> cases child <;> simp_all [Follows, game, legal, owner, next, choiceOne, rankOne]
  opponent_strict := by
    intro vertex child _ follows other _
    cases vertex <;> cases child <;> simp_all [Follows, game, legal, owner, next, choiceOne, rankOne]

def regionTwo : game.RankedRegion (fun _ => True) where
  choice := choiceTwo
  rank := rankTwo
  stage := 4
  rank_bound := by intro vertex _; cases vertex <;> decide
  chosen_legal := by intro vertex _ _; cases vertex <;> simp [game, legal, choiceTwo, next, owner]
  closed := by
    intro vertex _ move follows
    cases move with
    | node child => trivial
    | leaf score =>
      have leafLegal := follows.1
      change 20 ≤ score
      cases vertex <;> simp [game, legal, owner, next] at leafLegal <;> omega
  decreasing := by
    intro vertex child _ follows
    cases vertex <;> cases child <;> simp_all [Follows, game, legal, owner, next, choiceTwo, rankTwo]
  opponent_strict := by
    intro vertex child _ follows other _
    cases vertex <;> cases child <;> simp_all [Follows, game, legal, owner, next, choiceTwo, rankTwo]

inductive Edge where
  | aNext | aLeaf | bNext | cNext | cLeaf | dNext
  deriving DecidableEq

def outgoing : Node → List Edge
  | .a => [.aNext, .aLeaf]
  | .b => [.bNext]
  | .c => [.cNext, .cLeaf]
  | .d => [.dNext]

def source : Edge → Node
  | .aNext | .aLeaf => .a
  | .bNext => .b
  | .cNext | .cLeaf => .c
  | .dNext => .d

def move : Edge → Move Node
  | .aLeaf | .cLeaf => .leaf 20
  | edge => .node (next (source edge))

def indexed : game.IndexedMoves Edge where
  outgoing := outgoing
  source := source
  move := move
  unique := by intro vertex; cases vertex <;> decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [outgoing, source]
  legal := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [game, legal, outgoing, move, source, owner, next]
  covers := by
    intro vertex candidate law
    cases vertex with
    | a =>
      rcases law with rfl | ⟨_, rfl⟩
      · exact ⟨.aNext, by decide, rfl⟩
      · exact ⟨.aLeaf, by decide, rfl⟩
    | b =>
      have same : candidate = .node .c := by simpa [game, legal, owner, next] using law
      exact ⟨.bNext, by decide, same.symm⟩
    | c =>
      rcases law with rfl | ⟨_, rfl⟩
      · exact ⟨.cNext, by decide, rfl⟩
      · exact ⟨.cLeaf, by decide, rfl⟩
    | d =>
      have same : candidate = .node .a := by simpa [game, legal, owner, next] using law
      exact ⟨.dNext, by decide, same.symm⟩

def inputOne : RankedMoveFilter.Input regionOne Edge where
  indexed := indexed
  member := fun _ => true
  member_correct := by intro _; simp
  checked := fun _ _ => false
  checked_correct := by intro _ _; simp [game]

def inputTwo : RankedMoveFilter.Input regionTwo Edge where
  indexed := indexed
  member := fun _ => true
  member_correct := by intro _; simp
  checked := fun _ _ => false
  checked_correct := by intro _ _; simp [game]

theorem one_candidates : inputOne.kept .a = [.aNext, .aLeaf] ∧ inputOne.kept .c = [.cLeaf] := by decide
theorem two_candidates : inputTwo.kept .a = [.aLeaf] ∧ inputTwo.kept .c = [.cNext, .cLeaf] := by decide
theorem opponents_unchanged : inputOne.kept .b = [.bNext] ∧ inputOne.kept .d = [.dNext] := by decide
theorem one_filter_eleven : ([Node.a, .b, .c, .d].map (fun vertex => (inputOne.counted vertex).2)).sum = 11 := by decide
theorem one_filter_bound : ([Node.a, .b, .c, .d].map (fun vertex => (inputOne.counted vertex).2)).sum ≤ 12 :=
  inputOne.total_bound _

theorem first_policy_wins (root : Node) : game.FourfoldWinning root := regionOne.fourfold_winning root trivial
theorem second_policy_wins (root : Node) : game.FourfoldWinning root := regionTwo.fourfold_winning root trivial

def mixedPlan : game.MovePlan where
  choose := fun history vertex => match vertex with
    | .a => if history.length % 2 = 0 then .leaf 20 else .node .b
    | .c => .leaf 20
    | _ => .node (next vertex)
  legal := by
    intro history vertex
    cases vertex with
    | a =>
      change legal .a (if history.length % 2 = 0 then .leaf 20 else .node .b)
      by_cases even : history.length % 2 = 0 <;> simp [even, legal, owner, next]
    | b => exact Or.inl rfl
    | c => exact Or.inr ⟨rfl, rfl⟩
    | d => exact Or.inl rfl

theorem history_changes_choice : mixedPlan.choose [] .a = .leaf 20 ∧ mixedPlan.choose [.a] .a = .node .b := by
  exact ⟨rfl, rfl⟩

theorem mixedPlan_admissible : regionOne.AdmissiblePlan mixedPlan := by
  intro history vertex _ own
  cases vertex with
  | a =>
    change regionOne.admissibleMove .a (if history.length % 2 = 0 then .leaf 20 else .node .b)
    split
    · exact inputOne.kept_sound .a .aLeaf (by decide)
    · exact inputOne.kept_sound .a .aNext (by decide)
  | b => cases own
  | c => exact inputOne.kept_sound .c .cLeaf (by decide)
  | d => cases own

theorem mixedPlan_guarantees (opponent : game.MovePlan) (root : Node) (payoff : Int)
    (result : game.TerminalResult (game.combinePlans mixedPlan opponent) root payoff) : 20 ≤ payoff :=
  regionOne.admissible_plan_guarantee mixedPlan opponent mixedPlan_admissible root trivial payoff result

def cyclicPlan : game.MovePlan where
  choose := fun _ vertex => .node (next vertex)
  legal := fun _ _ => Or.inl rfl

def nextEdge (vertex : Node) : game.LegalNode vertex (next vertex) := Or.inl rfl

def dToA : Walk game.LegalNode Node.d Node.a := .cons (nextEdge .d) (.nil Node.a)
def cToA : Walk game.LegalNode Node.c Node.a := .cons (nextEdge .c) dToA

def backToA : Walk game.LegalNode .b .a :=
  .cons (nextEdge .b) cToA

def lap : Walk game.LegalNode .a .a := .cons (nextEdge .a) backToA

def backThree : Walk game.LegalNode .b .a :=
  backToA.append (lap.append lap)

def traceThree : Walk game.LegalNode .a .a := .cons (nextEdge .a) backThree

theorem cyclic_payoff_zero : game.repetitionValue (show game.LegalNode .a .b from Or.inl rfl) backThree = 0 := by
  have no_own : ¬ traceThree.Every (fun v w => game.owner v = game.player → game.check v w) := by
    intro all
    exact all.1 rfl
  have no_other : ¬ traceThree.Every (fun v w => game.owner v ≠ game.player → game.check v w) := by
    intro all
    exact all.2.1 (by decide)
  unfold traceThree at no_own no_other
  simp only [repetitionValue, if_neg no_own, if_neg no_other]

noncomputable def cyclicTerminal : game.TerminalResult (game.combinePlans cyclicPlan cyclicPlan) .a 0 := by
  have result : game.TerminalResult (game.combinePlans cyclicPlan cyclicPlan) .a
      (game.repetitionValue (show game.LegalNode .a .b from Or.inl rfl) backThree) :=
    .repetition traceThree (by simp [traceThree, backThree, backToA, cToA, dToA, lap, Walk.append, Walk.Selected, cyclicPlan, combinePlans, next])
      (by intro vertex; cases vertex <;> decide) (.nil Node.a) (nextEdge .a) backThree (.nil Node.a) rfl (by decide) (by decide)
  rw [cyclic_payoff_zero] at result
  exact result

theorem union_contains_cycle (history : List Node) (vertex : Node) (own : game.owner vertex = game.player) :
    ∃ edge, (edge ∈ inputOne.kept vertex ∨ edge ∈ inputTwo.kept vertex) ∧
      cyclicPlan.choose history vertex = indexed.move edge := by
  cases vertex with
  | a => exact ⟨.aNext, Or.inl (by decide), rfl⟩
  | b => cases own
  | c => exact ⟨.cNext, Or.inr (by decide), rfl⟩
  | d => cases own

theorem union_does_not_guarantee : ¬ ∀ payoff,
    game.TerminalResult (game.combinePlans cyclicPlan cyclicPlan) .a payoff → 20 ≤ payoff := by
  intro guarantee
  have impossible := guarantee 0 cyclicTerminal
  omega

end PetaProof.RankedMoveEnvelopeExamples
