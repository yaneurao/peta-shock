import PetaProof.ValueStratumFilter

/-! 0の通常循環から20へ進む辺を持つ、二層・両視点の候補表を検査する。 -/
namespace PetaProof.ValueStratumExamples

open ThresholdGame

inductive Node where
  | a | b | c | d
  deriving DecidableEq

def owner : Node → Bool | .a | .c => false | .b | .d => true

def legal : Node → Move Node → Prop
  | .a, move => move = .leaf 0 ∨ move = .node .b
  | .b, move => move = .node .a ∨ move = .node .c
  | .c, move => move = .leaf 20 ∨ move = .node .d
  | .d, move => move = .leaf 20

def game : ThresholdGame Node where
  legal := legal
  owner := owner
  check := fun _ _ => False
  player := false
  threshold := 1
  mate := 100
  positive := by decide
  bounded := by decide
  alternating := by intro vertex child law; cases vertex <;> cases child <;> simp_all [legal, owner]
  nonempty_moves := by
    intro vertex
    cases vertex with
    | a => exact ⟨.leaf 0, Or.inl rfl⟩
    | b => exact ⟨.node .a, Or.inl rfl⟩
    | c => exact ⟨.leaf 20, Or.inl rfl⟩
    | d => exact ⟨.leaf 20, rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def value : Node → Int | .a | .b => 0 | .c | .d => 20

def table : game.ValueRankTable where
  value := value
  bounded := by intro vertex; cases vertex <;> decide
  rank := fun bound vertex => if bound = 0 then
    (match vertex with | .a => 0 | .b => 1 | .c => 1000 | .d => 1000)
    else (match vertex with | .c => 1 | .d => 0 | _ => 777)

def oppositeTable : game.opposite.ValueRankTable where
  value := fun vertex => -value vertex
  bounded := by intro vertex; cases vertex <;> decide
  rank := fun bound vertex => if bound = 0 then
    (match vertex with | .a => 1 | .b => 0 | _ => 1000)
    else (match vertex with | .c => 1 | .d => 0 | _ => 777)

theorem cross_level_allowed : table.admissibleMove .b (.node .c) := by
  simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition, table, value, game, legal]

theorem cross_level_rank_increases : table.rank 0 .b < table.rank 0 .c := by decide

theorem quiet_same_level_reset : table.admissibleMove .a (.node .b) ∧ table.rank 0 .a < table.rank 0 .b := by
  simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition, ValueRankTable.sameLevelCondition,
    table, value, game, legal, owner]

theorem opponent_cannot_drop_value : ¬ oppositeTable.admissibleMove .b (.node .c) := by
  simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition, oppositeTable, value]

theorem all_replies : table.AllReplies := by
  intro vertex move other law
  cases vertex with
  | a => cases other rfl
  | c => cases other rfl
  | b =>
    rcases law with rfl | rfl <;>
      simp [ValueRankTable.candidateCondition, ValueRankTable.sameLevelCondition, table, value, game, owner]
  | d => cases law; change 20 ≤ 20; omega

theorem opposite_replies : oppositeTable.AllReplies := by
  intro vertex move other law
  cases vertex with
  | a =>
    change legal .a move.negate at law
    cases move with
    | node child =>
      have same : child = .b := by simpa [legal, Move.negate] using law
      subst child
      simp [ValueRankTable.candidateCondition, ValueRankTable.sameLevelCondition,
        oppositeTable, value, game, opposite, owner]
    | leaf score =>
      have same : score = 0 := by simpa [legal, Move.negate] using law
      subst score
      change (0 : Int) ≤ 0
      omega
  | c =>
    change legal .c move.negate at law
    cases move with
    | node child =>
      have same : child = .d := by simpa [legal, Move.negate] using law
      subst child
      simp [ValueRankTable.candidateCondition, ValueRankTable.sameLevelCondition,
        oppositeTable, value, game, opposite, owner]
    | leaf score =>
      have same : -score = 20 := by simpa [legal, Move.negate] using law
      have eq : score = -20 := by omega
      subst score
      change (-20 : Int) ≤ -20
      omega
  | b => exact False.elim (other rfl)
  | d => exact False.elim (other rfl)

/-- aとcでは履歴に応じて直接leafと内部手を切り替える。 -/
def mixedPlan : game.MovePlan where
  choose := fun history vertex => match vertex with
    | .a => if history.length % 2 = 0 then .leaf 0 else .node .b
    | .b => .node .a
    | .c => if history.length % 2 = 0 then .leaf 20 else .node .d
    | .d => .leaf 20
  legal := by
    intro history vertex
    cases vertex with
    | a => change legal .a (if _ then _ else _); split <;> simp [legal]
    | b => exact Or.inl rfl
    | c => change legal .c (if _ then _ else _); split <;> simp [legal]
    | d => rfl

theorem mixed_admissible : table.AdmissiblePlan mixedPlan := by
  intro history vertex own
  cases vertex with
  | a =>
    change table.admissibleMove .a (if _ then _ else _)
    split <;> simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition,
      ValueRankTable.sameLevelCondition, table, value, game, legal, owner]
  | b => cases own
  | c =>
    change table.admissibleMove .c (if _ then _ else _)
    split <;> simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition,
      ValueRankTable.sameLevelCondition, table, value, game, legal, owner]
  | d => cases own

theorem opponent_admissible : oppositeTable.AdmissiblePlan mixedPlan.opposite := by
  intro history vertex own
  cases vertex with
  | a => cases own
  | b =>
    change oppositeTable.admissibleMove .b (.node .a)
    simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition,
      ValueRankTable.sameLevelCondition, oppositeTable, value, game, opposite, legal, owner, Move.negate]
  | c => cases own
  | d =>
    change oppositeTable.admissibleMove .d (.leaf (-20))
    simp [ValueRankTable.admissibleMove, ValueRankTable.candidateCondition,
      oppositeTable, value, game, opposite, legal, owner, Move.negate]

theorem mixed_lower (opponent : game.MovePlan) (root : Node) (payoff : Int)
    (result : game.TerminalResult (game.combinePlans mixedPlan opponent) root payoff) : value root ≤ payoff :=
  table.terminal_lower all_replies mixedPlan opponent mixed_admissible root payoff result

theorem both_exact (root : Node) (payoff : Int)
    (result : game.TerminalResult (game.combinePlans mixedPlan mixedPlan) root payoff) : payoff = value root :=
  table.terminal_exact oppositeTable (fun _ => rfl) all_replies opposite_replies mixedPlan mixedPlan
    mixed_admissible opponent_admissible root payoff result

theorem values_exact (root : Node) : game.ExactValue root (value root) := by
  refine ⟨⟨mixedPlan, fun opponent payoff result => mixed_lower opponent root payoff result⟩,
    mixedPlan, ?_⟩
  intro self payoff result
  have reflected := TerminalResult.opposite game result
  rw [game.opposite_combine] at reflected
  have upper := oppositeTable.terminal_lower opposite_replies mixedPlan.opposite self.opposite
    opponent_admissible root (-payoff) reflected
  change -value root ≤ -payoff at upper
  omega

inductive Edge where
  | aLeaf | aNext | bReturn | bUp | cLeaf | cNext | dLeaf
  deriving DecidableEq

def outgoing : Node → List Edge
  | .a => [.aLeaf, .aNext]
  | .b => [.bReturn, .bUp]
  | .c => [.cLeaf, .cNext]
  | .d => [.dLeaf]

def source : Edge → Node
  | .aLeaf | .aNext => .a
  | .bReturn | .bUp => .b
  | .cLeaf | .cNext => .c
  | .dLeaf => .d

def edgeMove : Edge → Move Node
  | .aLeaf => .leaf 0
  | .aNext => .node .b
  | .bReturn => .node .a
  | .bUp => .node .c
  | .cLeaf | .dLeaf => .leaf 20
  | .cNext => .node .d

def indexed : game.IndexedMoves Edge where
  outgoing := outgoing
  source := source
  move := edgeMove
  unique := by intro vertex; cases vertex <;> decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [outgoing, source]
  legal := by intro vertex edge member; cases vertex <;> cases edge <;> simp_all [outgoing, edgeMove, legal, game]
  covers := by
    intro vertex move law
    cases vertex with
    | a =>
      rcases law with rfl | rfl
      · exact ⟨.aLeaf, by decide, rfl⟩
      · exact ⟨.aNext, by decide, rfl⟩
    | b =>
      rcases law with rfl | rfl
      · exact ⟨.bReturn, by decide, rfl⟩
      · exact ⟨.bUp, by decide, rfl⟩
    | c =>
      rcases law with rfl | rfl
      · exact ⟨.cLeaf, by decide, rfl⟩
      · exact ⟨.cNext, by decide, rfl⟩
    | d => exact ⟨.dLeaf, by decide, law.symm⟩

def input : ValueStratumFilter.Input table Edge where
  indexed := indexed
  checked := fun _ _ => false
  checked_correct := by intro _ _; simp [game]

theorem filtered_rows : input.kept .a = [.aLeaf, .aNext] ∧ input.kept .b = [.bReturn, .bUp] ∧
    input.kept .c = [.cLeaf, .cNext] ∧ input.kept .d = [.dLeaf] := by decide

theorem filter_cost : ([Node.a, .b, .c, .d].map (fun vertex => (input.counted vertex).2)).sum = 14 := by decide

theorem filter_bound : ([Node.a, .b, .c, .d].map (fun vertex => (input.counted vertex).2)).sum ≤ 14 :=
  input.total_bound _

end PetaProof.ValueStratumExamples
