import PetaProof.EscapeComputation

/-! 循環の出口、見かけ上の短い経路、同距離の複数手、到達不能な通常循環を検査する。 -/
namespace PetaProof.EscapeExamples

open HistoryArena

inductive Node where
  | a | b | c | f | e | t | u | exit
  deriving DecidableEq

def successors : Node → List Node
  | .a => [.b, .c, .f]
  | .b => [.exit, .a]
  | .c | .f => [.e]
  | .e => [.exit, .a]
  | .t => [.u, .exit]
  | .u => [.t]
  | .exit => [.exit]

def arena : HistoryArena Node where
  edge := fun vertex child => child ∈ successors vertex
  owner := fun vertex => match vertex with | .b | .c | .f | .t => true | _ => false
  player := false
  bad := fun _ _ => False
  moves_exist := by
    intro vertex
    cases vertex with
    | a => exact ⟨.b, by decide⟩
    | b => exact ⟨.exit, by decide⟩
    | c => exact ⟨.e, by decide⟩
    | f => exact ⟨.e, by decide⟩
    | e => exact ⟨.exit, by decide⟩
    | t => exact ⟨.u, by decide⟩
    | u => exact ⟨.t, by decide⟩
    | exit => exact ⟨.exit, by decide⟩

def vertices : List Node := [.a, .b, .c, .f, .e, .t, .u, .exit]
theorem covered (vertex : Node) : vertex ∈ vertices := by cases vertex <;> decide

/-- A,B,C,F,Eは一つの循環成分をなす。目標はこの成分の外。 -/
def outsideCore : Node → Prop
  | .t | .u | .exit => True
  | _ => False

def input : EscapeInput arena outsideCore where
  successors := successors
  edges := fun _ _ => Iff.rfl
  goal := fun vertex => match vertex with | .t | .u | .exit => true | _ => false
  goal_correct := by intro vertex; cases vertex <;> simp [outsideCore]

def exitInput : EscapeInput arena (fun vertex => vertex = .exit) where
  successors := successors
  edges := fun _ _ => Iff.rfl
  goal := fun vertex => decide (vertex = .exit)
  goal_correct := by intro vertex; simp

theorem distances : input.computedDistance vertices.length .a = some 3 ∧
    input.computedDistance vertices.length .b = some 4 ∧
    input.computedDistance vertices.length .c = some 2 ∧
    input.computedDistance vertices.length .f = some 2 ∧
    input.computedDistance vertices.length .e = some 1 ∧
    input.computedDistance vertices.length .exit = some 0 := by decide

theorem picked_moves : input.optimalNext vertices.length .a = some .c ∧
    input.optimalNext vertices.length .e = some .exit := by decide

/-- 二つの同距離手を残せる一方、見かけの近道Bは最短保証を達成しない。 -/
theorem minimizing_candidates : input.minimizingFlag vertices.length .a .c = true ∧
    input.minimizingFlag vertices.length .a .f = true ∧
    input.minimizingFlag vertices.length .a .b = false := by decide

theorem a_within_three :
    arena.escapeWithin outsideCore (input.computedStrategy vertices.length) [] 3 .a := by
  have inside : arena.escapeLayer outsideCore vertices.length .a :=
    arena.escapeLayer_complete outsideCore vertices covered 3 .a
      ((input.computedDistance_some vertices.length 3 .a).mp distances.1).2.1
  have upper := (arena.escapeRank_le_iff outsideCore vertices.length .a inside 3).mpr
    ((input.computedDistance_some vertices.length 3 .a).mp distances.1).2.1
  exact arena.escapeOptimal_guarantees outsideCore vertices covered _ (input.computedStrategy_optimal vertices covered)
    [] 3 .a inside upper

theorem a_not_within_two (strategy : arena.Strategy) (past : List Node) :
    ¬ arena.escapeWithin outsideCore strategy past 2 .a :=
  ((input.computedDistance_minimax vertices covered .a 3 distances.1).2 strategy past 2 (by decide))

theorem no_forced_exit_from_trap : exitInput.computedDistance vertices.length .t = none ∧
    exitInput.computedDistance vertices.length .u = none := by decide

theorem trap_spoiler (strategy : arena.Strategy) (n : Nat) :
    arena.play strategy (arena.escapeSpoiler (fun vertex => vertex = .exit) vertices covered) .t n ≠ .exit := by
  have outside := (exitInput.computedDistance_none vertices.length .t).mp no_forced_exit_from_trap.1
  exact arena.escapeSpoiler_avoids (fun vertex => vertex = .exit) vertices covered .t outside strategy n

end PetaProof.EscapeExamples
