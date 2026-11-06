import PetaProof.EscapeExact

/-! 実FIFOのラベルで選ぶ最短候補を、最短保証の戦略へ接続する。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E) {arena : HistoryArena V} {target : V → Prop}

/-- 参照側の有限出辺も同じ辺ID入力から作る。距離や到達層の正解を入力しない。 -/
def referenceInput (matching : ArenaMatch input arena) (goals : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) : HistoryArena.EscapeInput arena target where
  successors := fun vertex => (input.outgoing vertex).map input.child
  edges := by intro vertex child; rw [List.mem_map]; exact (matching.edges vertex child).symm
  goal := fun vertex => decide (vertex ∈ goals)
  goal_correct := by intro vertex; simp only [decide_eq_true_eq]; exact (goals_correct vertex).symm

def minimizingFlag (goals vertices : List V) (vertex child : V) : Bool :=
  match runLabels input goals vertices vertex, runLabels input goals vertices child with
  | some parent, some next => decide (next + 1 = parent)
  | _, _ => false

def nextChild (goals vertices : List V) (vertex : V) : Option V :=
  ((input.outgoing vertex).map input.child).find? (minimizingFlag input goals vertices vertex)

theorem minimizingFlag_eq (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex child : V) : minimizingFlag input goals vertices vertex child =
      (referenceInput input matching goals goals_correct).minimizingFlag vertices.length vertex child := by
  unfold minimizingFlag HistoryArena.EscapeInput.minimizingFlag
  rw [runLabels_reference input matching goals vertices goals_correct covered (referenceInput input matching goals goals_correct) vertex,
    runLabels_reference input matching goals vertices goals_correct covered (referenceInput input matching goals goals_correct) child]
  rfl

theorem nextChild_eq (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) : nextChild input goals vertices vertex =
      (referenceInput input matching goals goals_correct).optimalNext vertices.length vertex := by
  apply congrArg (fun flag : V → Bool => ((input.outgoing vertex).map input.child).find? flag)
  funext child
  exact minimizingFlag_eq input matching goals vertices goals_correct covered vertex child

theorem nextChild_exists (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : arena.escapeLayer target vertices.length vertex) (notGoal : ¬ target vertex)
    (own : arena.owner vertex = arena.player) : ∃ child, nextChild input goals vertices vertex = some child := by
  rw [nextChild_eq input matching goals vertices goals_correct covered vertex]
  exact (referenceInput input matching goals goals_correct).optimalNext_exists vertices covered vertex inside notGoal own

theorem nextChild_sound (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex child : V) (inside : arena.escapeLayer target vertices.length vertex)
    (selected : nextChild input goals vertices vertex = some child) :
    arena.edge vertex child ∧ arena.escapeLayer target vertices.length child ∧
      arena.escapeRank target vertices.length child + 1 = arena.escapeRank target vertices.length vertex := by
  rw [nextChild_eq input matching goals vertices goals_correct covered vertex] at selected
  exact (referenceInput input matching goals goals_correct).optimalNext_sound vertices.length vertex child inside selected

/-- 同じ最小距離の全候補を、履歴に応じて任意に切り替えてよい。 -/
theorem minimizing_choices_optimal (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (strategy : arena.Strategy)
    (selected : ∀ past vertex, arena.escapeLayer target vertices.length vertex → ¬ target vertex →
      arena.owner vertex = arena.player → minimizingFlag input goals vertices vertex (strategy.choose past vertex) = true) :
    arena.EscapeOptimal target vertices strategy := by
  apply (referenceInput input matching goals goals_correct).minimizing_choices_optimal vertices strategy
  intro past vertex inside notGoal own
  rw [← minimizingFlag_eq input matching goals vertices goals_correct covered vertex]
  exact selected past vertex inside notGoal own

theorem runLabels_minimax (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (distance : Nat) (known : runLabels input goals vertices vertex = some distance) :
    (∃ strategy : arena.Strategy, arena.escapeWithin target strategy [] distance vertex) ∧
      ∀ strategy : arena.Strategy, ∀ past earlier, earlier < distance → ¬ arena.escapeWithin target strategy past earlier vertex := by
  have reference := referenceInput input matching goals goals_correct
  have computed : reference.computedDistance vertices.length vertex = some distance := by
    rw [← runLabels_reference input matching goals vertices goals_correct covered reference vertex]
    exact known
  exact reference.computedDistance_minimax vertices covered vertex distance computed

end PetaProof.EscapePropagation.State
