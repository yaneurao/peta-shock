import PetaProof.EscapeInfinite

/-! 有限の出辺とBool目標から距離を計算する参照版。FIFO版の実装時間とは区別する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} {A : HistoryArena V} {target : V → Prop}

structure EscapeInput (A : HistoryArena V) (target : V → Prop) where
  successors : V → List V
  edges : ∀ vertex child, child ∈ successors vertex ↔ A.edge vertex child
  goal : V → Bool
  goal_correct : ∀ vertex, goal vertex = true ↔ target vertex

namespace EscapeInput

variable (input : EscapeInput A target)

def layerFlag : Nat → V → Bool
  | 0, vertex => input.goal vertex
  | n + 1, vertex => input.goal vertex ||
      if A.owner vertex = A.player then (input.successors vertex).any (layerFlag n)
      else (input.successors vertex).all (layerFlag n)

theorem layerFlag_spec (n : Nat) (vertex : V) :
    input.layerFlag n vertex = true ↔ A.escapeLayer target n vertex := by
  induction n generalizing vertex with
  | zero => exact input.goal_correct vertex
  | succ n ih =>
    by_cases own : A.owner vertex = A.player <;>
      simp [layerFlag, escapeLayer, escapeStep, own, input.goal_correct, List.any_eq_true,
        List.all_eq_true, ih, input.edges]

/-- 初めてtrueになる段を探す実行可能な参照計算。未到達はnone。 -/
def computedDistance (cap : Nat) (vertex : V) : Option Nat :=
  (List.range' 0 (cap + 1)).find? (fun n => input.layerFlag n vertex)

theorem computedDistance_some (cap n : Nat) (vertex : V) :
    input.computedDistance cap vertex = some n ↔ n ≤ cap ∧ A.escapeLayer target n vertex ∧
      ∀ earlier, earlier < n → ¬ A.escapeLayer target earlier vertex := by
  constructor
  · intro computed
    have found := List.find?_range'_eq_some.mp computed
    have member := List.mem_range'_1.mp found.2.1
    refine ⟨by omega, (input.layerFlag_spec n vertex).mp found.1, ?_⟩
    intro earlier before inside
    have absent := found.2.2 earlier (Nat.zero_le _) before
    have present := (input.layerFlag_spec earlier vertex).mpr inside
    simp [present] at absent
  · rintro ⟨bounded, inside, minimal⟩
    apply List.find?_range'_eq_some.mpr
    refine ⟨(input.layerFlag_spec n vertex).mpr inside, ?_, ?_⟩
    · apply List.mem_range'_1.mpr; omega
    · intro earlier _ before
      have absent : input.layerFlag earlier vertex ≠ true := fun present =>
        minimal earlier before ((input.layerFlag_spec earlier vertex).mp present)
      cases found : input.layerFlag earlier vertex <;> simp_all

theorem computedDistance_none (cap : Nat) (vertex : V) :
    input.computedDistance cap vertex = none ↔ ¬ A.escapeLayer target cap vertex := by
  rw [computedDistance, List.find?_eq_none]
  constructor
  · intro absent inside
    exact absent cap (List.mem_range'_1.mpr (by omega)) ((input.layerFlag_spec cap vertex).mpr inside)
  · intro outside n member present
    have range := List.mem_range'_1.mp member
    exact outside (A.escapeLayer_mono target (by omega) vertex ((input.layerFlag_spec n vertex).mp present))

theorem computedDistance_eq (cap : Nat) (vertex : V) :
    input.computedDistance cap vertex = A.escapeDistance target cap vertex := by
  classical
  by_cases inside : A.escapeLayer target cap vertex
  · rw [(input.computedDistance_some cap (A.escapeRank target cap vertex) vertex).mpr
      (A.escapeRank_spec target cap vertex inside)]
    simp only [escapeDistance, if_pos inside]
  · rw [(input.computedDistance_none cap vertex).mpr inside]
    simp only [escapeDistance, if_neg inside]

/-- 計算結果some nが、任意履歴戦略を許した最短保証手数である。 -/
theorem computedDistance_minimax (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (n : Nat) (computed : input.computedDistance vertices.length vertex = some n) :
    (∃ strategy : A.Strategy, A.escapeWithin target strategy [] n vertex) ∧
      ∀ strategy : A.Strategy, ∀ past earlier, earlier < n → ¬ A.escapeWithin target strategy past earlier vertex := by
  have spec := (input.computedDistance_some vertices.length n vertex).mp computed
  have inside := A.escapeLayer_complete target vertices covered n vertex spec.2.1
  have canonical := A.escapeRank_spec target vertices.length vertex inside
  have equal : A.escapeRank target vertices.length vertex = n := by
    have upper := (A.escapeRank_le_iff target vertices.length vertex inside n).mpr spec.2.1
    have lower : n ≤ A.escapeRank target vertices.length vertex := by
      apply Nat.le_of_not_gt
      intro before
      exact spec.2.2 _ before canonical.2.1
    omega
  refine ⟨(A.escape_minimax target vertices covered vertex inside n).mpr (by omega), ?_⟩
  intro strategy past earlier before guaranteed
  exact spec.2.2 earlier before (A.escapeWithin_layer target strategy past earlier vertex guaranteed)

def minimizingFlag (cap : Nat) (vertex child : V) : Bool :=
  match input.computedDistance cap vertex, input.computedDistance cap child with
  | some parent, some next => decide (next + 1 = parent)
  | _, _ => false

theorem minimizingFlag_spec (cap : Nat) (vertex : V) (inside : A.escapeLayer target cap vertex) (child : V) :
    input.minimizingFlag cap vertex child = true ↔ A.escapeLayer target cap child ∧
      A.escapeRank target cap child + 1 = A.escapeRank target cap vertex := by
  classical
  by_cases childInside : A.escapeLayer target cap child <;>
    simp [minimizingFlag, input.computedDistance_eq, escapeDistance, inside, childInside]

def optimalNext (cap : Nat) (vertex : V) : Option V :=
  (input.successors vertex).find? (input.minimizingFlag cap vertex)

theorem optimalNext_sound (cap : Nat) (vertex child : V) (inside : A.escapeLayer target cap vertex)
    (selected : input.optimalNext cap vertex = some child) :
    A.edge vertex child ∧ A.escapeLayer target cap child ∧
      A.escapeRank target cap child + 1 = A.escapeRank target cap vertex :=
  ⟨(input.edges vertex child).mp (List.mem_of_find?_eq_some selected),
    (input.minimizingFlag_spec cap vertex inside child).mp (List.find?_some selected)⟩

theorem optimalNext_exists (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : A.escapeLayer target vertices.length vertex) (notTarget : ¬ target vertex)
    (own : A.owner vertex = A.player) : ∃ child, input.optimalNext vertices.length vertex = some child := by
  obtain ⟨child, edge, childInside, rank⟩ := A.own_escape_successor target vertices covered vertex inside notTarget own
  have member := (input.edges vertex child).mpr edge
  have flag := (input.minimizingFlag_spec vertices.length vertex inside child).mpr ⟨childInside, rank⟩
  cases computed : input.optimalNext vertices.length vertex with
  | some found => exact ⟨found, rfl⟩
  | none => exact False.elim ((List.find?_eq_none.mp computed) child member flag)

noncomputable def computedStrategy (cap : Nat) : A.Strategy where
  choose := fun _ vertex => match input.optimalNext cap vertex with
    | some child => child
    | none => Classical.choose (A.moves_exist vertex)
  legal := by
    intro past vertex own
    cases selected : input.optimalNext cap vertex with
    | some child => exact (input.edges vertex child).mp (List.mem_of_find?_eq_some selected)
    | none => exact Classical.choose_spec (A.moves_exist vertex)

/-- 実際に有限出辺から選んだ手も、全有限距離の頂点で最短保証を実現する。 -/
theorem computedStrategy_optimal (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    A.EscapeOptimal target vertices (input.computedStrategy vertices.length) := by
  intro past vertex inside notTarget own
  obtain ⟨child, selected⟩ := input.optimalNext_exists vertices covered vertex inside notTarget own
  have spec := input.optimalNext_sound vertices.length vertex child inside selected
  simpa only [computedStrategy, selected] using spec.2

theorem minimizing_choices_optimal (vertices : List V) (strategy : A.Strategy)
    (selected : ∀ past vertex, A.escapeLayer target vertices.length vertex → ¬ target vertex →
      A.owner vertex = A.player → input.minimizingFlag vertices.length vertex (strategy.choose past vertex) = true) :
    A.EscapeOptimal target vertices strategy := by
  intro past vertex inside notTarget own
  exact (input.minimizingFlag_spec vertices.length vertex inside _).mp (selected past vertex inside notTarget own)

end EscapeInput
end PetaProof.HistoryArena
