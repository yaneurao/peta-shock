import PetaProof.EscapeComputation

/-! 最終距離表の局所min/max条件から、到達層との完全一致を証明する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} {A : HistoryArena V} {target : V → Prop}

def DistanceWithin (labels : V → Option Nat) (bound : Nat) (vertex : V) : Prop :=
  ∃ distance, labels vertex = some distance ∧ distance ≤ bound

/-- noneは無限距離。min/max条件は有限の出辺だけを見て検査できる。 -/
structure EscapeTable (A : HistoryArena V) (target : V → Prop) (labels : V → Option Nat) : Prop where
  goals : ∀ vertex, target vertex → labels vertex = some 0
  own_finite : ∀ vertex distance, ¬ target vertex → A.owner vertex = A.player →
    labels vertex = some distance →
      (∃ child cost, A.edge vertex child ∧ labels child = some cost ∧ cost + 1 = distance) ∧
      (∀ child cost, A.edge vertex child → labels child = some cost → distance ≤ cost + 1)
  other_finite : ∀ vertex distance, ¬ target vertex → A.owner vertex ≠ A.player →
    labels vertex = some distance →
      (∀ child, A.edge vertex child → ∃ cost, labels child = some cost ∧ cost + 1 ≤ distance) ∧
      (∃ child cost, A.edge vertex child ∧ labels child = some cost ∧ cost + 1 = distance)
  own_infinite : ∀ vertex, ¬ target vertex → A.owner vertex = A.player → labels vertex = none →
    ∀ child, A.edge vertex child → labels child = none
  other_infinite : ∀ vertex, ¬ target vertex → A.owner vertex ≠ A.player → labels vertex = none →
    ∃ child, A.edge vertex child ∧ labels child = none

namespace EscapeTable
variable {labels : V → Option Nat} (table : EscapeTable A target labels)
include table

/-- 有限ラベルから毎手小さいラベルへ進むので、循環に偽の有限距離を付けられない。 -/
theorem finite_sound (vertex : V) (distance : Nat) (known : labels vertex = some distance) :
    A.escapeLayer target distance vertex := by
  induction distance using Nat.strongRecOn generalizing vertex with
  | ind distance ih =>
    by_cases goal : target vertex
    · exact A.escapeLayer_mono target (Nat.zero_le distance) vertex goal
    · by_cases own : A.owner vertex = A.player
      · obtain ⟨⟨child, cost, edge, label, same⟩, _⟩ := table.own_finite vertex distance goal own known
        have inside := ih cost (by omega) child label
        rw [← same]
        exact Or.inr (by simpa only [escapeStep, if_pos own] using
          (show ∃ child, A.edge vertex child ∧ A.escapeLayer target cost child from ⟨child, edge, inside⟩))
      · have parts := table.other_finite vertex distance goal own known
        obtain ⟨child, cost, _, _, same⟩ := parts.2
        rw [← same]
        apply Or.inr
        rw [if_neg own]
        intro next edge
        obtain ⟨nextCost, label, bound⟩ := parts.1 next edge
        have inside := ih nextCost (by omega) next label
        exact A.escapeLayer_mono target (by omega) next inside

/-- 到達層nの全頂点がラベルn以下を持つ。noneや過大距離の誤りを排除する。 -/
theorem layer_bounded (bound : Nat) (vertex : V) (inside : A.escapeLayer target bound vertex) :
    DistanceWithin labels bound vertex := by
  induction bound generalizing vertex with
  | zero => exact ⟨0, table.goals vertex inside, Nat.le_refl _⟩
  | succ bound ih =>
    rcases inside with goal | step
    · exact ⟨0, table.goals vertex goal, Nat.zero_le _⟩
    · by_cases goal : target vertex
      · exact ⟨0, table.goals vertex goal, Nat.zero_le _⟩
      · by_cases own : A.owner vertex = A.player
        · rw [if_pos own] at step
          obtain ⟨child, edge, childInside⟩ := step
          obtain ⟨cost, label, smaller⟩ := ih child childInside
          cases known : labels vertex with
          | none =>
            have absent := table.own_infinite vertex goal own known child edge
            rw [absent] at label
            cases label
          | some distance =>
            have upper := (table.own_finite vertex distance goal own known).2 child cost edge label
            exact ⟨distance, known, by omega⟩
        · rw [if_neg own] at step
          cases known : labels vertex with
          | none =>
            obtain ⟨child, edge, absent⟩ := table.other_infinite vertex goal own known
            obtain ⟨cost, label, _⟩ := ih child (step child edge)
            rw [absent] at label
            cases label
          | some distance =>
            obtain ⟨child, cost, edge, label, same⟩ := (table.other_finite vertex distance goal own known).2
            obtain ⟨otherCost, otherLabel, smaller⟩ := ih child (step child edge)
            have equal : cost = otherCost := Option.some.inj (label.symm.trans otherLabel)
            exact ⟨distance, known, by omega⟩

theorem finite_iff (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    (∃ distance, labels vertex = some distance) ↔ A.escapeLayer target vertices.length vertex := by
  constructor
  · rintro ⟨distance, known⟩
    exact A.escapeLayer_complete target vertices covered distance vertex (table.finite_sound vertex distance known)
  · intro inside
    obtain ⟨distance, known, _⟩ := table.layer_bounded vertices.length vertex inside
    exact ⟨distance, known⟩

/-- 局所条件を満たす距離表は、任意履歴戦略に対する最短保証距離そのものである。 -/
theorem exact_distance (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    labels vertex = A.escapeDistance target vertices.length vertex := by
  classical
  cases known : labels vertex with
  | none =>
    have outside : ¬ A.escapeLayer target vertices.length vertex := by
      intro inside
      obtain ⟨distance, impossible⟩ := (table.finite_iff vertices covered vertex).mpr inside
      rw [known] at impossible
      cases impossible
    simp [escapeDistance, outside]
  | some distance =>
    have inside := (table.finite_iff vertices covered vertex).mp ⟨distance, known⟩
    have first := A.escapeRank_spec target vertices.length vertex inside
    have lower := (A.escapeRank_le_iff target vertices.length vertex inside distance).mpr
      (table.finite_sound vertex distance known)
    obtain ⟨cost, label, upper⟩ := table.layer_bounded _ vertex first.2.1
    have same : distance = cost := Option.some.inj (known.symm.trans label)
    have equal : distance = A.escapeRank target vertices.length vertex := by omega
    simp [escapeDistance, inside, equal]

theorem agrees_with_reference (input : EscapeInput A target) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    labels vertex = input.computedDistance vertices.length vertex := by
  rw [input.computedDistance_eq]
  exact table.exact_distance vertices covered vertex

theorem unique {other : V → Option Nat} (second : EscapeTable A target other)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) : labels = other := by
  funext vertex
  exact (table.exact_distance vertices covered vertex).trans (second.exact_distance vertices covered vertex).symm

end EscapeTable

/-- 真の最短距離表は局所条件を全て満たす。検査条件は必要条件でもある。 -/
theorem escapeDistance_table (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    EscapeTable A target (A.escapeDistance target vertices.length) := by
  classical
  have finite (vertex : V) (distance : Nat) :
      A.escapeDistance target vertices.length vertex = some distance ↔
        A.escapeLayer target vertices.length vertex ∧ A.escapeRank target vertices.length vertex = distance := by
    by_cases inside : A.escapeLayer target vertices.length vertex <;> simp [escapeDistance, inside]
  constructor
  · intro vertex goal
    have inside := A.escapeLayer_mono target (Nat.zero_le vertices.length) vertex goal
    exact (finite vertex 0).mpr ⟨inside, (A.escapeRank_zero_iff target vertices.length vertex inside).mpr goal⟩
  · intro vertex distance goal own known
    obtain ⟨inside, same⟩ := (finite vertex distance).mp known
    obtain ⟨child, edge, childInside, descent⟩ := A.own_escape_successor target vertices covered vertex inside goal own
    refine ⟨⟨child, _, edge, (finite child _).mpr ⟨childInside, rfl⟩, descent.trans same⟩, ?_⟩
    intro next cost nextEdge nextLabel
    obtain ⟨nextInside, nextSame⟩ := (finite next cost).mp nextLabel
    simpa only [same, nextSame] using A.escape_own_cost target vertices vertex next inside own nextEdge nextInside
  · intro vertex distance goal other known
    obtain ⟨inside, same⟩ := (finite vertex distance).mp known
    constructor
    · intro child edge
      obtain ⟨childInside, descent⟩ := A.other_escape_successor target vertices covered vertex inside goal other child edge
      refine ⟨_, (finite child _).mpr ⟨childInside, rfl⟩, ?_⟩
      omega
    · obtain ⟨child, edge, childInside, descent⟩ := A.escape_other_max target vertices covered vertex inside goal other
      exact ⟨child, _, edge, (finite child _).mpr ⟨childInside, rfl⟩, descent.trans same⟩
  · intro vertex _ own absent child edge
    have outside := (A.escapeDistance_none target vertices.length vertex).mp absent
    exact (A.escapeDistance_none target vertices.length child).mpr
      (A.escape_outside_own target vertices covered vertex outside own child edge)
  · intro vertex _ other absent
    have outside := (A.escapeDistance_none target vertices.length vertex).mp absent
    obtain ⟨child, edge, childOutside⟩ := A.escape_outside_other target vertices covered vertex outside other
    exact ⟨child, edge, (A.escapeDistance_none target vertices.length child).mpr childOutside⟩

end PetaProof.HistoryArena
