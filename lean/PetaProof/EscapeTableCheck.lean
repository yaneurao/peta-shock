import PetaProof.EscapeDistanceTable

/-! 有限距離表の局所条件を、経路列挙をせずBoolで検査する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} {A : HistoryArena V} {target : V → Prop}

namespace EscapeInput

def exactChild (label : Option Nat) (distance : Nat) : Bool :=
  match label with
  | none => false
  | some cost => decide (cost + 1 = distance)

def lowerChild (label : Option Nat) (distance : Nat) : Bool :=
  match label with
  | none => true
  | some cost => decide (distance ≤ cost + 1)

def upperChild (label : Option Nat) (distance : Nat) : Bool :=
  match label with
  | none => false
  | some cost => decide (cost + 1 ≤ distance)

theorem exactChild_spec (label : Option Nat) (distance : Nat) :
    exactChild label distance = true ↔ ∃ cost, label = some cost ∧ cost + 1 = distance := by
  cases label <;> simp [exactChild]

theorem lowerChild_spec (label : Option Nat) (distance : Nat) :
    lowerChild label distance = true ↔ ∀ cost, label = some cost → distance ≤ cost + 1 := by
  cases label <;> simp [lowerChild]

theorem upperChild_spec (label : Option Nat) (distance : Nat) :
    upperChild label distance = true ↔ ∃ cost, label = some cost ∧ cost + 1 ≤ distance := by
  cases label <;> simp [upperChild]

variable (input : EscapeInput A target) (labels : V → Option Nat)

def localTableCheck (vertex : V) : Bool :=
  if input.goal vertex then decide (labels vertex = some 0) else
    match labels vertex with
    | none =>
      if A.owner vertex = A.player then (input.successors vertex).all (fun child => (labels child).isNone)
      else (input.successors vertex).any (fun child => (labels child).isNone)
    | some distance =>
      if A.owner vertex = A.player then
        (input.successors vertex).any (fun child => exactChild (labels child) distance) &&
        (input.successors vertex).all (fun child => lowerChild (labels child) distance)
      else
        (input.successors vertex).all (fun child => upperChild (labels child) distance) &&
        (input.successors vertex).any (fun child => exactChild (labels child) distance)

def LocalTable (vertex : V) : Prop := by
  classical
  exact if target vertex then labels vertex = some 0 else
    match labels vertex with
    | none =>
      if A.owner vertex = A.player then ∀ child, A.edge vertex child → labels child = none
      else ∃ child, A.edge vertex child ∧ labels child = none
    | some distance =>
      if A.owner vertex = A.player then
        (∃ child cost, A.edge vertex child ∧ labels child = some cost ∧ cost + 1 = distance) ∧
        (∀ child, A.edge vertex child → ∀ cost, labels child = some cost → distance ≤ cost + 1)
      else
        (∀ child, A.edge vertex child → ∃ cost, labels child = some cost ∧ cost + 1 ≤ distance) ∧
        (∃ child cost, A.edge vertex child ∧ labels child = some cost ∧ cost + 1 = distance)

theorem localTableCheck_spec (vertex : V) :
    input.localTableCheck labels vertex = true ↔ LocalTable (A := A) (target := target) labels vertex := by
  classical
  by_cases goal : target vertex
  · have flag := (input.goal_correct vertex).mpr goal
    simp [localTableCheck, LocalTable, goal, flag]
  · have flag : input.goal vertex = false := by
      cases same : input.goal vertex with
      | false => rfl
      | true => exact False.elim (goal ((input.goal_correct vertex).mp same))
    by_cases own : A.owner vertex = A.player <;> cases known : labels vertex <;>
      simp [localTableCheck, LocalTable, goal, flag, own, known, List.any_eq_true, List.all_eq_true,
        exactChild_spec, lowerChild_spec, upperChild_spec, input.edges, exists_and_left]

def tableCheck (vertices : List V) : Bool := vertices.all (input.localTableCheck labels)

/-- チェッカーが検査するのは有限な局所条件であり、到達層の再計算ではない。 -/
theorem tableCheck_correct (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    input.tableCheck labels vertices = true ↔ EscapeTable A target labels := by
  classical
  have allLocal : input.tableCheck labels vertices = true ↔
      ∀ vertex, LocalTable (A := A) (target := target) labels vertex := by
    simp only [tableCheck, List.all_eq_true, input.localTableCheck_spec]
    exact ⟨fun checked vertex => checked vertex (covered vertex), fun checked vertex _ => checked vertex⟩
  rw [allLocal]
  constructor
  · intro checked
    constructor
    · intro vertex goal
      simpa [LocalTable, goal] using checked vertex
    · intro vertex distance goal own known
      have parts := checked vertex
      simp only [LocalTable, if_neg goal, known, if_pos own] at parts
      exact ⟨parts.1, fun child cost edge label => parts.2 child edge cost label⟩
    · intro vertex distance goal own known
      simpa [LocalTable, goal, own, known] using checked vertex
    · intro vertex goal own known
      simpa [LocalTable, goal, own, known] using checked vertex
    · intro vertex goal own known
      simpa [LocalTable, goal, own, known] using checked vertex
  · intro table vertex
    by_cases goal : target vertex
    · simpa [LocalTable, goal] using table.goals vertex goal
    · by_cases own : A.owner vertex = A.player
      · cases known : labels vertex with
        | none => simpa [LocalTable, goal, own, known] using table.own_infinite vertex goal own known
        | some distance =>
          have parts := table.own_finite vertex distance goal own known
          simp only [LocalTable, if_neg goal, known, if_pos own]
          exact ⟨parts.1, fun child edge cost label => parts.2 child cost edge label⟩
      · cases known : labels vertex with
        | none => simpa [LocalTable, goal, own, known] using table.other_infinite vertex goal own known
        | some distance => simpa [LocalTable, goal, own, known] using table.other_finite vertex distance goal own known

theorem checked_exact (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (checked : input.tableCheck labels vertices = true) (vertex : V) :
    labels vertex = input.computedDistance vertices.length vertex := by
  exact ((input.tableCheck_correct labels vertices covered).mp checked).agrees_with_reference input vertices covered vertex

/-- 受理する表は最短保証距離表ただ一つで、正しい表を棄却することもない。 -/
theorem tableCheck_iff_exact (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    input.tableCheck labels vertices = true ↔ labels = input.computedDistance vertices.length := by
  constructor
  · intro checked
    funext vertex
    exact input.checked_exact labels vertices covered checked vertex
  · intro same
    apply (input.tableCheck_correct labels vertices covered).mpr
    have reference := escapeDistance_table (A := A) (target := target) vertices covered
    have equal : labels = A.escapeDistance target vertices.length := by
      funext vertex
      rw [same]
      exact input.computedDistance_eq vertices.length vertex
    simpa only [equal] using reference

end EscapeInput
end PetaProof.HistoryArena
