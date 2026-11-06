import PetaProof.RankedPolicy
import PetaProof.Progress

/-! 固定した安全候補グラフで、目標集合への最短保証手数を到達層から定義する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V) (target : V → Prop)

/-- 自分は一手を選び、相手については全応手を対象にする。目標では直ちに停止する。 -/
def escapeStep (current : V → Prop) (vertex : V) : Prop :=
  target vertex ∨ if A.owner vertex = A.player then
    ∃ child, A.edge vertex child ∧ current child
  else ∀ child, A.edge vertex child → current child

def escapeLayer : Nat → V → Prop
  | 0 => target
  | n + 1 => A.escapeStep target (escapeLayer n)

theorem escapeStep_mono {small large : V → Prop} (sub : ∀ vertex, small vertex → large vertex)
    {vertex : V} (inside : A.escapeStep target small vertex) : A.escapeStep target large vertex := by
  rcases inside with goal | step
  · exact Or.inl goal
  · right
    by_cases own : A.owner vertex = A.player
    · rw [if_pos own] at step ⊢
      obtain ⟨child, edge, found⟩ := step
      exact ⟨child, edge, sub child found⟩
    · rw [if_neg own] at step ⊢
      exact fun child edge => sub child (step child edge)

theorem escapeLayer_succ (n : Nat) (vertex : V) :
    A.escapeLayer target n vertex → A.escapeLayer target (n + 1) vertex := by
  induction n generalizing vertex with
  | zero => exact Or.inl
  | succ n ih => exact A.escapeStep_mono target (fun child => ih child)

theorem escapeLayer_mono {n m : Nat} (bound : n ≤ m) (vertex : V)
    (inside : A.escapeLayer target n vertex) : A.escapeLayer target m vertex := by
  induction bound with
  | refl => exact inside
  | step _ ih => exact A.escapeLayer_succ target _ vertex ih

/-- ある段階で新規頂点がなければ、それ以降も増えない。 -/
theorem escapeLayer_closed (n : Nat)
    (closed : ∀ vertex, A.escapeLayer target (n + 1) vertex → A.escapeLayer target n vertex) :
    ∀ m vertex, A.escapeLayer target m vertex → A.escapeLayer target n vertex := by
  intro m
  induction m with
  | zero => exact fun vertex inside => A.escapeLayer_mono target (Nat.zero_le n) vertex inside
  | succ m ih => exact fun _ inside => closed _ (A.escapeStep_mono target ih inside)

theorem escapeLayer_stops (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    ∃ n, n ≤ vertices.length ∧
      ∀ vertex, A.escapeLayer target (n + 1) vertex → A.escapeLayer target n vertex := by
  classical
  apply progress_stops vertices (A.escapeLayer target) (A.escapeLayer_succ target)
    (fun n => ∀ vertex, A.escapeLayer target (n + 1) vertex → A.escapeLayer target n vertex)
  intro n notClosed
  have witness : ∃ vertex, A.escapeLayer target (n + 1) vertex ∧ ¬ A.escapeLayer target n vertex := by
    apply Classical.byContradiction
    intro none
    apply notClosed
    intro vertex inside
    apply Classical.byContradiction
    intro outside
    exact none ⟨vertex, inside, outside⟩
  obtain ⟨vertex, inside, outside⟩ := witness
  exact ⟨vertex, covered vertex, inside, outside⟩

/-- N段までで到達可能な全頂点を網羅する。組合せ経路を列挙する必要はない。 -/
theorem escapeLayer_complete (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (n : Nat) (vertex : V) (inside : A.escapeLayer target n vertex) :
    A.escapeLayer target vertices.length vertex := by
  obtain ⟨stage, bound, closed⟩ := A.escapeLayer_stops target vertices covered
  exact A.escapeLayer_mono target bound vertex (A.escapeLayer_closed target stage closed n vertex inside)

/-- 初めて到達層へ入る段階。存在だけでなく、それ以前には保証できないことも記録する。 -/
theorem escape_first_entry (cap : Nat) (vertex : V) (inside : A.escapeLayer target cap vertex) :
    ∃ n, n ≤ cap ∧ A.escapeLayer target n vertex ∧
      ∀ k, k < n → ¬ A.escapeLayer target k vertex := by
  classical
  obtain ⟨n, found, minimal⟩ := minimum_on_domain (List.range (cap + 1))
    (fun n => n ≤ cap ∧ A.escapeLayer target n vertex) id
    (fun n found => List.mem_range.mpr (by omega)) ⟨cap, Nat.le_refl _, inside⟩
  refine ⟨n, found.1, found.2, ?_⟩
  intro k before earlier
  have lower := minimal k ⟨by omega, earlier⟩
  change n ≤ k at lower
  omega

noncomputable def escapeRank (cap : Nat) (vertex : V) : Nat := by
  classical
  exact if inside : A.escapeLayer target cap vertex then
    Classical.choose (A.escape_first_entry target cap vertex inside) else 0

theorem escapeRank_spec (cap : Nat) (vertex : V) (inside : A.escapeLayer target cap vertex) :
    A.escapeRank target cap vertex ≤ cap ∧ A.escapeLayer target (A.escapeRank target cap vertex) vertex ∧
      ∀ k, k < A.escapeRank target cap vertex → ¬ A.escapeLayer target k vertex := by
  classical
  simpa only [escapeRank, dif_pos inside] using Classical.choose_spec (A.escape_first_entry target cap vertex inside)

theorem escapeRank_le_iff (cap : Nat) (vertex : V) (inside : A.escapeLayer target cap vertex) (n : Nat) :
    A.escapeRank target cap vertex ≤ n ↔ A.escapeLayer target n vertex := by
  have spec := A.escapeRank_spec target cap vertex inside
  constructor
  · intro bound
    exact A.escapeLayer_mono target bound vertex spec.2.1
  · intro found
    apply Nat.le_of_not_gt
    intro tooSmall
    exact spec.2.2 n tooSmall found

theorem escapeRank_zero_iff (cap : Nat) (vertex : V) (inside : A.escapeLayer target cap vertex) :
    A.escapeRank target cap vertex = 0 ↔ target vertex := by
  have rank := A.escapeRank_le_iff target cap vertex inside 0
  simpa only [Nat.le_zero_eq, escapeLayer] using rank

/-- noneは脱出を強制できないことを表す。未確定頂点を距離0とは扱わない。 -/
noncomputable def escapeDistance (cap : Nat) (vertex : V) : Option Nat := by
  classical
  exact if A.escapeLayer target cap vertex then some (A.escapeRank target cap vertex) else none

theorem escapeDistance_none (cap : Nat) (vertex : V) :
    A.escapeDistance target cap vertex = none ↔ ¬ A.escapeLayer target cap vertex := by
  classical
  simp [escapeDistance]

theorem own_escape_successor (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : A.escapeLayer target vertices.length vertex) (notTarget : ¬ target vertex)
    (own : A.owner vertex = A.player) :
    ∃ child, A.edge vertex child ∧ A.escapeLayer target vertices.length child ∧
      A.escapeRank target vertices.length child + 1 = A.escapeRank target vertices.length vertex := by
  have positive : 0 < A.escapeRank target vertices.length vertex := by
    have zero := A.escapeRank_zero_iff target vertices.length vertex inside
    exact Nat.pos_of_ne_zero (fun equal => notTarget (zero.mp equal))
  obtain ⟨n, rank⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have layer := (A.escapeRank_spec target vertices.length vertex inside).2.1
  rw [rank] at layer
  have step := layer.resolve_left notTarget
  rw [if_pos own] at step
  obtain ⟨child, edge, reached⟩ := step
  have childInside := A.escapeLayer_complete target vertices covered n child reached
  have upper := (A.escapeRank_le_iff target vertices.length child childInside n).mpr reached
  have parentLayer : A.escapeLayer target (A.escapeRank target vertices.length child + 1) vertex :=
    Or.inr (by rw [if_pos own]; exact ⟨child, edge, (A.escapeRank_spec target vertices.length child childInside).2.1⟩)
  have lower := (A.escapeRank_le_iff target vertices.length vertex inside _).mpr parentLayer
  exact ⟨child, edge, childInside, by omega⟩

theorem other_escape_successor (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : A.escapeLayer target vertices.length vertex) (notTarget : ¬ target vertex)
    (other : A.owner vertex ≠ A.player) (child : V) (edge : A.edge vertex child) :
    A.escapeLayer target vertices.length child ∧
      A.escapeRank target vertices.length child < A.escapeRank target vertices.length vertex := by
  have positive : 0 < A.escapeRank target vertices.length vertex := by
    have zero := A.escapeRank_zero_iff target vertices.length vertex inside
    exact Nat.pos_of_ne_zero (fun equal => notTarget (zero.mp equal))
  obtain ⟨n, rank⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have layer := (A.escapeRank_spec target vertices.length vertex inside).2.1
  rw [rank] at layer
  have step := layer.resolve_left notTarget
  rw [if_neg other] at step
  have reached := step child edge
  have childInside := A.escapeLayer_complete target vertices covered n child reached
  have upper := (A.escapeRank_le_iff target vertices.length child childInside n).mpr reached
  exact ⟨childInside, by omega⟩

end PetaProof.HistoryArena
