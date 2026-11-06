import PetaProof.EscapeComputation
import PetaProof.PathRank
import PetaProof.EscapeExact

/-! 最小化する頂点と最大化する頂点を計算前に固定した、無限を含むrank生成。 -/
namespace PetaProof.SignedRankGraph

universe u
variable {V : Type u}

structure Input (V : Type u) where
  moves : V → List V
  nonempty : ∀ vertex, moves vertex ≠ []
  minimizes : V → Bool
  goal : V → Bool

namespace Input
variable (input : Input V)

def arena : HistoryArena V where
  edge := fun v w => w ∈ input.moves v
  owner := input.minimizes
  player := true
  bad := fun _ _ => False
  moves_exist := by
    intro vertex
    cases found : input.moves vertex with
    | nil => exact False.elim (input.nonempty vertex found)
    | cons first rest => exact ⟨first, by simp [found]⟩

def target (vertex : V) : Prop := input.goal vertex = true

def computation : HistoryArena.EscapeInput input.arena input.target where
  successors := input.moves
  edges := fun _ _ => Iff.rfl
  goal := input.goal
  goal_correct := fun _ => Iff.rfl

def rank (cap : Nat) (vertex : V) : PathRank.Rank :=
  input.computation.computedDistance cap vertex

theorem rank_bound (cap : Nat) (vertex : V) : PathRank.Bounded cap (input.rank cap vertex) := by
  intro n found
  exact ((input.computation.computedDistance_some cap n vertex).mp found).1

theorem rank_eq_distance (cap : Nat) (vertex : V) :
    input.rank cap vertex = input.arena.escapeDistance input.target cap vertex :=
  input.computation.computedDistance_eq cap vertex

/-- 参照の再帰評価を実装に要求しない。正しい辺ID・逆辺を持つ既証FIFOの出力と一致する。 -/
theorem fifo_rank [DecidableEq V] {E : Type u} [DecidableEq E]
    (indexed : EscapePropagation.Input V E) (matching : EscapePropagation.ArenaMatch indexed input.arena)
    (goals vertices : List V) (goals_correct : ∀ vertex, input.target vertex ↔ vertex ∈ goals)
    (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    EscapePropagation.State.runLabels indexed goals vertices vertex = input.rank vertices.length vertex :=
  EscapePropagation.State.runLabels_reference indexed matching goals vertices goals_correct covered input.computation vertex

theorem rank_table (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    HistoryArena.EscapeTable input.arena input.target (input.rank vertices.length) := by
  have same : input.rank vertices.length = input.arena.escapeDistance input.target vertices.length :=
    funext (input.rank_eq_distance vertices.length)
  rw [same]
  exact HistoryArena.escapeDistance_table vertices covered

theorem rank_some_spec (cap n : Nat) (vertex : V) (found : input.rank cap vertex = some n) :
    input.arena.escapeLayer input.target cap vertex ∧
      input.arena.escapeRank input.target cap vertex = n := by
  have spec := (input.computation.computedDistance_some cap n vertex).mp found
  have inside := input.arena.escapeLayer_mono input.target spec.1 vertex spec.2.1
  rw [input.rank_eq_distance] at found
  exact ⟨inside, Option.some.inj (by simpa only [HistoryArena.escapeDistance, if_pos inside] using found)⟩

theorem finite_min_witness (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex : V) (n : Nat) (found : input.rank vertices.length vertex = some n)
    (notGoal : ¬ input.target vertex) (small : input.minimizes vertex = true) :
    ∃ child ∈ input.moves vertex, ∃ k,
      input.rank vertices.length child = some k ∧ k + 1 = n := by
  have spec := input.rank_some_spec vertices.length n vertex found
  obtain ⟨child, edge, inside, step⟩ := input.arena.own_escape_successor input.target vertices covered
    vertex spec.1 notGoal small
  refine ⟨child, edge, input.arena.escapeRank input.target vertices.length child, ?_, ?_⟩
  · rw [input.rank_eq_distance]
    simp only [HistoryArena.escapeDistance, if_pos inside]
  · omega

theorem finite_max_witness (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex : V) (n : Nat) (found : input.rank vertices.length vertex = some n)
    (notGoal : ¬ input.target vertex) (large : input.minimizes vertex = false) :
    ∃ child ∈ input.moves vertex, ∃ k,
      input.rank vertices.length child = some k ∧ k + 1 = n := by
  have spec := input.rank_some_spec vertices.length n vertex found
  have other : input.arena.owner vertex ≠ input.arena.player := by
    change input.minimizes vertex ≠ true
    simp [large]
  obtain ⟨child, edge, inside, step⟩ := input.arena.escape_other_max input.target vertices covered
    vertex spec.1 notGoal other
  refine ⟨child, edge, input.arena.escapeRank input.target vertices.length child, ?_, ?_⟩
  · rw [input.rank_eq_distance]
    simp only [HistoryArena.escapeDistance, if_pos inside]
  · omega

/-- 最大化側の有限rankでは全ての子が有限。少なくとも一子が最大値を達成する。 -/
theorem finite_max_all (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex : V) (n : Nat) (found : input.rank vertices.length vertex = some n)
    (notGoal : ¬ input.target vertex) (large : input.minimizes vertex = false)
    (child : V) (edge : child ∈ input.moves vertex) :
    ∃ k, input.rank vertices.length child = some k ∧ k + 1 ≤ n := by
  have spec := input.rank_some_spec vertices.length n vertex found
  have other : input.arena.owner vertex ≠ input.arena.player := by
    change input.minimizes vertex ≠ true
    simp [large]
  have next := input.arena.other_escape_successor input.target vertices covered vertex spec.1 notGoal other child edge
  refine ⟨input.arena.escapeRank input.target vertices.length child, ?_, by omega⟩
  rw [input.rank_eq_distance]
  simp only [HistoryArena.escapeDistance, if_pos next.1]

/-- 最小化側の無限rankでは全ての子も無限。短い出口があるのに無限とすることはない。 -/
theorem infinite_min_all (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex : V) (found : input.rank vertices.length vertex = none)
    (small : input.minimizes vertex = true) (child : V) (edge : child ∈ input.moves vertex) :
    input.rank vertices.length child = none := by
  have outside := (input.computation.computedDistance_none vertices.length vertex).mp found
  apply (input.computation.computedDistance_none vertices.length child).mpr
  intro inside
  have next : input.arena.escapeLayer input.target (vertices.length + 1) vertex := by
    right
    change if input.minimizes vertex = true then _ else _
    rw [if_pos small]
    exact ⟨child, edge, inside⟩
  exact outside (input.arena.escapeLayer_complete input.target vertices covered _ vertex next)

/-- 最大化側の無限rankでは、無限rankを保つ応手が実際に一つ以上ある。 -/
theorem infinite_max_witness (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex : V) (found : input.rank vertices.length vertex = none)
    (large : input.minimizes vertex = false) :
    ∃ child ∈ input.moves vertex, input.rank vertices.length child = none := by
  classical
  have outside := (input.computation.computedDistance_none vertices.length vertex).mp found
  apply Classical.byContradiction
  intro absent
  have children : ∀ child, child ∈ input.moves vertex → input.arena.escapeLayer input.target vertices.length child := by
    intro child edge
    apply Classical.byContradiction
    intro notInside
    exact absent ⟨child, edge, (input.computation.computedDistance_none vertices.length child).mpr notInside⟩
  have next : input.arena.escapeLayer input.target (vertices.length + 1) vertex := by
    right
    have other : input.arena.owner vertex ≠ input.arena.player := by
      change input.minimizes vertex ≠ true
      simp [large]
    rw [if_neg other]
    exact children
  exact outside (input.arena.escapeLayer_complete input.target vertices covered _ vertex next)

def cost (cap : Nat) (child : V) : PathRank.Rank :=
  (input.rank cap child).map Nat.succ

theorem cost_bound (cap : Nat) (child : V) : PathRank.Bounded (cap + 1) (input.cost cap child) := by
  intro n found
  have bound := input.rank_bound cap child
  cases rank : input.rank cap child with
  | none => simp [cost, rank] at found
  | some k =>
    have limit := bound k rank
    simp [cost, rank] at found
    omega

/-- 計算時のmin/maxを選別時にも使う。負値側を、最短距離の計算後に反転する処理ではない。 -/
def preferred (cap : Nat) (vertex child : V) : Prop :=
  PathRank.Preferred (fun _ => if input.minimizes vertex then 0 else -1) (input.cost cap) (cap + 1)
    (fun child => child ∈ input.moves vertex) (if input.minimizes vertex then 0 else -1) child

theorem preferred_exists (cap : Nat) (vertex : V) : ∃ child ∈ input.moves vertex, input.preferred cap vertex child := by
  obtain ⟨child, edge⟩ := input.arena.moves_exist vertex
  exact PathRank.preferred_exists _ _ _ _ _ (input.moves vertex) (fun _ member => member)
    ⟨child, edge, edge, rfl⟩

/-- 無限も含むBellman等号。選んだ子のrankから親のrankを実際に再構成できる。 -/
theorem preferred_rank (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex child : V) (notGoal : ¬ input.target vertex)
    (chosen : input.preferred vertices.length vertex child) :
    input.rank vertices.length vertex = input.cost vertices.length child := by
  cases parent : input.rank vertices.length vertex with
  | none =>
    cases small : input.minimizes vertex with
    | true =>
      have next := input.infinite_min_all vertices covered vertex parent small child chosen.1
      simp [cost, next]
    | false =>
      obtain ⟨other, member, infinite⟩ := input.infinite_max_witness vertices covered vertex parent small
      have accepted : PathRank.Preferred (fun _ : V => (-1 : Int)) (input.cost vertices.length)
          (vertices.length + 1) (fun child => child ∈ input.moves vertex) (-1) child := by
        simpa only [preferred, small, Bool.false_eq_true, if_false] using chosen
      have selected := PathRank.negative_prefers_infinite (fun _ : V => (-1 : Int)) _ _ _ _ child other
        accepted (by omega) (input.cost_bound vertices.length child) member rfl
        (by simp [cost, infinite])
      exact selected.symm
  | some n =>
    cases small : input.minimizes vertex with
    | true =>
      obtain ⟨other, member, k, found, step⟩ := input.finite_min_witness vertices covered vertex n parent notGoal small
      have comparison := (PathRank.preferred_direction _ _ _ _ _ child other chosen
        (input.cost_bound vertices.length child) (input.cost_bound vertices.length other) member rfl).1
        (show 0 ≤ (if input.minimizes vertex then (0 : Int) else -1) by simp [small])
      have witnessCost : input.cost vertices.length other = some n := by simp [cost, found, step]
      rw [witnessCost] at comparison
      cases next : input.rank vertices.length child with
      | none => simp [cost, next, PathRank.LE] at comparison
      | some m =>
        have lower := (input.rank_table vertices covered).own_finite vertex n notGoal small parent
        have bound := lower.2 child m chosen.1 next
        have upper : m + 1 ≤ n := by simpa [cost, next, PathRank.LE] using comparison
        have equal : n = m + 1 := by omega
        simp [cost, next, equal]
    | false =>
      obtain ⟨other, member, k, found, step⟩ := input.finite_max_witness vertices covered vertex n parent notGoal small
      obtain ⟨m, next, bound⟩ := input.finite_max_all vertices covered vertex n parent notGoal small child chosen.1
      have comparison := (PathRank.preferred_direction _ _ _ _ _ child other chosen
        (input.cost_bound vertices.length child) (input.cost_bound vertices.length other) member rfl).2
        (show (if input.minimizes vertex then (0 : Int) else -1) < 0 by simp [small])
      have upper : n ≤ m + 1 := by simpa [cost, next, found, step, PathRank.LE] using comparison
      have equal : n = m + 1 := by omega
      simp [cost, next, equal]

theorem goal_rank (cap : Nat) (vertex : V) (goal : input.target vertex) : input.rank cap vertex = some 0 := by
  apply (input.computation.computedDistance_some cap 0 vertex).mpr
  exact ⟨Nat.zero_le _, goal, fun earlier impossible => by omega⟩

/-- 有限rankを実現する全同点候補で、次のrankは厳密に一つ減る。 -/
theorem preferred_finite (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex child : V) (notGoal : ¬ input.target vertex)
    (chosen : input.preferred vertices.length vertex child) (n : Nat)
    (finite : input.rank vertices.length vertex = some n) :
    ∃ k, input.rank vertices.length child = some k ∧ k + 1 = n := by
  have equal := input.preferred_rank vertices covered vertex child notGoal chosen
  rw [finite] at equal
  cases next : input.rank vertices.length child with
  | none => simp [cost, next] at equal
  | some k =>
    refine ⟨k, rfl, ?_⟩
    have same : some n = some (k + 1) := by simpa [cost, next] using equal
    exact (Option.some.inj same).symm

theorem preferred_infinite (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (vertex child : V) (chosen : input.preferred vertices.length vertex child)
    (infinite : input.rank vertices.length vertex = none) : input.rank vertices.length child = none := by
  have notGoal : ¬ input.target vertex := by
    intro goal
    have zero := input.goal_rank vertices.length vertex goal
    rw [infinite] at zero
    cases zero
  have equal := input.preferred_rank vertices covered vertex child notGoal chosen
  rw [infinite] at equal
  cases next : input.rank vertices.length child with
  | none => rfl
  | some k => simp [cost, next] at equal

noncomputable def next (cap : Nat) (vertex : V) : V :=
  Classical.choose (input.preferred_exists cap vertex)

theorem next_preferred (cap : Nat) (vertex : V) : input.preferred cap vertex (input.next cap vertex) :=
  (Classical.choose_spec (input.preferred_exists cap vertex)).2

def run (next : V → V) (root : V) : Nat → V
  | 0 => root
  | n + 1 => next (run next root n)

/-- 無限の延長選択を実現する合法な経路がある。実対局の無限継続や引き分け強制とは別。 -/
theorem infinite_run (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (infinite : input.rank vertices.length root = none) :
    ∀ n, input.rank vertices.length (run (input.next vertices.length) root n) = none ∧
      ¬ input.target (run (input.next vertices.length) root n) := by
  intro n
  have stays : ∀ n, input.rank vertices.length (run (input.next vertices.length) root n) = none := by
    intro n
    induction n with
    | zero => exact infinite
    | succ n ih => exact input.preferred_infinite vertices covered _ _ (input.next_preferred _ _) ih
  refine ⟨stays n, ?_⟩
  intro goal
  have zero := input.goal_rank vertices.length _ goal
  rw [stays n] at zero
  cases zero

end Input
end PetaProof.SignedRankGraph
