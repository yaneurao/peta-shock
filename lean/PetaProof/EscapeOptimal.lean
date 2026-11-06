import PetaProof.EscapeLayers

/-! 到達層の最初の段数は、全履歴依存戦略を許した最短保証手数と一致する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V) (target : V → Prop)

/-- 目標への最初の到達までを測る。相手の全応手と、自分の実際の履歴依存選択を含む。 -/
def escapeWithin (strategy : A.Strategy) : List V → Nat → V → Prop
  | _, 0, vertex => target vertex
  | past, n + 1, vertex => target vertex ∨
      ∀ child, A.edge vertex child →
        (A.owner vertex = A.player → child = strategy.choose past vertex) →
          escapeWithin strategy (past ++ [vertex]) n child

theorem escapeWithin_layer (strategy : A.Strategy) (past : List V) (n : Nat) (vertex : V)
    (guaranteed : A.escapeWithin target strategy past n vertex) : A.escapeLayer target n vertex := by
  induction n generalizing past vertex with
  | zero => exact guaranteed
  | succ n ih =>
    rcases guaranteed with goal | replies
    · exact Or.inl goal
    · right
      by_cases own : A.owner vertex = A.player
      · rw [if_pos own]
        exact ⟨strategy.choose past vertex, strategy.legal past vertex own,
          ih _ _ (replies _ (strategy.legal past vertex own) (fun _ => rfl))⟩
      · rw [if_neg own]
        exact fun child edge => ih _ _ (replies child edge (fun turn => False.elim (own turn)))

/-- 自分の全履歴選択が、一段下の子を選ぶこと。同じ距離の最適候補は自由に切り替えられる。 -/
def EscapeOptimal (vertices : List V) (strategy : A.Strategy) : Prop :=
  ∀ past vertex, A.escapeLayer target vertices.length vertex → ¬ target vertex → A.owner vertex = A.player →
    A.escapeLayer target vertices.length (strategy.choose past vertex) ∧
      A.escapeRank target vertices.length (strategy.choose past vertex) + 1 = A.escapeRank target vertices.length vertex

noncomputable def escapeStrategy (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) : A.Strategy := by
  classical
  let choice := fun vertex => if eligible : A.escapeLayer target vertices.length vertex ∧
      ¬ target vertex ∧ A.owner vertex = A.player then
    Classical.choose (A.own_escape_successor target vertices covered vertex eligible.1 eligible.2.1 eligible.2.2)
    else Classical.choose (A.moves_exist vertex)
  exact {
    choose := fun _ vertex => choice vertex
    legal := by
      intro past vertex own
      simp only [choice]
      split
      · rename_i eligible
        exact (Classical.choose_spec (A.own_escape_successor target vertices covered vertex
          eligible.1 eligible.2.1 eligible.2.2)).1
      · exact Classical.choose_spec (A.moves_exist vertex)
  }

theorem escapeStrategy_optimal (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) :
    A.EscapeOptimal target vertices (A.escapeStrategy target vertices covered) := by
  classical
  intro past vertex inside outside own
  have guard : A.escapeLayer target vertices.length vertex ∧ ¬ target vertex ∧ A.owner vertex = A.player :=
    ⟨inside, outside, own⟩
  have selected := Classical.choose_spec (A.own_escape_successor target vertices covered vertex inside outside own)
  simpa only [escapeStrategy, dif_pos guard] using selected.2

theorem escapeOptimal_guarantees (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (strategy : A.Strategy) (optimal : A.EscapeOptimal target vertices strategy)
    (past : List V) (n : Nat) (vertex : V) (inside : A.escapeLayer target vertices.length vertex)
    (bound : A.escapeRank target vertices.length vertex ≤ n) : A.escapeWithin target strategy past n vertex := by
  induction n generalizing past vertex with
  | zero => exact (A.escapeRank_zero_iff target vertices.length vertex inside).mp (Nat.eq_zero_of_le_zero bound)
  | succ n ih =>
    by_cases goal : target vertex
    · exact Or.inl goal
    · right
      intro child edge follows
      have next : A.escapeLayer target vertices.length child ∧
          A.escapeRank target vertices.length child < A.escapeRank target vertices.length vertex := by
        by_cases own : A.owner vertex = A.player
        · have selected := optimal past vertex inside goal own
          rw [← follows own] at selected
          exact ⟨selected.1, by omega⟩
        · exact A.other_escape_successor target vertices covered vertex inside goal own child edge
      exact ih _ child next.1 (by omega)

/-- どの履歴依存戦略でも、最初の到達層より短い手数を保証できない。 -/
theorem escape_lower_bound (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (strategy : A.Strategy) (past : List V) (n : Nat) (vertex : V)
    (guaranteed : A.escapeWithin target strategy past n vertex) :
    A.escapeLayer target vertices.length vertex ∧ A.escapeRank target vertices.length vertex ≤ n := by
  have layer := A.escapeWithin_layer target strategy past n vertex guaranteed
  have inside := A.escapeLayer_complete target vertices covered n vertex layer
  exact ⟨inside, (A.escapeRank_le_iff target vertices.length vertex inside n).mpr layer⟩

/-- 同じ履歴不要戦略が、全ての有限距離の頂点で最短保証手数を実現する。 -/
theorem escape_minimax (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : A.escapeLayer target vertices.length vertex) (n : Nat) :
    (∃ strategy : A.Strategy, A.escapeWithin target strategy [] n vertex) ↔
      A.escapeRank target vertices.length vertex ≤ n := by
  constructor
  · rintro ⟨strategy, guaranteed⟩
    exact (A.escape_lower_bound target vertices covered strategy [] n vertex guaranteed).2
  · intro bound
    exact ⟨A.escapeStrategy target vertices covered,
      A.escapeOptimal_guarantees target vertices covered _ (A.escapeStrategy_optimal target vertices covered)
        [] n vertex inside bound⟩

theorem escape_infinite_no_bound (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (outside : ¬ A.escapeLayer target vertices.length vertex)
    (strategy : A.Strategy) (past : List V) (n : Nat) : ¬ A.escapeWithin target strategy past n vertex := by
  intro guaranteed
  exact outside (A.escape_lower_bound target vertices covered strategy past n vertex guaranteed).1

/-- 自分のどの有限距離の子についても、子の距離+1より親の最短距離が大きくなることはない。 -/
theorem escape_own_cost (vertices : List V) (vertex child : V)
    (inside : A.escapeLayer target vertices.length vertex) (own : A.owner vertex = A.player)
    (edge : A.edge vertex child) (childInside : A.escapeLayer target vertices.length child) :
    A.escapeRank target vertices.length vertex ≤ A.escapeRank target vertices.length child + 1 := by
  apply (A.escapeRank_le_iff target vertices.length vertex inside _).mpr
  right
  rw [if_pos own]
  exact ⟨child, edge, (A.escapeRank_spec target vertices.length child childInside).2.1⟩

/-- 相手番の最大値は実際の子で達成される。全辺単位長なのでmin/maxのBellman式となる。 -/
theorem escape_other_max (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (inside : A.escapeLayer target vertices.length vertex) (notTarget : ¬ target vertex)
    (other : A.owner vertex ≠ A.player) :
    ∃ child, A.edge vertex child ∧ A.escapeLayer target vertices.length child ∧
      A.escapeRank target vertices.length child + 1 = A.escapeRank target vertices.length vertex := by
  classical
  apply Classical.byContradiction
  intro none
  have positive : 0 < A.escapeRank target vertices.length vertex :=
    Nat.pos_of_ne_zero (fun zero => notTarget ((A.escapeRank_zero_iff target vertices.length vertex inside).mp zero))
  obtain ⟨first, edge⟩ := A.moves_exist vertex
  have firstSpec := A.other_escape_successor target vertices covered vertex inside notTarget other first edge
  have firstNe : A.escapeRank target vertices.length first + 1 ≠ A.escapeRank target vertices.length vertex :=
    fun equal => none ⟨first, edge, firstSpec.1, equal⟩
  have parentLarge : 2 ≤ A.escapeRank target vertices.length vertex := by omega
  have children (child : V) (edge : A.edge vertex child) :
      A.escapeLayer target (A.escapeRank target vertices.length vertex - 2) child := by
    have spec := A.other_escape_successor target vertices covered vertex inside notTarget other child edge
    have different : A.escapeRank target vertices.length child + 1 ≠ A.escapeRank target vertices.length vertex :=
      fun equal => none ⟨child, edge, spec.1, equal⟩
    exact (A.escapeRank_le_iff target vertices.length child spec.1 _).mp (by omega)
  have earlier : A.escapeLayer target ((A.escapeRank target vertices.length vertex - 2) + 1) vertex :=
    Or.inr (by rw [if_neg other]; exact children)
  have bound := (A.escapeRank_le_iff target vertices.length vertex inside _).mpr earlier
  omega

/-- 全最短候補と相手の全応手を含む、目標到達前の降下グラフ。 -/
def EscapeDescent (vertices : List V) (vertex child : V) : Prop :=
  A.escapeLayer target vertices.length vertex ∧ ¬ target vertex ∧ A.edge vertex child ∧
    (A.owner vertex = A.player → A.escapeLayer target vertices.length child ∧
      A.escapeRank target vertices.length child + 1 = A.escapeRank target vertices.length vertex)

theorem escapeDescent_strict (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    {vertex child : V} (edge : A.EscapeDescent target vertices vertex child) :
    A.escapeRank target vertices.length child < A.escapeRank target vertices.length vertex := by
  by_cases own : A.owner vertex = A.player
  · have selected := edge.2.2.2 own
    omega
  · exact (A.other_escape_successor target vertices covered vertex edge.1 edge.2.1 own child edge.2.2.1).2

theorem escapeDescent_no_cycle (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    {a b : V} (edge : A.EscapeDescent target vertices a b)
    (back : Walk (A.EscapeDescent target vertices) b a) : False := by
  have strict := A.escapeDescent_strict target vertices covered edge
  have lower := back.nat_antitone (A.escapeRank target vertices.length)
    (fun _ _ found => Nat.le_of_lt (A.escapeDescent_strict target vertices covered found))
  omega

end PetaProof.HistoryArena
