import PetaProof.EscapeOptimal

/-! 無限距離は計算未了ではない。相手が目標到達を拒否できることを証明する。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V) (target : V → Prop)

theorem escape_outside_own (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (outside : ¬ A.escapeLayer target vertices.length vertex)
    (own : A.owner vertex = A.player) (child : V) (edge : A.edge vertex child) :
    ¬ A.escapeLayer target vertices.length child := by
  intro childInside
  apply outside
  apply A.escapeLayer_complete target vertices covered (vertices.length + 1) vertex
  right
  rw [if_pos own]
  exact ⟨child, edge, childInside⟩

theorem escape_outside_other (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (outside : ¬ A.escapeLayer target vertices.length vertex)
    (other : A.owner vertex ≠ A.player) :
    ∃ child, A.edge vertex child ∧ ¬ A.escapeLayer target vertices.length child := by
  classical
  apply Classical.byContradiction
  intro none
  apply outside
  apply A.escapeLayer_complete target vertices covered (vertices.length + 1) vertex
  right
  rw [if_neg other]
  intro child edge
  apply Classical.byContradiction
  intro childOutside
  exact none ⟨child, edge, childOutside⟩

noncomputable def escapeSpoiler (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) : V := by
  classical
  exact if eligible : ¬ A.escapeLayer target vertices.length vertex ∧ A.owner vertex ≠ A.player then
    Classical.choose (A.escape_outside_other target vertices covered vertex eligible.1 eligible.2)
    else Classical.choose (A.moves_exist vertex)

theorem escapeSpoiler_legal (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    A.edge vertex (A.escapeSpoiler target vertices covered vertex) := by
  classical
  simp only [escapeSpoiler]
  split
  · rename_i eligible
    exact (Classical.choose_spec (A.escape_outside_other target vertices covered vertex eligible.1 eligible.2)).1
  · exact Classical.choose_spec (A.moves_exist vertex)

theorem escapeSpoiler_stays (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (outside : ¬ A.escapeLayer target vertices.length vertex)
    (other : A.owner vertex ≠ A.player) :
    ¬ A.escapeLayer target vertices.length (A.escapeSpoiler target vertices covered vertex) := by
  classical
  have eligible : ¬ A.escapeLayer target vertices.length vertex ∧ A.owner vertex ≠ A.player := ⟨outside, other⟩
  simpa only [escapeSpoiler, dif_pos eligible] using
    (Classical.choose_spec (A.escape_outside_other target vertices covered vertex outside other)).2

/-- 同じ履歴不要の相手応手で、自分の全履歴依存戦略に対して目標を避けられる。 -/
theorem escapeSpoiler_avoids (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (root : V) (outside : ¬ A.escapeLayer target vertices.length root) (strategy : A.Strategy) (n : Nat) :
    ¬ target (A.play strategy (A.escapeSpoiler target vertices covered) root n) := by
  have stays : ∀ i, ¬ A.escapeLayer target vertices.length
      (A.play strategy (A.escapeSpoiler target vertices covered) root i) := by
    intro i
    induction i with
    | zero => simpa only [A.play_start] using outside
    | succ i ih =>
      have follows := A.play_follows_response strategy (A.escapeSpoiler target vertices covered)
        (fun vertex _ => A.escapeSpoiler_legal target vertices covered vertex) root i
      by_cases own : A.owner (A.play strategy (A.escapeSpoiler target vertices covered) root i) = A.player
      · exact A.escape_outside_own target vertices covered _ ih own _ follows.1
      · rw [follows.2 own]
        exact A.escapeSpoiler_stays target vertices covered _ ih own
  intro goal
  exact stays n (A.escapeLayer_mono target (Nat.zero_le vertices.length) _ goal)

end PetaProof.HistoryArena
