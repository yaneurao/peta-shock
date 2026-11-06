import PetaProof.Completeness

/-!
循環上に悪い辺がないという条件から、有限の減少順位を構成する。
さらに有限歩道中の悪い辺の回数と、無限歩道上での有限回性を証明する。
履歴依存戦略を履歴不要戦略に変換する決定性とは区別する。
-/

namespace PetaProof

universe u
variable {V : Type u}

theorem population_mono (vertices : List V) {small large : V → Prop}
    (sub : ∀ v, small v → large v) :
    ThresholdGame.population vertices small ≤ ThresholdGame.population vertices large := by
  classical
  unfold ThresholdGame.population
  induction vertices with
  | nil => simp
  | cons v rest ih =>
    by_cases hs : small v
    · simp [hs, sub v hs, ih]
    · by_cases hl : large v
      · simp only [List.filter_cons, decide_eq_false hs, decide_eq_true hl, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        omega
      · simpa [hs, hl] using ih

/-- 全辺で非増加、悪い辺では厳密減少する自然数順位。 -/
structure BadEdgeRanking (R bad : V → V → Prop) where
  rank : V → Nat
  decreasing : ∀ v w, R v w → rank w ≤ rank v
  strict : ∀ v w, R v w → bad v w → rank w < rank v

/-- 到達集合の大きさによる存在証明。実行用アルゴリズムへの変更ではない。 -/
noncomputable def rankingOfNoBadCycle (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices)
    (no_bad_cycle : ∀ v w, R v w → bad v w → ¬ Reachable R w v) :
    BadEdgeRanking R bad where
  rank := fun v => ThresholdGame.population vertices (Reachable R v)
  decreasing := by
    intro v w e
    exact population_mono vertices (fun _ path => (Reachable.edge e).trans path)
  strict := by
    intro v w e hb
    exact population_strict_subset vertices (Reachable R w) (Reachable R v)
      (fun _ path => (Reachable.edge e).trans path) v (covered v)
      (Reachable.refl v) (no_bad_cycle v w e hb)

namespace Walk

noncomputable def badCount {R : V → V → Prop} (bad : V → V → Prop)
    {a b : V} : Walk R a b → Nat := by
  classical
  intro h
  exact match h with
  | .nil _ => 0
  | .cons (a := a) (b := b) _ tail => (if bad a b then 1 else 0) + badCount bad tail

/-- 悪い辺の総数は開始順位以下。経路数の列挙は不要。 -/
theorem badCount_bound {R bad : V → V → Prop} (ranking : BadEdgeRanking R bad)
    {a b : V} (h : Walk R a b) : h.badCount bad + ranking.rank b ≤ ranking.rank a := by
  classical
  induction h with
  | nil => simp [badCount]
  | @cons a b c e tail ih =>
    have nonincrease := ranking.decreasing a b e
    by_cases hb : bad a b
    · have decrease := ranking.strict a b e hb
      simp only [badCount, if_pos hb]
      omega
    · simp only [badCount, if_neg hb]
      omega

end Walk

namespace BadEdgeRanking

variable {R bad : V → V → Prop} (ranking : BadEdgeRanking R bad)

include ranking in
/-- 厳密減少する辺を含む閉路は作れない。 -/
theorem no_bad_cycle {v w : V} (edge : R v w) (hb : bad v w) :
    ¬ Reachable R w v := by
  intro back
  obtain ⟨walk⟩ := back
  have returning := walk.nat_antitone ranking.rank ranking.decreasing
  have decrease := ranking.strict v w edge hb
  omega

theorem along (path : Nat → V) (legal : ∀ i, R (path i) (path (i + 1)))
    (n k : Nat) : ranking.rank (path (n + k)) ≤ ranking.rank (path n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step := ranking.decreasing _ _ (legal (n + k))
    have : n + (k + 1) = n + k + 1 := by omega
    rw [this]
    omega

include ranking in
/-- 任意の無限歩道で、ある時点以降は悪い辺が一度も現れない。 -/
theorem eventually_no_bad (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (path : Nat → V) (legal : ∀ i, R (path i) (path (i + 1))) :
    ∃ n, ∀ i, n ≤ i → ¬ bad (path i) (path (i + 1)) := by
  obtain ⟨v, ⟨n, at_n⟩, minimal⟩ := minimum_on_domain vertices
    (fun v => ∃ i, path i = v) ranking.rank (fun v _ => covered v)
    ⟨path 0, 0, rfl⟩
  refine ⟨n, ?_⟩
  intro i after hb
  have lower := minimal (path (i + 1)) ⟨i + 1, rfl⟩
  have upper := ranking.along path legal n (i - n)
  have equal : n + (i - n) = i := by omega
  rw [equal, at_n] at upper
  have decrease := ranking.strict _ _ (legal i) hb
  omega

end BadEdgeRanking

/-- 有限グラフでは「悪い辺を含む閉路なし」と「減少順位あり」は同値。 -/
theorem no_bad_cycle_iff_ranking (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) :
    (∀ v w, R v w → bad v w → ¬ Reachable R w v) ↔
      Nonempty (BadEdgeRanking R bad) := by
  constructor
  · intro safe
    exact ⟨rankingOfNoBadCycle R bad vertices covered safe⟩
  · rintro ⟨ranking⟩ v w edge hb
    exact ranking.no_bad_cycle edge hb

/-- 閉路条件があれば、任意の有限歩道中の悪い辺は列挙頂点数以下。 -/
theorem bad_edges_bounded_by_vertices (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices)
    (safe : ∀ v w, R v w → bad v w → ¬ Reachable R w v)
    {a b : V} (walk : Walk R a b) : walk.badCount bad ≤ vertices.length := by
  let ranking := rankingOfNoBadCycle R bad vertices covered safe
  have count := walk.badCount_bound ranking
  have bound : ranking.rank a ≤ vertices.length :=
    ThresholdGame.population_bound vertices (Reachable R a)
  omega

end PetaProof

namespace PetaProof.ThresholdGame.PositionalRegion

universe u
variable {V : Type u} {G : ThresholdGame V} {possible : V → Prop}

/-- 循環条件だけを持つ方策にも、順位付き保証領域を与えられる。 -/
noncomputable def ranked (region : G.PositionalRegion possible) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) : G.RankedRegion possible := by
  let R := fun v w => possible v ∧ G.Follows region.choice v (.node w)
  let bad := fun v w => G.owner v ≠ G.player ∧ ¬ G.check v w
  let ranking := rankingOfNoBadCycle R bad vertices covered (by
    intro v w e hb back
    obtain ⟨walk⟩ := back
    exact hb.2 (region.cycle_checks v w e.1 e.2 walk hb.1))
  exact {
    choice := region.choice
    rank := ranking.rank
    stage := vertices.length
    rank_bound := fun v _ => population_bound vertices (Reachable R v)
    chosen_legal := region.chosen_legal
    closed := region.closed
    decreasing := fun v w hv e => ranking.decreasing v w ⟨hv, e⟩
    opponent_strict := fun v w hv e other noncheck => ranking.strict v w ⟨hv, e⟩ ⟨other, noncheck⟩
  }

/-- 履歴不要方策に従う無限対局では、相手の非王手は有限回しか現れない。 -/
theorem eventually_opponent_checks (region : G.PositionalRegion possible)
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (path : Nat → V) (inside : ∀ i, possible (path i))
    (legal : ∀ i, G.Follows region.choice (path i) (.node (path (i + 1)))) :
    ∃ n, ∀ i, n ≤ i → G.owner (path i) ≠ G.player → G.check (path i) (path (i + 1)) := by
  let regionRanked := region.ranked vertices covered
  let ranking : BadEdgeRanking
      (fun v w => possible v ∧ G.Follows region.choice v (.node w))
      (fun v w => G.owner v ≠ G.player ∧ ¬ G.check v w) := {
    rank := regionRanked.rank
    decreasing := fun v w e => regionRanked.decreasing v w e.1 e.2
    strict := fun v w e hb => regionRanked.opponent_strict v w e.1 e.2 hb.1 hb.2
  }
  obtain ⟨n, eventually⟩ := ranking.eventually_no_bad vertices covered path
    (fun i => ⟨inside i, legal i⟩)
  refine ⟨n, ?_⟩
  intro i after other
  apply Classical.byContradiction
  intro noncheck
  exact eventually i after ⟨other, noncheck⟩

end PetaProof.ThresholdGame.PositionalRegion
