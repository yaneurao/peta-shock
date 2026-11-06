import PetaProof.CoBuchi

/-!
閉じた歩道を反復する無限歩道を構成し、無限歩道上のco-Buchi条件から
悪い辺を含む閉路がないことを逆に導く。戦略の履歴不要決定性とは別の定理。
-/

namespace PetaProof

universe u
variable {V : Type u}

namespace Walk

variable {R : V → V → Prop}

/-- 歩道のi手後の頂点。長さを超える添字では終点を返す。 -/
def vertexAt : {a b : V} → Walk R a b → Nat → V
  | a, _, .nil _, _ => a
  | a, _, .cons _ _, 0 => a
  | _, _, .cons _ tail, i + 1 => tail.vertexAt i

@[simp] theorem at_zero {a b : V} (walk : Walk R a b) : walk.vertexAt 0 = a := by
  cases walk <;> rfl

@[simp] theorem at_steps {a b : V} (walk : Walk R a b) : walk.vertexAt walk.steps = b := by
  induction walk with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem at_edge {a b : V} (walk : Walk R a b) (i : Nat) (within : i < walk.steps) :
    R (walk.vertexAt i) (walk.vertexAt (i + 1)) := by
  induction walk generalizing i with
  | nil => simp [steps] at within
  | cons edge tail ih =>
    cases i with
    | zero => simpa [vertexAt] using edge
    | succ i =>
      exact ih i (by simp only [steps] at within; omega)

/-- 閉じた歩道の終点添字は、先頭へ折り返しても同じ頂点になる。 -/
theorem at_mod {a : V} (loop : Walk R a a) (_positive : 0 < loop.steps)
    (i : Nat) (within : i ≤ loop.steps) : loop.vertexAt (i % loop.steps) = loop.vertexAt i := by
  by_cases equal : i = loop.steps
  · subst i
    simp
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- 同じ有限閉路を無限回反復する経路。 -/
def repeatPath {a : V} (loop : Walk R a a) (i : Nat) : V :=
  loop.vertexAt (i % loop.steps)

theorem repeatPath_legal {a : V} (loop : Walk R a a) (positive : 0 < loop.steps)
    (i : Nat) : R (loop.repeatPath i) (loop.repeatPath (i + 1)) := by
  have within : i % loop.steps < loop.steps := Nat.mod_lt i positive
  have edge := loop.at_edge (i % loop.steps) within
  have next_mod : (i + 1) % loop.steps = (i % loop.steps + 1) % loop.steps := by
    simp only [Nat.add_mod, Nat.mod_mod]
  unfold repeatPath
  rw [next_mod, loop.at_mod positive (i % loop.steps + 1) (by omega)]
  exact edge

/-- 閉路の先頭辺は、反復回数にかかわらず再現される。 -/
theorem repeat_first_edge {a b : V} (edge : R a b) (back : Walk R b a) (n : Nat) :
    let loop : Walk R a a := .cons edge back
    loop.repeatPath (n * loop.steps) = a ∧
      loop.repeatPath (n * loop.steps + 1) = b := by
  dsimp only
  let loop : Walk R a a := .cons edge back
  have positive : 0 < loop.steps := by simp [loop, steps]
  have first : loop.vertexAt 1 = b := by simp [loop, vertexAt]
  change loop.vertexAt ((n * loop.steps) % loop.steps) = a ∧
    loop.vertexAt ((n * loop.steps + 1) % loop.steps) = b
  constructor
  · simp
  · have mod_next : (n * loop.steps + 1) % loop.steps = 1 % loop.steps := by
      simp [Nat.add_mod]
    rw [mod_next, loop.at_mod positive 1 (by omega), first]

end Walk

/-- 全無限歩道で、ある時点以降は悪い辺が現れないという条件。 -/
def AllPathsCoBuchi (R bad : V → V → Prop) : Prop :=
  ∀ path : Nat → V, (∀ i, R (path i) (path (i + 1))) →
    ∃ n, ∀ i, n ≤ i → ¬ bad (path i) (path (i + 1))

/-- 悪い辺の閉路から、その悪い辺が何度でも現れる無限歩道を構成する。 -/
theorem bad_cycle_repeats {R bad : V → V → Prop} {a b : V}
    (edge : R a b) (hb : bad a b) (back : Walk R b a) :
    ∃ path : Nat → V, (∀ i, R (path i) (path (i + 1))) ∧
      ∀ n, ∃ i, n ≤ i ∧ bad (path i) (path (i + 1)) := by
  let loop : Walk R a a := .cons edge back
  have positive : 0 < loop.steps := by simp [loop, Walk.steps]
  refine ⟨loop.repeatPath, loop.repeatPath_legal positive, ?_⟩
  intro n
  have first := Walk.repeat_first_edge edge back n
  change loop.repeatPath (n * loop.steps) = a ∧
    loop.repeatPath (n * loop.steps + 1) = b at first
  refine ⟨n * loop.steps, Nat.le_mul_of_pos_right n positive, ?_⟩
  rw [first.1, first.2]
  exact hb

/-- 逆方向は有限性すら不要。悪い閉路を繰り返す経路が反例になる。 -/
theorem AllPathsCoBuchi.no_bad_cycle {R bad : V → V → Prop}
    (safe : AllPathsCoBuchi R bad) :
    ∀ a b, R a b → bad a b → ¬ Reachable R b a := by
  intro a b edge hb back
  obtain ⟨walk⟩ := back
  obtain ⟨path, legal, recurring⟩ := bad_cycle_repeats edge hb walk
  obtain ⟨n, eventual⟩ := safe path legal
  obtain ⟨i, after, bad_edge⟩ := recurring n
  exact eventual i after bad_edge

/-- 有限グラフでは閉路条件と全無限歩道のco-Buchi条件が同値。 -/
theorem no_bad_cycle_iff_all_paths (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) :
    (∀ a b, R a b → bad a b → ¬ Reachable R b a) ↔ AllPathsCoBuchi R bad := by
  constructor
  · intro safe path legal
    exact (rankingOfNoBadCycle R bad vertices covered safe).eventually_no_bad
      vertices covered path legal
  · exact AllPathsCoBuchi.no_bad_cycle

/-- 有限グラフで無限歩道の条件と減少順位の存在も同値になる。 -/
theorem all_paths_iff_ranking (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) :
    AllPathsCoBuchi R bad ↔ Nonempty (BadEdgeRanking R bad) :=
  (no_bad_cycle_iff_all_paths R bad vertices covered).symm.trans
    (no_bad_cycle_iff_ranking R bad vertices covered)

end PetaProof

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 手は局面ごとに固定するが、勝利条件を閉路ではなく全無限経路で記述する。 -/
structure CoBuchiRegion (possible : V → Prop) where
  choice : V → Move V
  chosen_legal : ∀ v, possible v → G.owner v = G.player → G.legal v (choice v)
  closed : ∀ v, possible v → ∀ m, G.Follows choice v m →
    match m with
    | .node w => possible w
    | .leaf score => G.threshold ≤ score
  eventual : AllPathsCoBuchi
    (fun v w => possible v ∧ G.Follows choice v (.node w))
    (fun v w => G.owner v ≠ G.player ∧ ¬ G.check v w)

variable {G}

/-- 全無限経路の条件から循環条件へ。ここでは有限性を使わない。 -/
def CoBuchiRegion.positional {possible : V → Prop} (region : G.CoBuchiRegion possible) :
    G.PositionalRegion possible where
  choice := region.choice
  chosen_legal := region.chosen_legal
  closed := region.closed
  cycle_checks := by
    intro v w hv edge back other
    apply Classical.byContradiction
    intro noncheck
    exact region.eventual.no_bad_cycle v w ⟨hv, edge⟩ ⟨other, noncheck⟩ ⟨back⟩

/-- 有限グラフの循環条件から全無限経路の条件へ。同じ選択手を保持する。 -/
def PositionalRegion.coBuchi {possible : V → Prop} (region : G.PositionalRegion possible)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) : G.CoBuchiRegion possible where
  choice := region.choice
  chosen_legal := region.chosen_legal
  closed := region.closed
  eventual := (no_bad_cycle_iff_all_paths _ _ vertices covered).mp (by
    intro v w edge hb back
    obtain ⟨walk⟩ := back
    exact hb.2 (region.cycle_checks v w edge.1 edge.2 walk hb.1))

/-- 循環検査を使わず、有限終局と全無限経路の条件で記述した履歴不要の保証局面。 -/
def CoBuchiWinning (G : ThresholdGame V) (v : V) : Prop :=
  ∃ possible, Nonempty (G.CoBuchiRegion possible) ∧ possible v

theorem positional_iff_coBuchi (vertices : List V) (covered : ∀ v, v ∈ vertices) (v : V) :
    G.PositionalWinning v ↔ G.CoBuchiWinning v := by
  constructor
  · rintro ⟨possible, ⟨region⟩, hv⟩
    exact ⟨possible, ⟨region.coBuchi vertices covered⟩, hv⟩
  · rintro ⟨possible, ⟨region⟩, hv⟩
    exact ⟨possible, ⟨region.positional⟩, hv⟩

/-- 停止した閾値解法は、全無限経路の条件で定義した履歴不要保証局面とも一致する。 -/
theorem stopped_exact_for_coBuchi {won : V → Prop} (sound : G.RankedRegion won)
    (ordinary : G.OrdinaryClosed won) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v) :
    ∀ v, won v ↔ G.CoBuchiWinning v := by
  intro v
  exact (G.stopped_exact_for_positional sound ordinary vertices covered core covers_core n empty v).trans
    (positional_iff_coBuchi vertices covered v)

end PetaProof.ThresholdGame
