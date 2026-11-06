import PetaProof.Infinite

/-!
co-Buchiの保証を否定する側の順位証拠。
悪い辺の間では毎手順位が減り、悪い辺では順位をリセットしてよい。
この証拠の構成可能性（ゲームの決定性）自体は、ここでは仮定も証明もしていない。
-/

namespace PetaProof

universe u
variable {V : Type u}

/-- 悪い辺以外では厳密減少する順位。悪い辺での増加は許す。 -/
structure BuchiRanking (R bad : V → V → Prop) where
  rank : V → Nat
  strict_good : ∀ v w, R v w → ¬ bad v w → rank w < rank v

/-- 悪い辺を取り除いたグラフに閉路がなければ、反証側の順位を構成できる。 -/
noncomputable def buchiRankingOfNoGoodCycle (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices)
    (acyclic : ∀ v w, (R v w ∧ ¬ bad v w) →
      ¬ Reachable (fun x y => R x y ∧ ¬ bad x y) w v) : BuchiRanking R bad := by
  let good := fun v w => R v w ∧ ¬ bad v w
  let ranking := rankingOfNoBadCycle good good vertices covered (by
    intro v w e _
    exact acyclic v w e)
  exact {
    rank := ranking.rank
    strict_good := fun v w e nonbad => ranking.strict v w ⟨e, nonbad⟩ ⟨e, nonbad⟩
  }

namespace BuchiRanking

variable {R bad : V → V → Prop} (ranking : BuchiRanking R bad)

/-- 悪い辺のない有限区間では、区間長だけ順位が減る。 -/
theorem good_segment (path : Nat → V) (legal : ∀ i, R (path i) (path (i + 1)))
    (start length : Nat)
    (good : ∀ i, start ≤ i → i < start + length → ¬ bad (path i) (path (i + 1))) :
    ranking.rank (path (start + length)) + length ≤ ranking.rank (path start) := by
  induction length with
  | zero => simp
  | succ k ih =>
    have previous := ih (by intro i lo hi; exact good i lo (by omega))
    have decrease := ranking.strict_good _ _ (legal (start + k))
      (good (start + k) (by omega) (by omega))
    have next : start + (k + 1) = start + k + 1 := by omega
    rw [next]
    omega

/-- どの時刻からでも、その時点の順位以内の待ち時間で悪い辺が現れる。 -/
theorem bad_within_rank (path : Nat → V) (legal : ∀ i, R (path i) (path (i + 1)))
    (start : Nat) :
    ∃ i, start ≤ i ∧ i ≤ start + ranking.rank (path start) ∧
      bad (path i) (path (i + 1)) := by
  apply Classical.byContradiction
  intro none
  have good : ∀ i, start ≤ i → i < start + (ranking.rank (path start) + 1) →
      ¬ bad (path i) (path (i + 1)) := by
    intro i lo hi hb
    exact none ⟨i, lo, by omega, hb⟩
  have impossible := ranking.good_segment path legal start (ranking.rank (path start) + 1) good
  omega

include ranking in
/-- どの無限経路でも悪い辺が何度でも現れる。 -/
theorem infinitely_bad (path : Nat → V) (legal : ∀ i, R (path i) (path (i + 1))) :
    ∀ n, ∃ i, n ≤ i ∧ bad (path i) (path (i + 1)) := by
  intro n
  obtain ⟨i, after, _, hb⟩ := ranking.bad_within_rank path legal n
  exact ⟨i, after, hb⟩

include ranking in
/-- 全て良い辺からなる閉路は存在しない。有限の反復区間にも適用できる。 -/
theorem no_good_cycle {v w : V} (edge : R v w ∧ ¬ bad v w) :
    ¬ Reachable (fun x y => R x y ∧ ¬ bad x y) w v := by
  intro back
  obtain ⟨walk⟩ := back
  have returning := walk.nat_antitone ranking.rank
    (fun x y h => Nat.le_of_lt (ranking.strict_good x y h.1 h.2))
  have decrease := ranking.strict_good v w edge.1 edge.2
  omega

end BuchiRanking

/-- 全無限経路に悪い辺が何度でも現れるというBuchi条件。 -/
def AllPathsBuchi (R bad : V → V → Prop) : Prop :=
  ∀ path : Nat → V, (∀ i, R (path i) (path (i + 1))) →
    ∀ n, ∃ i, n ≤ i ∧ bad (path i) (path (i + 1))

/-- 全無限経路条件の逆方向。良い辺だけの閉路を反復して矛盾させる。 -/
theorem AllPathsBuchi.no_good_cycle {R bad : V → V → Prop}
    (recurring : AllPathsBuchi R bad) :
    ∀ v w, (R v w ∧ ¬ bad v w) →
      ¬ Reachable (fun x y => R x y ∧ ¬ bad x y) w v := by
  intro v w edge back
  obtain ⟨walk⟩ := back
  let loop : Walk (fun x y => R x y ∧ ¬ bad x y) v v := .cons edge walk
  have positive : 0 < loop.steps := by simp [loop, Walk.steps]
  have legal := loop.repeatPath_legal positive
  obtain ⟨i, _, hb⟩ := recurring loop.repeatPath (fun i => (legal i).1) 0
  exact (legal i).2 hb

/-- 有限グラフで、反証側の無限経路条件と順位証拠は同値。 -/
theorem all_paths_buchi_iff_ranking (R bad : V → V → Prop) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) :
    AllPathsBuchi R bad ↔ Nonempty (BuchiRanking R bad) := by
  constructor
  · intro recurring
    exact ⟨buchiRankingOfNoGoodCycle R bad vertices covered recurring.no_good_cycle⟩
  · rintro ⟨ranking⟩ path legal
    exact ranking.infinitely_bad path legal

end PetaProof
