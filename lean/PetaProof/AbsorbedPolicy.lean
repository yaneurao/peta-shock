import PetaProof.Absorption

/-!
元の閾値ゲームの順位付き保証領域と、吸収状態付きアリーナの保証領域を相互変換する。
leafをまとめても、合法手・自分の選択手・相手の全応手を保つ。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

def extendWon (won : V → Prop) : AbsorbedState V → Prop
  | .node v => won v
  | .success => True
  | .failure => False

/-- 保証領域外の選択も合法手で埋め、アリーナ側の全域な方策に合わせる。 -/
noncomputable def regionChoice {won : V → Prop} (region : G.RankedRegion won) (v : V) : Move V := by
  classical
  exact if won v then region.choice v else Classical.choose (G.nonempty_moves v)

theorem regionChoice_legal {won : V → Prop} (region : G.RankedRegion won)
    (v : V) (own : G.owner v = G.player) : G.legal v (G.regionChoice region v) := by
  classical
  by_cases inside : won v
  · simpa only [regionChoice, if_pos inside] using region.chosen_legal v inside own
  · simpa only [regionChoice, if_neg inside] using Classical.choose_spec (G.nonempty_moves v)

/-- 元の領域へ成功吸収状態を加え、leafへの手で順位が増えないよう内部順位を1上げる。 -/
noncomputable def liftRankedRegion {won : V → Prop} (region : G.RankedRegion won) :
    G.absorbedArena.RankedPolicy (extendWon won) := by
  classical
  let selected := fun state : AbsorbedState V => match state with
    | .node v => G.encodeMove (G.regionChoice region v)
    | .success => .success
    | .failure => .failure
  let rank := fun state : AbsorbedState V => match state with
    | .node v => region.rank v + 1
    | _ => 0
  have realizes (v : V) (inside : won v) (target : AbsorbedState V)
      (follows : G.absorbedArena.FollowsChoice selected (.node v) target) :
      ∃ m, G.Follows region.choice v m ∧ G.encodeMove m = target := by
    apply G.realize_follows region.choice v target (region.chosen_legal v inside) follows.1
    intro own
    simpa only [selected, regionChoice, if_pos inside] using follows.2 own
  exact {
    choice := selected
    legal := by
      intro state own
      cases state with
      | node v =>
        exact (G.absorbed_edge_iff v _).mpr ⟨G.regionChoice region v, G.regionChoice_legal region v own, rfl⟩
      | success => rfl
      | failure => rfl
    rank := rank
    ceiling := region.stage + 1
    bounded := by
      intro state inside
      cases state with
      | node v =>
        have bound := region.rank_bound v inside
        change region.rank v + 1 ≤ region.stage + 1
        omega
      | success => exact Nat.zero_le _
      | failure => exact False.elim inside
    closed := by
      intro state target inside follows
      cases state with
      | failure => exact False.elim inside
      | success =>
        have ends : target = .success := follows.1
        rw [ends]
        trivial
      | node v =>
        obtain ⟨m, hm, equal⟩ := realizes v inside target follows
        subst target
        cases m with
        | node w => exact region.closed v inside (.node w) hm
        | leaf score =>
          have good := region.closed v inside (.leaf score) hm
          simp only [encodeMove, if_pos good, extendWon]
    decreasing := by
      intro state target inside follows
      cases state with
      | failure => exact False.elim inside
      | success =>
        have ends : target = .success := follows.1
        rw [ends]
        exact Nat.le_refl _
      | node v =>
        obtain ⟨m, hm, equal⟩ := realizes v inside target follows
        subst target
        cases m with
        | node w =>
          have lower := region.decreasing v w inside hm
          change region.rank w + 1 ≤ region.rank v + 1
          omega
        | leaf score =>
          have good := region.closed v inside (.leaf score) hm
          simp only [encodeMove, if_pos good]
          exact Nat.zero_le _
    strict_bad := by
      intro state target inside follows bad
      cases state with
      | failure => exact False.elim inside
      | success => cases target <;> cases bad
      | node v =>
        obtain ⟨m, hm, equal⟩ := realizes v inside target follows
        subst target
        cases m with
        | node w =>
          have lower := region.opponent_strict v w inside hm bad.1 bad.2
          change region.rank w + 1 < region.rank v + 1
          omega
        | leaf score =>
          have good := region.closed v inside (.leaf score) hm
          simp only [encodeMove, if_pos good] at bad
          exact False.elim bad
  }

/-- アリーナの選択先を、それを実現する元の合法手へ復元する。 -/
noncomputable def decodeChoice {won : AbsorbedState V → Prop}
    (policy : G.absorbedArena.RankedPolicy won) (v : V) : Move V := by
  classical
  exact if own : G.owner v = G.player then
    Classical.choose ((G.absorbed_edge_iff v (policy.choice (.node v))).mp (policy.legal (.node v) own))
  else Classical.choose (G.nonempty_moves v)

theorem decodeChoice_spec {won : AbsorbedState V → Prop}
    (policy : G.absorbedArena.RankedPolicy won) (v : V) (own : G.owner v = G.player) :
    G.legal v (G.decodeChoice policy v) ∧ G.encodeMove (G.decodeChoice policy v) = policy.choice (.node v) := by
  classical
  simp only [decodeChoice, dif_pos own]
  exact Classical.choose_spec ((G.absorbed_edge_iff v (policy.choice (.node v))).mp (policy.legal (.node v) own))

theorem decode_follows {won : AbsorbedState V → Prop} (policy : G.absorbedArena.RankedPolicy won)
    (v : V) (m : Move V) (follows : G.Follows (G.decodeChoice policy) v m) :
    G.absorbedArena.FollowsChoice policy.choice (.node v) (G.encodeMove m) := by
  refine ⟨(G.absorbed_edge_iff v _).mpr ⟨m, follows.1, rfl⟩, ?_⟩
  intro own
  rw [← follows.2 own]
  exact (G.decodeChoice_spec policy v own).2

/-- 吸収アリーナの保証を元の閾値ゲームへ戻す。失敗leafが選ばれないことも導く。 -/
noncomputable def extractRankedRegion {won : AbsorbedState V → Prop}
    (policy : G.absorbedArena.RankedPolicy won) : G.RankedRegion (fun v => won (.node v)) where
  choice := G.decodeChoice policy
  rank := fun v => policy.rank (.node v)
  stage := policy.ceiling
  rank_bound := fun v inside => policy.bounded (.node v) inside
  chosen_legal := fun v _ own => (G.decodeChoice_spec policy v own).1
  closed := by
    intro v inside m follows
    have child := policy.closed (.node v) (G.encodeMove m) inside (G.decode_follows policy v m follows)
    cases m with
    | node w => exact child
    | leaf score =>
      apply Classical.byContradiction
      intro bad
      simp only [encodeMove, if_neg bad] at child
      exact G.failure_not_in_policy policy child
  decreasing := by
    intro v w inside follows
    exact policy.decreasing (.node v) (.node w) inside (G.decode_follows policy v (.node w) follows)
  opponent_strict := by
    intro v w inside follows other noncheck
    exact policy.strict_bad (.node v) (.node w) inside
      (G.decode_follows policy v (.node w) follows) ⟨other, noncheck⟩

end PetaProof.ThresholdGame
