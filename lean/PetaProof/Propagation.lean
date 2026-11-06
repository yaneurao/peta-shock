import PetaProof.History

/-!
固定した正の閾値について、通常伝播と局所安全集合の追加が下限保証を保つことを示す。
値の最適性・局所集合の最大性・C++のキュー実装は、このファイルの対象ではない。
-/

namespace PetaProof

universe u

inductive Move (V : Type u) where
  | node : V → Move V
  | leaf : Int → Move V

/-- leafの値は固定プレイヤー視点。内部辺の王手情報は着手側についての情報。 -/
structure ThresholdGame (V : Type u) where
  legal : V → Move V → Prop
  owner : V → Bool
  check : V → V → Prop
  player : Bool
  threshold : Int
  mate : Int
  positive : 0 < threshold
  bounded : threshold ≤ mate
  alternating : ∀ v w, legal v (.node w) → owner w ≠ owner v
  nonempty_moves : ∀ v, ∃ m, legal v m
  no_mutual_cycle : ∀ a b, (legal a (.node b) ∧ check a b) →
    Walk (fun x y => legal x (.node y) ∧ check x y) b a → False

namespace ThresholdGame

variable {V : Type u} (G : ThresholdGame V)

/-- 内部手が手番を交代させるため、一方しか着手しない反復区間は存在しない。 -/
theorem loop_not_single_owner {a b : V} (first : G.legal a (.node b))
    (back : Walk (fun x y => G.legal x (.node y)) b a) (p : Bool) :
    ¬ (Walk.cons (R := fun x y => G.legal x (.node y)) first back).Every
      (fun x _ => G.owner x = p) := by
  intro all
  cases back with
  | nil => exact G.alternating a a first rfl
  | cons _ _ => exact G.alternating _ _ first (all.2.1.trans all.1.symm)

/-- 自分は指定した手、相手は任意の合法手を指す。 -/
def Follows (choice : V → Move V) (v : V) (m : Move V) : Prop :=
  G.legal v m ∧ (G.owner v = G.player → choice v = m)

/-- 確定済み集合への出口、良いleaf、または局所集合内の継続。
相手の内部継続は王手に限定する。自分の手は王手でなくてもよい。 -/
def SafeMove (won current : V → Prop) (v : V) : Move V → Prop
  | .leaf score => G.threshold ≤ score
  | .node w => won w ∨ (current w ∧ (G.owner v = G.player ∨ G.check v w))

/-- 閾値を下げるだけなら、既存の保証領域を捨てる必要はない。 -/
def lowerThreshold (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) : ThresholdGame V where
  legal := G.legal
  owner := G.owner
  check := G.check
  player := G.player
  threshold := t
  mate := G.mate
  positive := positive
  bounded := Int.le_trans lower G.bounded
  alternating := G.alternating
  nonempty_moves := G.nonempty_moves
  no_mutual_cycle := G.no_mutual_cycle

/-- 局面が確定した追加集合の順位。後続の追加でも、以前の選択手は変更しない。 -/
structure RankedRegion (won : V → Prop) where
  choice : V → Move V
  rank : V → Nat
  stage : Nat
  rank_bound : ∀ v, won v → rank v ≤ stage
  chosen_legal : ∀ v, won v → G.owner v = G.player → G.legal v (choice v)
  closed : ∀ v, won v → ∀ m, G.Follows choice v m →
    match m with
    | .node w => won w
    | .leaf score => G.threshold ≤ score
  decreasing : ∀ v w, won v → G.Follows choice v (.node w) → rank w ≤ rank v
  opponent_strict : ∀ v w, won v → G.Follows choice v (.node w) →
    G.owner v ≠ G.player → ¬ G.check v w → rank w < rank v

/-- 一度の局所処理で加える集合。確定済み集合とは重ならない。 -/
structure SafeBatch (won current : V → Prop) where
  fresh : ∀ v, current v → ¬ won v
  choice : V → Move V
  chosen_legal : ∀ v, current v → G.owner v = G.player → G.legal v (choice v)
  safe : ∀ v, current v → ∀ m, G.Follows choice v m → G.SafeMove won current v m

namespace SafeBatch

variable {G} {won current : V → Prop}

/-- 自分の1手が安全ならOR、相手の全手が安全ならANDとして追加条件を満たす。 -/
def ofOrAnd (fresh : ∀ v, current v → ¬ won v) (choice : V → Move V)
    (own_legal : ∀ v, current v → G.owner v = G.player → G.legal v (choice v))
    (own_safe : ∀ v, current v → G.owner v = G.player → G.SafeMove won current v (choice v))
    (all_safe : ∀ v, current v → G.owner v ≠ G.player →
      ∀ m, G.legal v m → G.SafeMove won current v m) : G.SafeBatch won current where
  fresh := fresh
  choice := choice
  chosen_legal := own_legal
  safe := by
    intro v hv m follows
    by_cases own : G.owner v = G.player
    · rw [← follows.2 own]
      exact own_safe v hv own
    · exact all_safe v hv own m follows.1

/-- 通常伝播は内部継続を全く使わず、確定済みの子か良いleafだけで追加できる場合。 -/
def ofOrdinary (fresh : ∀ v, current v → ¬ won v) (choice : V → Move V)
    (own_legal : ∀ v, current v → G.owner v = G.player → G.legal v (choice v))
    (good : ∀ v, current v → ∀ m, G.Follows choice v m →
      match m with
      | .node w => won w
      | .leaf score => G.threshold ≤ score) : G.SafeBatch won current where
  fresh := fresh
  choice := choice
  chosen_legal := own_legal
  safe := by
    intro v hv m follows
    cases m with
    | node w => exact Or.inl (good v hv (.node w) follows)
    | leaf score => exact good v hv (.leaf score) follows

end SafeBatch

namespace RankedRegion

variable {G} {won current : V → Prop}

/-- 高い閾値で得た方策と順位は、そのまま低い正の閾値でも使える。 -/
def weaken (region : G.RankedRegion won) (t : Int) (positive : 0 < t)
    (lower : t ≤ G.threshold) : (G.lowerThreshold t positive lower).RankedRegion won where
  choice := region.choice
  rank := region.rank
  stage := region.stage
  rank_bound := region.rank_bound
  chosen_legal := region.chosen_legal
  closed := by
    intro v hv m follows
    have good := region.closed v hv m follows
    cases m with
    | node _ => exact good
    | leaf _ => exact Int.le_trans lower good
  decreasing := region.decreasing
  opponent_strict := region.opponent_strict

/-- 各確定局面に実際に指せる手がある。相手の手番では全合法手が残っている。 -/
theorem has_following_move (region : G.RankedRegion won) (v : V) (hv : won v) :
    ∃ m, G.Follows region.choice v m := by
  by_cases own : G.owner v = G.player
  · exact ⟨region.choice v, region.chosen_legal v hv own, fun _ => rfl⟩
  · obtain ⟨m, legal⟩ := G.nonempty_moves v
    exact ⟨m, legal, fun impossible => False.elim (own impossible)⟩

/-- 確定領域だけに制限した内部手。確定集合外への手がないことはclosedが保証する。 -/
def Internal (region : G.RankedRegion won) (a b : {v // won v}) : Prop :=
  G.Follows region.choice a.val (.node b.val)

/-- 閉じた歩道の相手の非王手には順位の厳密減少が必要なので、そのような枝は循環できない。 -/
theorem opponent_checks (region : G.RankedRegion won) {a b : {v // won v}}
    (edge : region.Internal a b) (back : Walk region.Internal b a)
    (other : G.owner a.val ≠ G.player) : G.check a.val b.val := by
  apply Classical.byContradiction
  intro not_check
  have strict := region.opponent_strict a.val b.val a.property edge other not_check
  have returning := back.nat_antitone (fun x => region.rank x.val)
    (fun x y e => region.decreasing x.val y.val x.property e)
  change region.rank a.val ≤ region.rank b.val at returning
  omega

/-- 相手の循環辺が全て王手なら、自分も王手し続ける循環は双方王手循環となり入力前提に反する。 -/
theorem no_own_cycle (region : G.RankedRegion won) {a b : {v // won v}}
    (edge : region.Internal a b ∧ (G.owner a.val = G.player → G.check a.val b.val))
    (back : Walk (fun x y => region.Internal x y ∧
      (G.owner x.val = G.player → G.check x.val y.val)) b a) : False := by
  let ownEdge := fun x y : {v // won v} => region.Internal x y ∧
    (G.owner x.val = G.player → G.check x.val y.val)
  let loop : Walk ownEdge a a := .cons edge back
  have all_checks : loop.Every (fun x y => G.check x.val y.val) := by
    apply Walk.every_returning _ _ loop (.nil a)
    intro x y e returning
    by_cases own : G.owner x.val = G.player
    · exact e.2 own
    · exact region.opponent_checks e.1 (returning.map (fun _ _ h => h.1)) own
  apply G.no_mutual_cycle a.val b.val ⟨edge.1.1, all_checks.1⟩
  exact (back.withEvery _ all_checks.2).mapVertices Subtype.val
    (fun _ _ h => ⟨h.1.1.1, h.2⟩)

/-- 追加順位の不変条件を満たす領域は、固定閾値の下限保証の検査条件を満たす。 -/
def certificate (region : G.RankedRegion won) : Certificate {v // won v} where
  edge := region.Internal
  owner := fun v => G.owner v.val
  check := fun v w => G.check v.val w.val
  player := G.player
  value := fun _ => G.threshold
  mate := G.mate
  mate_pos := by have := G.positive; have := G.bounded; omega
  bounded := by intro _; have := G.positive; have := G.bounded; constructor <;> omega
  monotone := by intro _ _ _; exact Int.le_refl _
  no_own_cycle := by
    intro a b edge back
    exact region.no_own_cycle ⟨edge.1, edge.2.2.2⟩
      (back.map (fun _ _ h => ⟨h.1, h.2.2.2⟩))
  opponent_cycle_checks := by
    intro a b edge _ _ back other
    exact region.opponent_checks edge back other

/-- 構成された方策で実際に四回出現したときも、正の閾値以上の利得を保証する。 -/
theorem fourfold_guarantee [DecidableEq V] (region : G.RankedRegion won) {a b : {v // won v}}
    (h : Walk region.Internal a b) (v : {v // won v}) (many : 4 ≤ h.visits.count v) :
    ∃ (stem : Walk region.Internal a v) (next : {v // won v})
      (edge : region.Internal v next) (back : Walk region.Internal next v)
      (suffix : Walk region.Internal v b),
      h = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 ∧
      G.threshold ≤ region.certificate.repetitionPayoff edge back := by
  classical
  exact region.certificate.fourfold_from_walk h v many

def empty : G.RankedRegion (fun _ => False) where
  choice := fun _ => .leaf 0
  rank := fun _ => 0
  stage := 0
  rank_bound := by intro _ impossible; contradiction
  chosen_legal := by intro _ impossible; contradiction
  closed := by intro _ impossible; contradiction
  decreasing := by intro _ _ impossible; contradiction
  opponent_strict := by intro _ _ impossible; contradiction

noncomputable def extendedChoice (old : G.RankedRegion won) (batch : G.SafeBatch won current)
    (v : V) : Move V := by
  classical
  exact if current v then batch.choice v else old.choice v

noncomputable def extendedRank (old : G.RankedRegion won) (v : V) : Nat := by
  classical
  exact if current v then old.stage + 1 else old.rank v

/-- 通常伝播でも局所安全集合でも、1つの追加集合として同じ順位不変条件を保つ。 -/
noncomputable def extend (old : G.RankedRegion won) (batch : G.SafeBatch won current) :
    G.RankedRegion (fun v => won v ∨ current v) := by
  classical
  have not_new (v : V) (hv : won v) : ¬ current v := by
    intro hnew
    exact batch.fresh v hnew hv
  have follows_new (v : V) (hv : current v) (m : Move V)
      (h : G.Follows (old.extendedChoice batch) v m) : G.Follows batch.choice v m := by
    simpa only [Follows, extendedChoice, if_pos hv] using h
  have follows_old (v : V) (hv : ¬ current v) (m : Move V)
      (h : G.Follows (old.extendedChoice batch) v m) : G.Follows old.choice v m := by
    simpa only [Follows, extendedChoice, if_neg hv] using h
  exact {
    choice := old.extendedChoice batch
    rank := old.extendedRank (current := current)
    stage := old.stage + 1
    rank_bound := by
      intro v hv
      by_cases hnew : current v
      · simp only [extendedRank, if_pos hnew]
        exact Nat.le_refl _
      · have hold : won v := hv.resolve_right hnew
        simp only [extendedRank, if_neg hnew]
        have := old.rank_bound v hold
        omega
    chosen_legal := by
      intro v hv own
      by_cases hnew : current v
      · simpa only [extendedChoice, if_pos hnew] using batch.chosen_legal v hnew own
      · simpa only [extendedChoice, if_neg hnew] using
          old.chosen_legal v (hv.resolve_right hnew) own
    closed := by
      intro v hv m follows
      by_cases hnew : current v
      · have safe := batch.safe v hnew m (follows_new v hnew m follows)
        cases m with
        | leaf score => exact safe
        | node w => exact safe.elim Or.inl (fun h => Or.inr h.1)
      · have safe := old.closed v (hv.resolve_right hnew) m (follows_old v hnew m follows)
        cases m with
        | leaf score => exact safe
        | node w => exact Or.inl safe
    decreasing := by
      intro v w hv follows
      by_cases hnew : current v
      · have safe := batch.safe v hnew (.node w) (follows_new v hnew (.node w) follows)
        simp only [extendedRank, if_pos hnew]
        rcases safe with hold | ⟨hnext, _⟩
        · simp only [if_neg (not_new w hold)]
          have := old.rank_bound w hold
          omega
        · simp only [if_pos hnext]
          exact Nat.le_refl _
      · have hold := hv.resolve_right hnew
        have oldFollow := follows_old v hnew (.node w) follows
        have next := old.closed v hold (.node w) oldFollow
        simp only [extendedRank, if_neg hnew, if_neg (not_new w next)]
        exact old.decreasing v w hold oldFollow
    opponent_strict := by
      intro v w hv follows other not_check
      by_cases hnew : current v
      · have safe := batch.safe v hnew (.node w) (follows_new v hnew (.node w) follows)
        have hold : won w := by
          rcases safe with hold | ⟨_, internal⟩
          · exact hold
          · exact False.elim (internal.elim other not_check)
        simp only [extendedRank, if_pos hnew, if_neg (not_new w hold)]
        have := old.rank_bound w hold
        omega
      · have hold := hv.resolve_right hnew
        have oldFollow := follows_old v hnew (.node w) follows
        have next := old.closed v hold (.node w) oldFollow
        simp only [extendedRank, if_neg hnew, if_neg (not_new w next)]
        exact old.opponent_strict v w hold oldFollow other not_check
  }

end RankedRegion
end ThresholdGame
end PetaProof
