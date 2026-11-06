import PetaProof.Residual

/-!
終端なしのアリーナで、領域上の履歴不要方策とco-Buchi順位を扱う。
保証領域を併合し、有限グラフでは最大の領域を構成できることを示す。
-/

namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V)

structure RankedPolicy (won : V → Prop) where
  choice : V → V
  legal : ∀ v, A.owner v = A.player → A.edge v (choice v)
  rank : V → Nat
  ceiling : Nat
  bounded : ∀ v, won v → rank v ≤ ceiling
  closed : ∀ v w, won v → A.FollowsChoice choice v w → won w
  decreasing : ∀ v w, won v → A.FollowsChoice choice v w → rank w ≤ rank v
  strict_bad : ∀ v w, won v → A.FollowsChoice choice v w → A.bad v w → rank w < rank v

namespace RankedPolicy

variable {A} {won : V → Prop}

/-- 保証領域内からは、相手の全履歴依存応手に対しても勝利できる。 -/
theorem history_winning (policy : A.RankedPolicy won) (vertices : List V)
    (covered : ∀ v, v ∈ vertices) (root : V) (inside : won root) : A.HistoryWinning root := by
  let strategy : A.Strategy := {
    choose := fun _ v => policy.choice v
    legal := fun _ v own => policy.legal v own
  }
  refine ⟨strategy, ?_⟩
  intro path begins legal compatible
  have follows (i : Nat) : A.FollowsChoice policy.choice (path i) (path (i + 1)) :=
    ⟨legal i, fun own => compatible i own⟩
  have stays : ∀ i, won (path i) := by
    intro i
    induction i with
    | zero => simpa only [begins] using inside
    | succ i ih => exact policy.closed _ _ ih (follows i)
  let ranking : BadEdgeRanking (fun v w => won v ∧ A.FollowsChoice policy.choice v w) A.bad := {
    rank := policy.rank
    decreasing := fun v w e => policy.decreasing v w e.1 e.2
    strict := fun v w e => policy.strict_bad v w e.1 e.2
  }
  exact ranking.eventually_no_bad vertices covered path (fun i => ⟨stays i, follows i⟩)

/-- 空領域にも全域化した合法方策を与えられる。 -/
noncomputable def empty (A : HistoryArena V) : A.RankedPolicy (fun _ => False) where
  choice := fun v => Classical.choose (A.moves_exist v)
  legal := fun v _ => Classical.choose_spec (A.moves_exist v)
  rank := fun _ => 0
  ceiling := 0
  bounded := fun _ h => False.elim h
  closed := fun _ _ h => False.elim h
  decreasing := fun _ _ h => False.elim h
  strict_bad := fun _ _ h => False.elim h

/-- 旧領域へ入った後は旧方策に固定し、新領域の順位には十分なオフセットを足す。 -/
noncomputable def union {other : V → Prop} (left : A.RankedPolicy won)
    (right : A.RankedPolicy other) : A.RankedPolicy (fun v => won v ∨ other v) := by
  classical
  let choice := fun v => if won v then left.choice v else right.choice v
  let rank := fun v => if won v then left.rank v else left.ceiling + 1 + right.rank v
  have left_follows (v w : V) (inside : won v) (follows : A.FollowsChoice choice v w) :
      A.FollowsChoice left.choice v w := by
    refine ⟨follows.1, ?_⟩
    intro own
    simpa only [choice, if_pos inside] using follows.2 own
  have right_follows (v w : V) (outside : ¬ won v) (follows : A.FollowsChoice choice v w) :
      A.FollowsChoice right.choice v w := by
    refine ⟨follows.1, ?_⟩
    intro own
    simpa only [choice, if_neg outside] using follows.2 own
  exact {
    choice := choice
    legal := by
      intro v own
      by_cases inside : won v
      · simpa only [choice, if_pos inside] using left.legal v own
      · simpa only [choice, if_neg inside] using right.legal v own
    rank := rank
    ceiling := left.ceiling + 1 + right.ceiling
    bounded := by
      intro v inside
      by_cases old : won v
      · have bound := left.bounded v old
        simp only [rank, if_pos old]
        omega
      · have bound := right.bounded v (inside.resolve_left old)
        simp only [rank, if_neg old]
        omega
    closed := by
      intro v w inside follows
      by_cases old : won v
      · exact Or.inl (left.closed v w old (left_follows v w old follows))
      · exact Or.inr (right.closed v w (inside.resolve_left old) (right_follows v w old follows))
    decreasing := by
      intro v w inside follows
      by_cases old : won v
      · have lf := left_follows v w old follows
        have child := left.closed v w old lf
        simpa only [rank, if_pos old, if_pos child] using left.decreasing v w old lf
      · have rf := right_follows v w old follows
        by_cases child : won w
        · have bound := left.bounded w child
          simp only [rank, if_neg old, if_pos child]
          omega
        · have lower := right.decreasing v w (inside.resolve_left old) rf
          simp only [rank, if_neg old, if_neg child]
          omega
    strict_bad := by
      intro v w inside follows bad
      by_cases old : won v
      · have lf := left_follows v w old follows
        have child := left.closed v w old lf
        simpa only [rank, if_pos old, if_pos child] using left.strict_bad v w old lf bad
      · have rf := right_follows v w old follows
        by_cases child : won w
        · have bound := left.bounded w child
          simp only [rank, if_neg old, if_pos child]
          omega
        · have lower := right.strict_bad v w (inside.resolve_left old) rf bad
          simp only [rank, if_neg old, if_neg child]
          omega
  }

/-- 旧領域への出口か、悪い辺なしで新領域に残る手があれば、同じ高さの順位で追加できる。 -/
noncomputable def addGood {current : V → Prop} (old : A.RankedPolicy won)
    (fresh : ∀ v, current v → ¬ won v) (choice : V → V)
    (legal : ∀ v, current v → A.owner v = A.player → A.edge v (choice v))
    (safe : ∀ v w, current v → A.FollowsChoice choice v w → won w ∨ (current w ∧ ¬ A.bad v w)) :
    A.RankedPolicy (fun v => won v ∨ current v) := by
  classical
  let selected := fun v => if current v then choice v else old.choice v
  let rank := fun v => if won v then old.rank v else old.ceiling + 1
  have old_follows (v w : V) (hv : won v) (follows : A.FollowsChoice selected v w) :
      A.FollowsChoice old.choice v w := by
    have outside : ¬ current v := fun h => fresh v h hv
    exact ⟨follows.1, fun own => by simpa only [selected, if_neg outside] using follows.2 own⟩
  have new_follows (v w : V) (hv : current v) (follows : A.FollowsChoice selected v w) :
      A.FollowsChoice choice v w :=
    ⟨follows.1, fun own => by simpa only [selected, if_pos hv] using follows.2 own⟩
  exact {
    choice := selected
    legal := by
      intro v own
      by_cases hv : current v
      · simpa only [selected, if_pos hv] using legal v hv own
      · simpa only [selected, if_neg hv] using old.legal v own
    rank := rank
    ceiling := old.ceiling + 1
    bounded := by
      intro v _
      by_cases hv : won v
      · have bound := old.bounded v hv
        simp only [rank, if_pos hv]
        omega
      · simp only [rank, if_neg hv]
        omega
    closed := by
      intro v w inside follows
      rcases inside with hv | hv
      · exact Or.inl (old.closed v w hv (old_follows v w hv follows))
      · exact (safe v w hv (new_follows v w hv follows)).elim Or.inl (fun h => Or.inr h.1)
    decreasing := by
      intro v w inside follows
      by_cases hv : won v
      · have lf := old_follows v w hv follows
        have child := old.closed v w hv lf
        simpa only [rank, if_pos hv, if_pos child] using old.decreasing v w hv lf
      · by_cases child : won w
        · have bound := old.bounded w child
          simp only [rank, if_neg hv, if_pos child]
          omega
        · simp only [rank, if_neg hv, if_neg child]
          exact Nat.le_refl _
    strict_bad := by
      intro v w inside follows bad
      by_cases hv : won v
      · have lf := old_follows v w hv follows
        have child := old.closed v w hv lf
        simpa only [rank, if_pos hv, if_pos child] using old.strict_bad v w hv lf bad
      · by_cases child : won w
        · have bound := old.bounded w child
          simp only [rank, if_neg hv, if_pos child]
          omega
        · have good := (safe v w (inside.resolve_left hv) (new_follows v w (inside.resolve_left hv) follows)).resolve_left child
          exact False.elim (good.2 bad)
  }

end RankedPolicy

/-- 全ての順位付き保証領域を含む、最大の保証集合であること。 -/
def PolicyMaximal (won : V → Prop) : Prop :=
  ∀ other, A.RankedPolicy other → ∀ v, other v → won v

/-- 有限グラフでは、方策と順位を持つ最大保証領域が存在する。 -/
theorem maximal_policy_exists (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∃ won, Nonempty (A.RankedPolicy won) ∧ A.PolicyMaximal won := by
  classical
  let achievable := fun k => ∃ won, Nonempty (A.RankedPolicy won) ∧
    ThresholdGame.population vertices won = k
  have bounded : ∀ k, achievable k → k ≤ vertices.length := by
    rintro k ⟨won, _, equal⟩
    rw [← equal]
    exact ThresholdGame.population_bound vertices won
  obtain ⟨k, ⟨won, ⟨policy⟩, count⟩, minimum⟩ := minimum_on_domain (List.range (vertices.length + 1))
    achievable (fun k => vertices.length - k)
    (fun k hk => List.mem_range.mpr (by have := bounded k hk; omega))
    ⟨ThresholdGame.population vertices (fun _ => False),
      (fun _ => False), ⟨RankedPolicy.empty A⟩, rfl⟩
  refine ⟨won, ⟨policy⟩, ?_⟩
  intro other right v inside
  apply Classical.byContradiction
  intro outside
  let combined := policy.union right
  have bigger := population_strict_subset vertices won (fun v => won v ∨ other v)
    (fun _ h => Or.inl h) v (covered v) (Or.inr inside) outside
  have lower := minimum (ThresholdGame.population vertices (fun v => won v ∨ other v))
    ⟨(fun v => won v ∨ other v), ⟨combined⟩, rfl⟩
  have old_bound := ThresholdGame.population_bound vertices won
  have new_bound := ThresholdGame.population_bound vertices (fun v => won v ∨ other v)
  omega

end PetaProof.HistoryArena
