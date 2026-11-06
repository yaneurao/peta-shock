import PetaProof.Determinacy

/-!
閾値以上のleafを成功吸収状態、閾値未満を失敗吸収状態に変換する。
成功では悪い辺がなく、失敗では悪い辺が毎回現れる。
四回出現規則との同値性は別途必要であり、このファイルでは仮定しない。
-/

namespace PetaProof

universe u

inductive AbsorbedState (V : Type u) where
  | node : V → AbsorbedState V
  | success : AbsorbedState V
  | failure : AbsorbedState V

namespace ThresholdGame

variable {V : Type u} (G : ThresholdGame V)

def encodeMove : Move V → AbsorbedState V
  | .node v => .node v
  | .leaf score => if G.threshold ≤ score then .success else .failure

/-- leafを選ぶ各手を成功・失敗へ写す。内部手と王手情報は変えない。 -/
def absorbedEdge : AbsorbedState V → AbsorbedState V → Prop
  | .node v, .node w => G.legal v (.node w)
  | .node v, .success => ∃ score, G.legal v (.leaf score) ∧ G.threshold ≤ score
  | .node v, .failure => ∃ score, G.legal v (.leaf score) ∧ ¬ G.threshold ≤ score
  | .success, target => target = .success
  | .failure, target => target = .failure

def absorbedArena : HistoryArena (AbsorbedState V) where
  edge := G.absorbedEdge
  owner := fun state => match state with
    | .node v => G.owner v
    | _ => G.player
  player := G.player
  bad := fun source target => match source, target with
    | .node v, .node w => G.owner v ≠ G.player ∧ ¬ G.check v w
    | .failure, .failure => True
    | _, _ => False
  moves_exist := by
    intro state
    cases state with
    | success => exact ⟨.success, rfl⟩
    | failure => exact ⟨.failure, rfl⟩
    | node v =>
      obtain ⟨m, legal⟩ := G.nonempty_moves v
      cases m with
      | node w => exact ⟨.node w, legal⟩
      | leaf score =>
        by_cases good : G.threshold ≤ score
        · exact ⟨.success, score, legal, good⟩
        · exact ⟨.failure, score, legal, good⟩

/-- 成功と失敗の2状態を足すだけで、有限性を保つ。 -/
def absorbedVertices (_G : ThresholdGame V) (vertices : List V) : List (AbsorbedState V) :=
  .success :: .failure :: vertices.map .node

theorem absorbedVertices_length (vertices : List V) :
    (G.absorbedVertices vertices).length = vertices.length + 2 := by
  simp only [absorbedVertices, List.length_cons, List.length_map]

theorem absorbedVertices_cover (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (state : AbsorbedState V) : state ∈ G.absorbedVertices vertices := by
  cases state with
  | success => simp [absorbedVertices]
  | failure => simp [absorbedVertices]
  | node v => simp [absorbedVertices, covered v]

/-- 内部頂点からの辺は、元の合法手を写したものに限る。 -/
theorem absorbed_edge_iff (v : V) (target : AbsorbedState V) :
    G.absorbedArena.edge (.node v) target ↔
      ∃ m, G.legal v m ∧ G.encodeMove m = target := by
  constructor
  · intro edge
    cases target with
    | node w => exact ⟨.node w, edge, rfl⟩
    | success =>
      obtain ⟨score, legal, good⟩ := edge
      exact ⟨.leaf score, legal, by simp [encodeMove, good]⟩
    | failure =>
      obtain ⟨score, legal, bad⟩ := edge
      exact ⟨.leaf score, legal, by simp [encodeMove, bad]⟩
  · rintro ⟨m, legal, equal⟩
    subst target
    cases m with
    | node w => exact legal
    | leaf score =>
      by_cases good : G.threshold ≤ score
      · simp only [encodeMove, if_pos good]
        exact ⟨score, legal, good⟩
      · simp only [encodeMove, if_neg good]
        exact ⟨score, legal, good⟩

/-- 自分の選択手を保持し、相手の吸収状態への手も元の合法leafへ戻せる。 -/
theorem realize_follows (choice : V → Move V) (v : V) (target : AbsorbedState V)
    (legal : G.owner v = G.player → G.legal v (choice v))
    (edge : G.absorbedArena.edge (.node v) target)
    (selected : G.owner v = G.player → target = G.encodeMove (choice v)) :
    ∃ m, G.Follows choice v m ∧ G.encodeMove m = target := by
  by_cases own : G.owner v = G.player
  · exact ⟨choice v, ⟨legal own, fun _ => rfl⟩, (selected own).symm⟩
  · obtain ⟨m, hm, equal⟩ := (G.absorbed_edge_iff v target).mp edge
    exact ⟨m, ⟨hm, fun impossible => False.elim (own impossible)⟩, equal⟩

/-- 失敗吸収状態を含む順位付き保証領域は存在しない。 -/
theorem failure_not_in_policy {won : AbsorbedState V → Prop}
    (policy : G.absorbedArena.RankedPolicy won) : ¬ won .failure := by
  intro inside
  have selected : policy.choice .failure = .failure := policy.legal .failure rfl
  have follows : G.absorbedArena.FollowsChoice policy.choice .failure .failure :=
    ⟨rfl, fun _ => selected.symm⟩
  have impossible := policy.strict_bad .failure .failure inside follows trivial
  omega

/-- 成功吸収状態は、悪い辺を一度も使わない安全集合である。 -/
theorem success_safe : G.absorbedArena.GoodSafeSet (fun state => state = .success) := by
  intro state inside
  subst state
  constructor
  · intro _
    exact ⟨.success, rfl, fun h => h, rfl⟩
  · intro other
    exact False.elim (other rfl)

theorem success_history_winning : G.absorbedArena.HistoryWinning .success :=
  G.absorbedArena.goodSafeSet_history_winning G.success_safe .success rfl

theorem failure_not_history_winning (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ¬ G.absorbedArena.HistoryWinning .failure := by
  intro winning
  obtain ⟨won, ⟨policy⟩, inside⟩ :=
    (G.absorbedArena.history_winning_iff_ranked (G.absorbedVertices vertices)
      (G.absorbedVertices_cover vertices covered) .failure).mp winning
  exact G.failure_not_in_policy policy inside

end ThresholdGame
end PetaProof
