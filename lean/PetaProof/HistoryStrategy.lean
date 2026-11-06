import PetaProof.Buchi

/-!
全履歴を受け取る戦略を明示し、履歴不要の反証方策でそれを破れることを示す。
対象は終端を持たない抽象アリーナ。leafの吸収状態化と四回出現規則との対応は別途必要。
-/

namespace PetaProof

universe u

structure HistoryArena (V : Type u) where
  edge : V → V → Prop
  owner : V → Bool
  player : Bool
  bad : V → V → Prop
  moves_exist : ∀ v, ∃ w, edge v w

namespace HistoryArena

variable {V : Type u} (A : HistoryArena V)

/-- 過去の全局面を古い順に渡す。選択手は履歴と現在局面の両方に依存してよい。 -/
structure Strategy where
  choose : List V → V → V
  legal : ∀ past v, A.owner v = A.player → A.edge v (choose past v)

/-- 全局面で合法手があるため、戦略の型が空であることによる自明な反証ではない。 -/
noncomputable def defaultStrategy : A.Strategy where
  choose := fun _ v => Classical.choose (A.moves_exist v)
  legal := fun _ v _ => Classical.choose_spec (A.moves_exist v)

/-- 相手の手だけを固定し、自分の全合法手を残したグラフ。 -/
def FollowsResponse (response : V → V) (v w : V) : Prop :=
  A.edge v w ∧ (A.owner v ≠ A.player → w = response v)

/-- 順位検査で全無限経路のBuchi条件を保証する、履歴不要の相手方策。 -/
structure Counterstrategy where
  response : V → V
  legal : ∀ v, A.owner v ≠ A.player → A.edge v (response v)
  ranking : BuchiRanking (A.FollowsResponse response) A.bad

/-- 相手方策を固定した後、非王手のない循環を排除できれば反証証拠を構成できる。 -/
noncomputable def Counterstrategy.ofNoGoodCycle (response : V → V)
    (legal : ∀ v, A.owner v ≠ A.player → A.edge v (response v))
    (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (acyclic : ∀ v w, (A.FollowsResponse response v w ∧ ¬ A.bad v w) →
      ¬ Reachable (fun x y => A.FollowsResponse response x y ∧ ¬ A.bad x y) w v) :
    A.Counterstrategy where
  response := response
  legal := legal
  ranking := buchiRankingOfNoGoodCycle _ _ vertices covered acyclic

/-- 再帰状態は過去の全局面と現在局面。初期履歴は空とする。 -/
def runState (strategy : A.Strategy) (response : V → V) (root : V) : Nat → List V × V
  | 0 => ([], root)
  | n + 1 =>
    let previous := runState strategy response root n
    (previous.1 ++ [previous.2],
      if A.owner previous.2 = A.player then strategy.choose previous.1 previous.2
      else response previous.2)

def play (strategy : A.Strategy) (response : V → V) (root : V) (n : Nat) : V :=
  (A.runState strategy response root n).2

@[simp] theorem play_start (strategy : A.Strategy) (response : V → V) (root : V) :
    A.play strategy response root 0 = root := rfl

/-- 戦略へ渡す履歴は、生成された対局列の先頭n局面そのものである。 -/
theorem runState_past (strategy : A.Strategy) (response : V → V) (root : V) (n : Nat) :
    (A.runState strategy response root n).1 =
      (List.range n).map (A.play strategy response root) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runState, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [ih]
    rfl

theorem play_follows_response (strategy : A.Strategy) (response : V → V)
    (response_legal : ∀ v, A.owner v ≠ A.player → A.edge v (response v)) (root : V)
    (i : Nat) : A.FollowsResponse response
      (A.play strategy response root i) (A.play strategy response root (i + 1)) := by
  let state := A.runState strategy response root i
  change A.edge state.2 (if A.owner state.2 = A.player then strategy.choose state.1 state.2
      else response state.2) ∧
    (A.owner state.2 ≠ A.player →
      (if A.owner state.2 = A.player then strategy.choose state.1 state.2
      else response state.2) = response state.2)
  by_cases own : A.owner state.2 = A.player
  · simp only [if_pos own]
    exact ⟨strategy.legal state.1 state.2 own, fun other => False.elim (other own)⟩
  · simp only [if_neg own]
    exact ⟨response_legal state.2 own, fun _ => trivial⟩

theorem play_follows (strategy : A.Strategy) (counter : A.Counterstrategy) (root : V)
    (i : Nat) : A.FollowsResponse counter.response
      (A.play strategy counter.response root i) (A.play strategy counter.response root (i + 1)) :=
  A.play_follows_response strategy counter.response counter.legal root i

/-- 無限対局列が、自分の全履歴依存の選択に従うこと。 -/
def Compatible (strategy : A.Strategy) (path : Nat → V) : Prop :=
  ∀ i, A.owner (path i) = A.player →
    path (i + 1) = strategy.choose ((List.range i).map path) (path i)

theorem play_compatible (strategy : A.Strategy) (response : V → V) (root : V) :
    A.Compatible strategy (A.play strategy response root) := by
  intro i own
  change (if A.owner (A.play strategy response root i) = A.player then
    strategy.choose (A.runState strategy response root i).1 (A.play strategy response root i)
    else response (A.play strategy response root i)) = _
  rw [if_pos own, A.runState_past]

/-- 任意の全履歴依存戦略と対局しても、相手方策が非王手を無限回発生させる。 -/
theorem Counterstrategy.defeats_history (counter : A.Counterstrategy) (strategy : A.Strategy)
    (root : V) : ∀ n, ∃ i, n ≤ i ∧
      A.bad (A.play strategy counter.response root i)
        (A.play strategy counter.response root (i + 1)) :=
  counter.ranking.infinitely_bad _ (A.play_follows strategy counter root)

/-- 任意の合法応手に対してco-Buchi条件を保証できる、全履歴依存戦略の存在。 -/
def HistoryWinning (root : V) : Prop :=
  ∃ strategy : A.Strategy, ∀ path : Nat → V, path 0 = root →
    (∀ i, A.edge (path i) (path (i + 1))) → A.Compatible strategy path →
    ∃ n, ∀ i, n ≤ i → ¬ A.bad (path i) (path (i + 1))

/-- 自分の選択手を固定し、相手の全合法手を残したグラフ。 -/
def FollowsChoice (choice : V → V) (v w : V) : Prop :=
  A.edge v w ∧ (A.owner v = A.player → w = choice v)

/-- 無限経路条件を保証する、正側の履歴不要証明書。 -/
structure PositionalCertificate where
  choice : V → V
  legal : ∀ v, A.owner v = A.player → A.edge v (choice v)
  eventual : AllPathsCoBuchi (A.FollowsChoice choice) A.bad

/-- 履歴を参照しない選択も、全履歴依存戦略の特殊な場合として扱える。 -/
def PositionalCertificate.strategy (cert : A.PositionalCertificate) : A.Strategy where
  choose := fun _ v => cert.choice v
  legal := fun _ v own => cert.legal v own

/-- 正側の証拠は、相手の任意の履歴依存の応手に対しても保証を与える。 -/
theorem PositionalCertificate.history_winning (cert : A.PositionalCertificate) (root : V) :
    A.HistoryWinning root := by
  refine ⟨cert.strategy A, ?_⟩
  intro path _ legal compatible
  apply cert.eventual path
  intro i
  exact ⟨legal i, fun own => compatible i own⟩

/-- この反証証拠があれば、任意の履歴依存戦略を許しても勝てない。 -/
theorem Counterstrategy.not_history_winning (counter : A.Counterstrategy) (root : V) :
    ¬ A.HistoryWinning root := by
  rintro ⟨strategy, wins⟩
  obtain ⟨n, eventual⟩ := wins (A.play strategy counter.response root) rfl
    (fun i => (A.play_follows strategy counter root i).1)
    (A.play_compatible strategy counter.response root)
  obtain ⟨i, after, hb⟩ := counter.defeats_history A strategy root n
  exact eventual i after hb

/-- 同じアリーナ全体で、正側の順位証拠と反証方策は両立しない。 -/
theorem Counterstrategy.excludes_coBuchi (counter : A.Counterstrategy) (root : V)
    (strategy : A.Strategy) :
    ¬ AllPathsCoBuchi (A.FollowsResponse counter.response) A.bad := by
  intro safe
  obtain ⟨n, eventual⟩ := safe (A.play strategy counter.response root)
    (A.play_follows strategy counter root)
  obtain ⟨i, after, hb⟩ := counter.defeats_history A strategy root n
  exact eventual i after hb

/-- 正側と反証側の両証明書は、同じ非空アリーナでは両立しない。 -/
theorem certificates_disjoint (cert : A.PositionalCertificate) (counter : A.Counterstrategy)
    (root : V) : False :=
  counter.not_history_winning A root (cert.history_winning A root)

end HistoryArena
end PetaProof
