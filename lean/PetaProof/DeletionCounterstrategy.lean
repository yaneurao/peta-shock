import PetaProof.HistoryStrategy

/-!
安全候補の同期削除が空になれば、最初の削除回を順位として反証方策を構成する。
反証手や順位の存在を前提にせず、OR/AND条件の失敗から取り出す。
終端なしの抽象アリーナが対象で、本番C++のキューを変更するものではない。
-/

namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V)

/-- 悪い辺を一度も使わず、現在の候補内に残れる条件。 -/
def StayGood (current : V → Prop) (v : V) : Prop :=
  (A.owner v = A.player → ∃ w, A.edge v w ∧ ¬ A.bad v w ∧ current w) ∧
  (A.owner v ≠ A.player → ∀ w, A.edge v w → ¬ A.bad v w ∧ current w)

def GoodSafeSet (current : V → Prop) : Prop := ∀ v, current v → A.StayGood current v

/-- 全頂点から始め、条件に違反する頂点だけを毎回削除する。 -/
def goodIter : Nat → V → Prop
  | 0 => fun _ => True
  | n + 1 => fun v => goodIter n v ∧ A.StayGood (goodIter n) v

theorem stayGood_mono {small large : V → Prop} (sub : ∀ v, small v → large v)
    {v : V} (stays : A.StayGood small v) : A.StayGood large v := by
  constructor
  · intro own
    obtain ⟨w, edge, nonbad, inside⟩ := stays.1 own
    exact ⟨w, edge, nonbad, sub w inside⟩
  · intro other w edge
    have safe := stays.2 other w edge
    exact ⟨safe.1, sub w safe.2⟩

/-- 真の安全集合は同期削除のどの回でも消えない。 -/
theorem goodSafeSet_survives {current : V → Prop} (safe : A.GoodSafeSet current) (n : Nat) :
    ∀ v, current v → A.goodIter n v := by
  induction n with
  | zero => exact fun _ _ => trivial
  | succ n ih => exact fun v hv => ⟨ih v hv, A.stayGood_mono ih (safe v hv)⟩

/-- 最初に候補から消える回が存在し、それ以前には消えていない。 -/
theorem first_deletion (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) :
    ∃ k, k ≤ n ∧ ¬ A.goodIter k v ∧ ∀ j, j < k → A.goodIter j v := by
  classical
  obtain ⟨k, hk, minimal⟩ := minimum_on_domain (List.range (n + 1))
    (fun i => i ≤ n ∧ ¬ A.goodIter i v) (fun i => i)
    (by intro i hi; exact List.mem_range.mpr (by omega)) ⟨n, Nat.le_refl _, empty v⟩
  refine ⟨k, hk.1, hk.2, ?_⟩
  intro j before
  apply Classical.byContradiction
  intro absent
  have lower := minimal j ⟨by omega, absent⟩
  omega

noncomputable def deletionTime (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) : Nat :=
  Classical.choose (A.first_deletion n empty v)

theorem deletionTime_spec (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) :
    A.deletionTime n empty v ≤ n ∧ ¬ A.goodIter (A.deletionTime n empty v) v ∧
      ∀ j, j < A.deletionTime n empty v → A.goodIter j v :=
  Classical.choose_spec (A.first_deletion n empty v)

theorem deletionTime_pos (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) :
    0 < A.deletionTime n empty v := by
  have spec := A.deletionTime_spec n empty v
  by_cases zero : A.deletionTime n empty v = 0
  · rw [zero] at spec
    exact False.elim (spec.2.1 trivial)
  · omega

/-- 既に消えているなら、その最初の削除回は現在回以下。 -/
theorem deletionTime_le_of_absent (n : Nat) (empty : ∀ v, ¬ A.goodIter n v)
    (v : V) (j : Nat) (absent : ¬ A.goodIter j v) : A.deletionTime n empty v ≤ j := by
  have spec := A.deletionTime_spec n empty v
  apply Nat.le_of_not_gt
  intro before
  exact absent (spec.2.2 j before)

/-- 初めて削除された直前には候補内にいるが、その時点の継続条件には違反する。 -/
theorem deletion_failure (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) :
    ¬ A.StayGood (A.goodIter (A.deletionTime n empty v - 1)) v := by
  have spec := A.deletionTime_spec n empty v
  have positive := A.deletionTime_pos n empty v
  have previous := spec.2.2 (A.deletionTime n empty v - 1) (by omega)
  intro stays
  have next : A.goodIter ((A.deletionTime n empty v - 1) + 1) v := ⟨previous, stays⟩
  have index : A.deletionTime n empty v - 1 + 1 = A.deletionTime n empty v := by omega
  rw [index] at next
  exact spec.2.1 next

/-- 自分の手番で削除されたなら、全ての悪くない合法手は先に消えた頂点へ進む。 -/
theorem own_good_decreases (n : Nat) (empty : ∀ v, ¬ A.goodIter n v)
    (v w : V) (own : A.owner v = A.player) (edge : A.edge v w) (nonbad : ¬ A.bad v w) :
    A.deletionTime n empty w < A.deletionTime n empty v := by
  have absent : ¬ A.goodIter (A.deletionTime n empty v - 1) w := by
    intro alive
    apply A.deletion_failure n empty v
    exact ⟨fun _ => ⟨w, edge, nonbad, alive⟩,
      fun other => False.elim (other own)⟩
  have earlier := A.deletionTime_le_of_absent n empty w _ absent
  have positive := A.deletionTime_pos n empty v
  omega

/-- 相手の手番で削除されたなら、悪い辺か、先に消えた頂点へ進む合法手を選べる。 -/
theorem response_exists (n : Nat) (empty : ∀ v, ¬ A.goodIter n v)
    (v : V) (other : A.owner v ≠ A.player) :
    ∃ w, A.edge v w ∧ (¬ A.bad v w → A.deletionTime n empty w < A.deletionTime n empty v) := by
  classical
  apply Classical.byContradiction
  intro none
  apply A.deletion_failure n empty v
  refine ⟨fun own => False.elim (other own), ?_⟩
  intro _ w edge
  have nonbad : ¬ A.bad v w := by
    intro bad
    exact none ⟨w, edge, fun good => False.elim (good bad)⟩
  refine ⟨nonbad, ?_⟩
  apply Classical.byContradiction
  intro absent
  have earlier := A.deletionTime_le_of_absent n empty w _ absent
  have positive := A.deletionTime_pos n empty v
  exact none ⟨w, edge, fun _ => by omega⟩

/-- OR/AND削除の失敗証拠から、相手の手を取り出す。 -/
noncomputable def deletionResponse (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (v : V) : V := by
  classical
  exact if other : A.owner v ≠ A.player then
    Classical.choose (A.response_exists n empty v other)
  else Classical.choose (A.moves_exist v)

/-- 候補削除が空になれば、反証方策とその順位を実際に構成できる。 -/
noncomputable def counterstrategyOfEmpty (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) :
    A.Counterstrategy where
  response := A.deletionResponse n empty
  legal := by
    intro v other
    simp only [deletionResponse, dif_pos other]
    exact (Classical.choose_spec (A.response_exists n empty v other)).1
  ranking := {
    rank := A.deletionTime n empty
    strict_good := by
      intro v w follows nonbad
      by_cases own : A.owner v = A.player
      · exact A.own_good_decreases n empty v w own follows.1 nonbad
      · have selected := follows.2 own
        rw [selected]
        simp only [deletionResponse, dif_pos own]
        have chosen := Classical.choose_spec (A.response_exists n empty v own)
        apply chosen.2
        simpa only [selected, deletionResponse, dif_pos own] using nonbad
  }

/-- 空の削除結果から、全履歴依存戦略の不可能性まで接続する。 -/
theorem empty_excludes_history (n : Nat) (empty : ∀ v, ¬ A.goodIter n v) (root : V) :
    ¬ A.HistoryWinning root :=
  (A.counterstrategyOfEmpty n empty).not_history_winning A root

/-- 安全集合内では安全手を選び、それ以外では任意の合法手で全域化する。 -/
noncomputable def goodSafeChoice {current : V → Prop} (safe : A.GoodSafeSet current) (v : V) : V := by
  classical
  exact if hv : current v ∧ A.owner v = A.player then
    Classical.choose ((safe v hv.1).1 hv.2)
  else Classical.choose (A.moves_exist v)

theorem goodSafeChoice_legal {current : V → Prop} (safe : A.GoodSafeSet current)
    (v : V) : A.edge v (A.goodSafeChoice safe v) := by
  classical
  by_cases hv : current v ∧ A.owner v = A.player
  · simp only [goodSafeChoice, dif_pos hv]
    exact (Classical.choose_spec ((safe v hv.1).1 hv.2)).1
  · simp only [goodSafeChoice, dif_neg hv]
    exact Classical.choose_spec (A.moves_exist v)

theorem goodSafeChoice_stays {current : V → Prop} (safe : A.GoodSafeSet current)
    (v w : V) (inside : current v) (follows : A.FollowsChoice (A.goodSafeChoice safe) v w) :
    current w ∧ ¬ A.bad v w := by
  classical
  by_cases own : A.owner v = A.player
  · rw [follows.2 own]
    simp only [goodSafeChoice, dif_pos (And.intro inside own)]
    have chosen := Classical.choose_spec ((safe v inside).1 own)
    exact ⟨chosen.2.2, chosen.2.1⟩
  · have good := (safe v inside).2 own w follows.1
    exact ⟨good.2, good.1⟩

/-- 空でない安全集合の各頂点から、悪い辺を一度も使わない勝利戦略を作れる。 -/
theorem goodSafeSet_history_winning {current : V → Prop} (safe : A.GoodSafeSet current)
    (root : V) (inside : current root) : A.HistoryWinning root := by
  let strategy : A.Strategy := {
    choose := fun _ v => A.goodSafeChoice safe v
    legal := fun _ v _ => A.goodSafeChoice_legal safe v
  }
  refine ⟨strategy, ?_⟩
  intro path begins legal compatible
  have follows (i : Nat) : A.FollowsChoice (A.goodSafeChoice safe) (path i) (path (i + 1)) :=
    ⟨legal i, fun own => compatible i own⟩
  have stays : ∀ i, current (path i) := by
    intro i
    induction i with
    | zero => simpa only [begins] using inside
    | succ i ih => exact (A.goodSafeChoice_stays safe _ _ ih (follows i)).1
  exact ⟨0, fun i _ => (A.goodSafeChoice_stays safe _ _ (stays i) (follows i)).2⟩

/-- 不安定な回には、有限列挙の中から少なくとも1頂点が削除される。 -/
theorem goodIter_population_lt (vertices : List V) (covered : ∀ v, v ∈ vertices) (n : Nat)
    (unstable : ¬ A.GoodSafeSet (A.goodIter n)) :
    ThresholdGame.population vertices (A.goodIter (n + 1)) <
      ThresholdGame.population vertices (A.goodIter n) := by
  classical
  have witness : ∃ v, A.goodIter n v ∧ ¬ A.StayGood (A.goodIter n) v := by
    apply Classical.byContradiction
    intro none
    apply unstable
    intro v inside
    apply Classical.byContradiction
    intro invalid
    exact none ⟨v, inside, invalid⟩
  obtain ⟨v, inside, invalid⟩ := witness
  exact population_strict_subset vertices (A.goodIter (n + 1)) (A.goodIter n)
    (fun _ h => h.1) v (covered v) inside (fun h => invalid h.2)

theorem goodIter_deletion_bound (vertices : List V) (covered : ∀ v, v ∈ vertices) (n : Nat)
    (unstable : ∀ i, i < n → ¬ A.GoodSafeSet (A.goodIter i)) :
    ThresholdGame.population vertices (A.goodIter n) + n ≤ vertices.length := by
  induction n with
  | zero => exact ThresholdGame.population_bound vertices (A.goodIter 0)
  | succ n ih =>
    have previous := ih (fun i hi => unstable i (by omega))
    have decreases := A.goodIter_population_lt vertices covered n (unstable n (by omega))
    omega

/-- 有限N頂点なら、高々N回で安全な集合が残るか空になる。 -/
theorem goodIter_stable_exists (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∃ n, n ≤ vertices.length ∧ A.GoodSafeSet (A.goodIter n) := by
  apply Classical.byContradiction
  intro none
  have unstable : ∀ i, i < vertices.length + 1 → ¬ A.GoodSafeSet (A.goodIter i) := by
    intro i hi safe
    exact none ⟨i, by omega, safe⟩
  have impossible := A.goodIter_deletion_bound vertices covered (vertices.length + 1) unstable
  omega

/-- 全頂点で履歴依存の勝利戦略がないなら、有限回の候補削除は空になる。 -/
theorem empty_of_no_history_winners (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (no_winners : ∀ v, ¬ A.HistoryWinning v) :
    ∃ n, n ≤ vertices.length ∧ ∀ v, ¬ A.goodIter n v := by
  obtain ⟨n, bound, stable⟩ := A.goodIter_stable_exists vertices covered
  exact ⟨n, bound, fun v hv => no_winners v (A.goodSafeSet_history_winning stable v hv)⟩

/-- 勝利頂点が全くない有限アリーナには、全履歴依存戦略を破る履歴不要反証方策がある。 -/
theorem counterstrategy_of_no_history_winners (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (no_winners : ∀ v, ¬ A.HistoryWinning v) : Nonempty A.Counterstrategy := by
  obtain ⟨n, _, empty⟩ := A.empty_of_no_history_winners vertices covered no_winners
  exact ⟨A.counterstrategyOfEmpty n empty⟩

/-- 全頂点が負けであることと、アリーナ全体を覆う反証証拠の存在は同値。 -/
theorem no_history_winners_iff_counterstrategy (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    (∀ v, ¬ A.HistoryWinning v) ↔ Nonempty A.Counterstrategy := by
  constructor
  · exact A.counterstrategy_of_no_history_winners vertices covered
  · rintro ⟨counter⟩ v
    exact counter.not_history_winning A v

/-- 同じ条件を候補削除が空になることでも特徴付けられる。 -/
theorem no_history_winners_iff_empty (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    (∀ v, ¬ A.HistoryWinning v) ↔ ∃ n, n ≤ vertices.length ∧ ∀ v, ¬ A.goodIter n v := by
  constructor
  · exact A.empty_of_no_history_winners vertices covered
  · rintro ⟨n, _, empty⟩ v
    exact A.empty_excludes_history n empty v

end PetaProof.HistoryArena
