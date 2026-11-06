import PetaProof.DeletionCounterstrategy

/-!
確定領域の補集合を切り出し、そこで構成した反証方策を元のアリーナへ戻す。
自分の合法手を勝手に削除せず、相手は領域内へ進む手を必ず持つことが重要。
-/

namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V)

/-- 自分は外へ出られず、相手は領域内で対局を続けられる部分領域。 -/
structure Trap (domain : V → Prop) where
  own_closed : ∀ v w, domain v → A.owner v = A.player → A.edge v w → domain w
  other_move : ∀ v, domain v → A.owner v ≠ A.player → ∃ w, A.edge v w ∧ domain w

/-- 自分の1手または相手の全手で確定領域へ進める頂点が、既に確定していること。 -/
def OrdinaryClosed (won : V → Prop) : Prop := ∀ v,
  ((A.owner v = A.player ∧ ∃ w, A.edge v w ∧ won w) ∨
   (A.owner v ≠ A.player ∧ ∀ w, A.edge v w → won w)) → won v

/-- 通常のOR/AND伝播が閉じていれば、その補集合は反証側が保持できる領域。 -/
def complementTrap {won : V → Prop} (ordinary : A.OrdinaryClosed won) :
    A.Trap (fun v => ¬ won v) where
  own_closed := by
    intro v w outside own edge child
    exact outside (ordinary v (Or.inl ⟨own, w, edge, child⟩))
  other_move := by
    intro v outside other
    apply Classical.byContradiction
    intro none
    apply outside
    apply ordinary v
    refine Or.inr ⟨other, ?_⟩
    intro w edge
    apply Classical.byContradiction
    intro child
    exact none ⟨w, edge, child⟩

namespace Trap

variable {A} {domain : V → Prop} (trap : A.Trap domain)

/-- 領域内の頂点と内部辺をそのまま使う。自分の全合法手は残る。 -/
def restricted : HistoryArena {v // domain v} where
  edge := fun v w => A.edge v.val w.val
  owner := fun v => A.owner v.val
  player := A.player
  bad := fun v w => A.bad v.val w.val
  moves_exist := by
    intro v
    by_cases own : A.owner v.val = A.player
    · obtain ⟨w, edge⟩ := A.moves_exist v.val
      exact ⟨⟨w, trap.own_closed v.val w v.property own edge⟩, edge⟩
    · obtain ⟨w, edge, inside⟩ := trap.other_move v.val v.property own
      exact ⟨⟨w, inside⟩, edge⟩

/-- 有限列挙から領域内の頂点だけを取り、型付きの列挙を作る。 -/
noncomputable def vertices (_trap : A.Trap domain) (all : List V) : List {v // domain v} := by
  classical
  exact all.filterMap (fun v => if h : domain v then some ⟨v, h⟩ else none)

theorem vertices_cover (all : List V) (covered : ∀ v, v ∈ all) (v : {v // domain v}) :
    v ∈ trap.vertices all := by
  classical
  apply List.mem_filterMap.mpr
  refine ⟨v.val, covered v.val, ?_⟩
  simp [vertices, dif_pos v.property]

/-- 領域外では任意の合法手で埋め、反証方策を元の頂点型へ戻す。 -/
noncomputable def liftResponse (counter : trap.restricted.Counterstrategy) (v : V) : V := by
  classical
  exact if inside : domain v then (counter.response ⟨v, inside⟩).val
    else Classical.choose (A.moves_exist v)

theorem liftResponse_legal (counter : trap.restricted.Counterstrategy)
    (v : V) (other : A.owner v ≠ A.player) : A.edge v (trap.liftResponse counter v) := by
  classical
  by_cases inside : domain v
  · simp only [liftResponse, dif_pos inside]
    exact counter.legal ⟨v, inside⟩ other
  · simp only [liftResponse, dif_neg inside]
    exact Classical.choose_spec (A.moves_exist v)

theorem liftResponse_stays (counter : trap.restricted.Counterstrategy) (v w : V)
    (inside : domain v) (follows : A.FollowsResponse (trap.liftResponse counter) v w) : domain w := by
  classical
  by_cases own : A.owner v = A.player
  · exact trap.own_closed v w inside own follows.1
  · rw [follows.2 own]
    simp only [liftResponse, dif_pos inside]
    exact (counter.response ⟨v, inside⟩).property

theorem liftResponse_follows (counter : trap.restricted.Counterstrategy)
    (v w : {v // domain v})
    (follows : A.FollowsResponse (trap.liftResponse counter) v.val w.val) :
    trap.restricted.FollowsResponse counter.response v w := by
  classical
  refine ⟨follows.1, ?_⟩
  intro other
  apply Subtype.ext
  have selected := follows.2 other
  simpa only [liftResponse, dif_pos v.property] using selected

/-- 元の履歴依存戦略との実際の対局も、領域内にとどまる。 -/
theorem lifted_play_stays (counter : trap.restricted.Counterstrategy) (strategy : A.Strategy)
    (root : V) (inside : domain root) :
    ∀ n, domain (A.play strategy (trap.liftResponse counter) root n) := by
  intro n
  induction n with
  | zero => exact inside
  | succ n ih =>
    exact trap.liftResponse_stays counter _ _ ih
      (A.play_follows_response strategy _ (trap.liftResponse_legal counter) root n)

/-- 制限アリーナの反証方策は、元のゲームの任意の全履歴依存戦略も破る。 -/
theorem counter_refutes_original (counter : trap.restricted.Counterstrategy)
    (root : V) (inside : domain root) : ¬ A.HistoryWinning root := by
  rintro ⟨strategy, wins⟩
  let path := A.play strategy (trap.liftResponse counter) root
  have stays := trap.lifted_play_stays counter strategy root inside
  let subpath : Nat → {v // domain v} := fun n => ⟨path n, stays n⟩
  have follows := fun n => A.play_follows_response strategy _ (trap.liftResponse_legal counter) root n
  have recurring := counter.ranking.infinitely_bad subpath
    (fun n => trap.liftResponse_follows counter _ _ (follows n))
  obtain ⟨n, eventual⟩ := wins path rfl (fun n => (follows n).1)
    (A.play_compatible strategy _ root)
  obtain ⟨i, after, hb⟩ := recurring n
  exact eventual i after hb

/-- 制限アリーナの候補削除が空なら、その領域は元のゲームでも負けである。 -/
theorem empty_refutes_original (n : Nat) (empty : ∀ v, ¬ trap.restricted.goodIter n v)
    (root : V) (inside : domain root) : ¬ A.HistoryWinning root :=
  trap.counter_refutes_original (trap.restricted.counterstrategyOfEmpty n empty) root inside

end Trap
end PetaProof.HistoryArena
