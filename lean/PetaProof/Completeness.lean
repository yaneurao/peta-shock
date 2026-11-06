import PetaProof.FiniteSink

/-!
通常伝播が閉じ、core内に非空の安全集合がなければ、正の循環条件を満たす
履歴不要方策の領域を取りこぼしていないことを示す。
任意の履歴依存戦略から履歴不要戦略を得る決定性は、ここでは仮定も証明もしていない。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 既に確定した領域への内部手、または閾値以上のleaf。 -/
def GoodExit (won : V → Prop) : Move V → Prop
  | .node w => won w
  | .leaf score => G.threshold ≤ score

/-- 通常のOR/AND伝播で追加できる頂点が、もう残っていないこと。 -/
def OrdinaryClosed (won : V → Prop) : Prop := ∀ v,
  ((G.owner v = G.player ∧ ∃ m, G.legal v m ∧ G.GoodExit won m) ∨
   (G.owner v ≠ G.player ∧ ∀ m, G.legal v m → G.GoodExit won m)) → won v

/-- 相手の非王手辺を除いた元のグラフ。循環頂点が局所処理のcoreとなる。 -/
def OpponentChecking (v w : V) : Prop :=
  G.legal v (.node w) ∧ (G.owner v = G.player ∨ G.check v w)

/-- 良いleafへ出て、循環上では相手が王手を続ける履歴不要方策の証拠。 -/
structure PositionalRegion (possible : V → Prop) where
  choice : V → Move V
  chosen_legal : ∀ v, possible v → G.owner v = G.player → G.legal v (choice v)
  closed : ∀ v, possible v → ∀ m, G.Follows choice v m →
    match m with
    | .node w => possible w
    | .leaf score => G.threshold ≤ score
  cycle_checks : ∀ v w, possible v → G.Follows choice v (.node w) →
    Walk (fun x y => possible x ∧ G.Follows choice x (.node y)) w v →
    G.owner v ≠ G.player → G.check v w

namespace RankedRegion

variable {G} {possible : V → Prop}

/-- 前段階で構成した順位付き保証領域も、この完全性の比較対象に含まれる。 -/
def positional (region : G.RankedRegion possible) : G.PositionalRegion possible where
  choice := region.choice
  chosen_legal := region.chosen_legal
  closed := region.closed
  cycle_checks := by
    intro v w hv edge back other
    apply Classical.byContradiction
    intro not_check
    have decrease := region.opponent_strict v w hv edge other not_check
    have returning := back.nat_antitone region.rank
      (fun x y h => region.decreasing x y h.1 h.2)
    omega

end RankedRegion

namespace PositionalRegion

variable {G} {possible won : V → Prop}

def Internal (region : G.PositionalRegion possible) (a b : {v // possible v}) : Prop :=
  G.Follows region.choice a.val (.node b.val)

/-- この比較対象の方策条件も、単なる名称ではなく実際の下限保証へ接続できる。 -/
def certificate (region : G.PositionalRegion possible) : Certificate {v // possible v} where
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
    let ownEdge := fun x y : {v // possible v} => region.Internal x y ∧
      (G.owner x.val = G.player → G.check x.val y.val)
    have first : ownEdge a b := ⟨edge.1, edge.2.2.2⟩
    have tail : Walk ownEdge b a := back.map (fun _ _ h => ⟨h.1, h.2.2.2⟩)
    let loop : Walk ownEdge a a := .cons first tail
    have all : loop.Every (fun x y => G.check x.val y.val) := by
      apply Walk.every_returning _ _ loop (.nil a)
      intro x y e returning
      by_cases own : G.owner x.val = G.player
      · exact e.2 own
      · exact region.cycle_checks x.val y.val x.property e.1
          (returning.mapVertices Subtype.val (fun u _ h => ⟨u.property, h.1⟩)) own
    apply G.no_mutual_cycle a.val b.val ⟨edge.1.1, all.1⟩
    exact (tail.withEvery _ all.2).mapVertices Subtype.val (fun _ _ h => ⟨h.1.1.1, h.2⟩)
  opponent_cycle_checks := by
    intro a b edge _ _ back other
    exact region.cycle_checks a.val b.val a.property edge
      (back.mapVertices Subtype.val (fun x _ h => ⟨x.property, h⟩)) other

def Residual (region : G.PositionalRegion possible) (won : V → Prop) (v w : V) : Prop :=
  (possible v ∧ ¬ won v) ∧ (possible w ∧ ¬ won w) ∧ G.Follows region.choice v (.node w)

/-- 通常伝播が閉じていれば、未発見の方策領域から確定済み集合を除いても行き止まりはない。 -/
theorem residual_successor (region : G.PositionalRegion possible)
    (ordinary : G.OrdinaryClosed won) (v : V) (hv : possible v ∧ ¬ won v) :
    ∃ w, region.Residual won v w := by
  classical
  by_cases own : G.owner v = G.player
  · have legal := region.chosen_legal v hv.1 own
    cases selected : region.choice v with
    | leaf score =>
      rw [selected] at legal
      have good := region.closed v hv.1 (.leaf score) ⟨legal, fun _ => selected⟩
      exact False.elim (hv.2 (ordinary v (Or.inl ⟨own, .leaf score, legal, good⟩)))
    | node w =>
      rw [selected] at legal
      have follows : G.Follows region.choice v (.node w) := ⟨legal, fun _ => selected⟩
      have child := region.closed v hv.1 (.node w) follows
      have outside : ¬ won w := by
        intro inside
        exact hv.2 (ordinary v (Or.inl ⟨own, .node w, legal, inside⟩))
      exact ⟨w, hv, ⟨child, outside⟩, follows⟩
  · have bad_exit : ∃ m, G.legal v m ∧ ¬ G.GoodExit won m := by
      apply Classical.byContradiction
      intro none
      apply hv.2
      apply ordinary v
      apply Or.inr
      refine ⟨own, ?_⟩
      intro m legal
      apply Classical.byContradiction
      intro bad
      exact none ⟨m, legal, bad⟩
    obtain ⟨m, legal, bad⟩ := bad_exit
    have follows : G.Follows region.choice v m :=
      ⟨legal, fun impossible => False.elim (own impossible)⟩
    have child := region.closed v hv.1 m follows
    cases m with
    | leaf score => exact False.elim (bad child)
    | node w => exact ⟨w, hv, ⟨child, bad⟩, follows⟩

theorem residual_cycle_checks (region : G.PositionalRegion possible) {v w : V}
    (edge : region.Residual won v w) (back : Walk (region.Residual won) w v)
    (other : G.owner v ≠ G.player) : G.check v w :=
  region.cycle_checks v w edge.1.1 edge.2.2
    (back.map (fun _ _ h => ⟨h.1.1, h.2.2⟩)) other

/-- 残余グラフのどの循環頂点も、相手王手グラフの元のcoreに含まれる。 -/
theorem residual_cycle_in_core (region : G.PositionalRegion possible) {v : V}
    (cyclic : CyclicVertex (region.Residual won) v) : CyclicVertex G.OpponentChecking v := by
  obtain ⟨w, edge, ⟨back⟩⟩ := cyclic
  let loop : Walk (region.Residual won) v v := .cons edge back
  have all : loop.Every (fun x y => G.owner x = G.player ∨ G.check x y) := by
    apply Walk.every_returning _ _ loop (.nil v)
    intro x y e returning
    by_cases own : G.owner x = G.player
    · exact Or.inl own
    · exact Or.inr (region.residual_cycle_checks e returning own)
  refine ⟨w, ⟨edge.2.2.1, all.1⟩, ?_⟩
  exact ⟨(back.withEvery _ all.2).map (fun _ _ h => ⟨h.1.2.2.1, h.2⟩)⟩

/-- 最下流成分の自分の手は成分内に留まり、相手の応手は王手で留まるか成功出口になる。 -/
theorem sink_is_safe (region : G.PositionalRegion possible)
    (ordinary : G.OrdinaryClosed won)
    (sink : SinkComponent (region.Residual won) (fun v => possible v ∧ ¬ won v)) :
    G.SafeSet won sink.member := by
  intro v hv
  have source := sink.within v hv
  constructor
  · intro own
    obtain ⟨w, edge⟩ := region.residual_successor ordinary v source
    exact ⟨.node w, edge.2.2.1, Or.inr ⟨sink.closed v w hv edge, Or.inl own⟩⟩
  · intro other m legal
    have follows : G.Follows region.choice v m :=
      ⟨legal, fun impossible => False.elim (other impossible)⟩
    have good := region.closed v source.1 m follows
    cases m with
    | leaf score => exact good
    | node w =>
      by_cases inside : won w
      · exact Or.inl inside
      · have edge : region.Residual won v w := ⟨source, ⟨good, inside⟩, follows⟩
        have child := sink.closed v w hv edge
        obtain ⟨back⟩ := sink.connected w v child hv
        exact Or.inr ⟨child, Or.inr (region.residual_cycle_checks edge back other)⟩

/-- 未発見の履歴不要方策領域があれば、元のcore内に追加可能な非空安全集合が必ず残る。 -/
theorem missing_yields_local_safe (region : G.PositionalRegion possible)
    (ordinary : G.OrdinaryClosed won) (vertices : List V)
    (covered : ∀ v, possible v ∧ ¬ won v → v ∈ vertices)
    (missing : ∃ v, possible v ∧ ¬ won v) :
    ∃ candidate, (∃ v, candidate v) ∧ G.SafeSet won candidate ∧
      ∀ v, candidate v → CyclicVertex G.OpponentChecking v ∧ ¬ won v := by
  obtain ⟨sink⟩ := finite_sink_exists (region.Residual won)
    (fun v => possible v ∧ ¬ won v) vertices covered (fun _ _ edge _ => edge.2.1) missing
  refine ⟨sink.member, sink.nonempty, region.sink_is_safe ordinary sink, ?_⟩
  intro v hv
  exact ⟨region.residual_cycle_in_core
      (sink.cyclic (fun v hv => region.residual_successor ordinary v hv) v hv),
    (sink.within v hv).2⟩

/-- 通常伝播が閉じ、core内の局所削除結果が空なら、この方策の領域は全て確定済みである。 -/
theorem complete_when_local_empty (region : G.PositionalRegion possible)
    (ordinary : G.OrdinaryClosed won) (vertices : List V)
    (covered : ∀ v, possible v ∧ ¬ won v → v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v) :
    ∀ v, possible v → won v := by
  classical
  intro v hv
  apply Classical.byContradiction
  intro outside
  obtain ⟨candidate, ⟨w, hw⟩, safe, within⟩ :=
    region.missing_yields_local_safe ordinary vertices covered ⟨v, hv, outside⟩
  have survives := G.safe_survives (initial := fun x => core x ∧ ¬ won x) safe
    (fun x hx => ⟨covers_core x (within x hx).1, (within x hx).2⟩) n w hw
  exact empty w survives

end PositionalRegion

/-- 履歴不要方策の証拠で保証できる局面。任意の履歴依存戦略を量化した定義ではない。 -/
def PositionalWinning (v : V) : Prop :=
  ∃ possible, Nonempty (G.PositionalRegion possible) ∧ possible v

/-- 健全な確定領域について、停止条件が成り立てば履歴不要の正の保証局面と過不足なく一致する。 -/
theorem stopped_exact_for_positional {won : V → Prop} (sound : G.RankedRegion won)
    (ordinary : G.OrdinaryClosed won) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v) :
    ∀ v, won v ↔ G.PositionalWinning v := by
  intro v
  constructor
  · intro hv
    exact ⟨won, ⟨sound.positional⟩, hv⟩
  · rintro ⟨possible, ⟨region⟩, hv⟩
    exact region.complete_when_local_empty ordinary vertices (fun v _ => covered v)
      core covers_core n empty v hv

end PetaProof.ThresholdGame
