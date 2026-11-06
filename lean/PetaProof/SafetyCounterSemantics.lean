import PetaProof.SafetyCounter

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

/-- 通知途中では支持を過大評価してよい。ただし生存中の子の辺を通知済みにしてはいけない。 -/
theorem safety_support_complete (indexed : G.IndexedMoves E) (vertex : V)
    (view : SafetyCounter.View E) (counter : SafetyCounter.Counter E)
    (won initial current : V → Prop) (subset : ∀ v, current v → initial v)
    (good : ∀ e ∈ view.outgoing, e ∈ view.good ↔ G.GoodExit won (indexed.move e))
    (internal : ∀ e ∈ view.outgoing, e ∈ view.internal ↔ ∃ w,
      indexed.move e = .node w ∧ ¬ won w ∧ initial w ∧ (G.owner vertex = G.player ∨ G.check vertex w))
    (no_early_notification : ∀ e ∈ view.internal, ∀ w, indexed.move e = .node w →
      current w → counter.seen e = false) :
    ∀ e ∈ view.outgoing, G.SafeMove won current vertex (indexed.move e) → view.safe counter e := by
  intro e member safe
  cases move : indexed.move e with
  | leaf score =>
    exact Or.inl ((good e member).mpr (by simpa only [move, SafeMove, GoodExit] using safe))
  | node w =>
    have supported : won w ∨ (current w ∧ (G.owner vertex = G.player ∨ G.check vertex w)) := by
      simpa only [move, SafeMove] using safe
    by_cases exit : won w
    · exact Or.inl ((good e member).mpr (by simpa only [move, GoodExit] using exit))
    · have live := supported.resolve_left exit
      have inside := (internal e member).mpr ⟨w, move, exit, subset w live.1, live.2⟩
      exact Or.inr ⟨inside, no_early_notification e inside w move live.1⟩

/-- 初期分類と、内部辺の削除通知が現在の候補に追いついた条件から、支持の意味を導く。
    current⊆initialが必要。初期core外の局面を途中で追加する操作は対象にしない。 -/
theorem safety_support_representation (indexed : G.IndexedMoves E) (vertex : V)
    (view : SafetyCounter.View E) (counter : SafetyCounter.Counter E)
    (won initial current : V → Prop) (subset : ∀ v, current v → initial v)
    (good : ∀ e ∈ view.outgoing, e ∈ view.good ↔ G.GoodExit won (indexed.move e))
    (internal : ∀ e ∈ view.outgoing, e ∈ view.internal ↔ ∃ w,
      indexed.move e = .node w ∧ ¬ won w ∧ initial w ∧ (G.owner vertex = G.player ∨ G.check vertex w))
    (delivered : ∀ e ∈ view.internal, ∀ w, indexed.move e = .node w →
      (counter.seen e = false ↔ current w)) :
    ∀ e ∈ view.outgoing, view.safe counter e ↔ G.SafeMove won current vertex (indexed.move e) := by
  intro e member
  constructor
  · intro safe
    rcases safe with exit | ⟨inside, unseen⟩
    · have exit_good := (good e member).mp exit
      cases move : indexed.move e with
      | leaf score => simpa only [move, SafeMove, GoodExit] using exit_good
      | node w => exact Or.inl (by simpa only [move, GoodExit] using exit_good)
    · obtain ⟨w, move, _, _, check⟩ := (internal e member).mp inside
      rw [move]
      exact Or.inr ⟨(delivered e inside w move).mp unseen, check⟩
  · intro safe
    cases move : indexed.move e with
    | leaf score =>
      exact Or.inl ((good e member).mpr (by simpa only [move, SafeMove, GoodExit] using safe))
    | node w =>
      have supported : won w ∨ (current w ∧ (G.owner vertex = G.player ∨ G.check vertex w)) := by
        simpa only [move, SafeMove] using safe
      by_cases exit : won w
      · exact Or.inl ((good e member).mpr (by simpa only [move, GoodExit] using exit))
      · have live := supported.resolve_left exit
        have inside := (internal e member).mpr ⟨w, move, exit, subset w live.1, live.2⟩
        exact Or.inr ⟨inside, (delivered e inside w move).mpr live.1⟩

/-- 通知が完了し、辺ごとの支持がSafeMoveと一致した境界で、局所カウンターを集合仕様へ接続する。
    incomingの走査途中で、このrepresented条件を仮定してはいけない。 -/
theorem safety_counter_canStay (indexed : G.IndexedMoves E) (vertex : V)
    (view : SafetyCounter.View E) (counter : SafetyCounter.Counter E)
    (won current : V → Prop)
    (enumerated : ∀ edge, edge ∈ view.outgoing ↔ edge ∈ indexed.outgoing vertex)
    (represented : ∀ edge ∈ view.outgoing,
      view.safe counter edge ↔ G.SafeMove won current vertex (indexed.move edge)) :
    view.canStay (decide (G.owner vertex = G.player)) counter ↔ G.CanStay won current vertex := by
  classical
  constructor
  · intro stay
    constructor
    · intro own
      obtain ⟨edge, member, safe⟩ := stay.1 (by simp [own])
      exact ⟨indexed.move edge, indexed.legal vertex edge ((enumerated edge).mp member),
        (represented edge member).mp safe⟩
    · intro other move legal
      obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
      have present := (enumerated edge).mpr member
      have safe := (represented edge present).mp (stay.2 (by simp [other]) edge present)
      simpa only [same] using safe
  · intro stay
    constructor
    · intro own
      have self : G.owner vertex = G.player := of_decide_eq_true own
      obtain ⟨move, legal, safe⟩ := stay.1 self
      obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
      have present := (enumerated edge).mpr member
      refine ⟨edge, present, (represented edge present).mpr ?_⟩
      simpa only [same] using safe
    · intro other edge member
      have opponent : G.owner vertex ≠ G.player := by simpa only [decide_eq_false_iff_not] using other
      exact (represented edge member).mpr
        (stay.2 opponent _ (indexed.legal vertex edge ((enumerated edge).mp member)))

/-- 走査途中でも、支持を失った親を削除してよい。
    実際の安全手が支持リストに必ず含まれるという片方向だけで十分である。 -/
theorem safety_counter_invalid_sound (indexed : G.IndexedMoves E) (vertex : V)
    (view : SafetyCounter.View E) (counter : SafetyCounter.Counter E) (won current : V → Prop)
    (enumerated : ∀ edge, edge ∈ view.outgoing ↔ edge ∈ indexed.outgoing vertex)
    (complete : ∀ edge ∈ view.outgoing,
      G.SafeMove won current vertex (indexed.move edge) → view.safe counter edge)
    (invalid : ¬ view.canStay (decide (G.owner vertex = G.player)) counter) :
    ¬ G.CanStay won current vertex := by
  classical
  intro stay
  apply invalid
  constructor
  · intro own
    obtain ⟨move, legal, safe⟩ := stay.1 (of_decide_eq_true own)
    obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
    have present := (enumerated edge).mpr member
    refine ⟨edge, present, complete edge present ?_⟩
    simpa only [same] using safe
  · intro other edge member
    have opponent : G.owner vertex ≠ G.player := by simpa only [decide_eq_false_iff_not] using other
    exact complete edge member
      (stay.2 opponent _ (indexed.legal vertex edge ((enumerated edge).mp member)))

end PetaProof.ThresholdGame
