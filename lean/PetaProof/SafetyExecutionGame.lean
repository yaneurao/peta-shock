import PetaProof.SafetyExecutionTermination

namespace PetaProof.SafetyExecution

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

/-- 初期のgood/internal分類と辺IDの意味。C++の構築処理との対応は別に証明する。 -/
structure GameModel (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop) : Prop where
  own : ∀ vertex, graph.own vertex = decide (G.owner vertex = G.player)
  outgoing : ∀ vertex, graph.eligible vertex = true → ∀ edge,
    edge ∈ (graph.view vertex).outgoing ↔ edge ∈ indexed.outgoing vertex
  good : ∀ vertex, graph.eligible vertex = true → ∀ edge, edge ∈ (graph.view vertex).outgoing →
    (edge ∈ (graph.view vertex).good ↔ G.GoodExit won (indexed.move edge))
  internal : ∀ vertex, graph.eligible vertex = true → ∀ edge, edge ∈ (graph.view vertex).outgoing →
    (edge ∈ (graph.view vertex).internal ↔ ∃ w, indexed.move edge = .node w ∧
      ¬ won w ∧ graph.eligible w = true ∧ (G.owner vertex = G.player ∨ G.check vertex w))
  target : ∀ vertex edge, edge ∈ (graph.view vertex).internal → indexed.move edge = .node (graph.target edge)

omit [DecidableEq V] [DecidableEq E] in
theorem GameModel.safe_iff (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop)
    (model : GameModel graph indexed won) (kept : V → Prop)
    (subset : ∀ vertex, kept vertex → graph.eligible vertex = true)
    (vertex : V) (eligible : graph.eligible vertex = true) (edge : E) (member : edge ∈ (graph.view vertex).outgoing) :
    graph.safe kept vertex edge ↔ G.SafeMove won kept vertex (indexed.move edge) := by
  constructor
  · intro safe
    rcases safe with good | ⟨internal, child⟩
    · have exit := (model.good vertex eligible edge member).mp good
      cases move : indexed.move edge with
      | leaf score => simpa only [move, ThresholdGame.GoodExit, ThresholdGame.SafeMove] using exit
      | node w => exact Or.inl (by simpa only [move, ThresholdGame.GoodExit] using exit)
    · obtain ⟨w, move, _, _, check⟩ := (model.internal vertex eligible edge member).mp internal
      have same : w = graph.target edge := Move.node.inj (move.symm.trans (model.target vertex edge internal))
      rw [move]
      exact Or.inr ⟨by simpa only [same] using child, check⟩
  · intro safe
    cases move : indexed.move edge with
    | leaf score =>
      exact Or.inl ((model.good vertex eligible edge member).mpr
        (by simpa only [move, ThresholdGame.GoodExit, ThresholdGame.SafeMove] using safe))
    | node w =>
      have supported : won w ∨ (kept w ∧ (G.owner vertex = G.player ∨ G.check vertex w)) := by
        simpa only [move, ThresholdGame.SafeMove] using safe
      by_cases exit : won w
      · exact Or.inl ((model.good vertex eligible edge member).mpr
          (by simpa only [move, ThresholdGame.GoodExit] using exit))
      · have live := supported.resolve_left exit
        have internal := (model.internal vertex eligible edge member).mpr ⟨w, move, exit, subset w live.1, live.2⟩
        have same : w = graph.target edge := Move.node.inj (move.symm.trans (model.target vertex edge internal))
        exact Or.inr ⟨internal, by simpa only [same] using live.1⟩

omit [DecidableEq V] [DecidableEq E] in
theorem GameModel.canStay_iff (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop)
    (model : GameModel graph indexed won) (kept : V → Prop)
    (subset : ∀ vertex, kept vertex → graph.eligible vertex = true) (vertex : V)
    (eligible : graph.eligible vertex = true) :
    graph.canStay kept vertex ↔ G.CanStay won kept vertex := by
  constructor
  · intro stay
    constructor
    · intro own
      obtain ⟨edge, member, safe⟩ := stay.1 (by simp [model.own, own])
      exact ⟨indexed.move edge, indexed.legal vertex edge ((model.outgoing vertex eligible edge).mp member),
        (model.safe_iff graph indexed won kept subset vertex eligible edge member).mp safe⟩
    · intro opponent move legal
      obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
      have present := (model.outgoing vertex eligible edge).mpr member
      have safe := (model.safe_iff graph indexed won kept subset vertex eligible edge present).mp
        (stay.2 (by simp [model.own, opponent]) edge present)
      simpa only [same] using safe
  · intro stay
    constructor
    · intro own
      have self : G.owner vertex = G.player := by simpa only [model.own vertex, decide_eq_true_eq] using own
      obtain ⟨move, legal, safe⟩ := stay.1 self
      obtain ⟨edge, member, same⟩ := indexed.covers vertex move legal
      have present := (model.outgoing vertex eligible edge).mpr member
      refine ⟨edge, present, (model.safe_iff graph indexed won kept subset vertex eligible edge present).mpr ?_⟩
      simpa only [same] using safe
    · intro opponent edge member
      have other : G.owner vertex ≠ G.player := by simpa only [model.own vertex, decide_eq_false_iff_not] using opponent
      exact (model.safe_iff graph indexed won kept subset vertex eligible edge member).mpr
        (stay.2 other _ (indexed.legal vertex edge ((model.outgoing vertex eligible edge).mp member)))

omit [DecidableEq V] [DecidableEq E] in
theorem GameModel.safeSet_iff (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop)
    (model : GameModel graph indexed won) (kept : V → Prop)
    (subset : ∀ vertex, kept vertex → graph.eligible vertex = true) :
    graph.SafeSet kept ↔ G.SafeSet won kept := by
  constructor
  · intro safe vertex member
    exact (model.canStay_iff graph indexed won kept subset vertex (subset vertex member)).mp (safe vertex member)
  · intro safe vertex member
    exact (model.canStay_iff graph indexed won kept subset vertex (subset vertex member)).mpr (safe vertex member)

/-- 有限の局所実行を、従来の閾値ゲームの最大安全集合へ接続する。 -/
theorem solves_game (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop)
    (model : GameModel graph indexed won) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    ∃ n finish, Run graph (initial graph vertices) n finish ∧ Stopped finish ∧
      G.SafeSet won (alive finish) ∧ (∀ vertex, alive finish vertex → graph.eligible vertex = true) ∧
      ∀ kept, G.SafeSet won kept → (∀ vertex, kept vertex → graph.eligible vertex = true) →
        ∀ vertex, kept vertex → alive finish vertex := by
  obtain ⟨n, finish, run, stopped, _, safe, subset, greatest⟩ := solves graph vertices unique covered
  refine ⟨n, finish, run, stopped, (model.safeSet_iff graph indexed won _ subset).mp safe, subset, ?_⟩
  intro kept safe subset
  exact greatest kept ((model.safeSet_iff graph indexed won kept subset).mpr safe) subset

/-- 生存集合は既存の保証領域に一括追加できる。内部循環を単一頂点ずつ確定するのではない。 -/
noncomputable def batch_at_halt (graph : Graph V E) (indexed : G.IndexedMoves E) (won : V → Prop)
    (model : GameModel graph indexed won) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    {finish : State V E} {n : Nat} (run : Run graph (initial graph vertices) n finish)
    (stopped : Stopped finish) (fresh : ∀ vertex, graph.eligible vertex = true → ¬ won vertex) :
    G.SafeBatch won (alive finish) := by
  have result := greatest_at_halt graph vertices covered run stopped.1 stopped.2
  exact G.batchOfSafeSet ((model.safeSet_iff graph indexed won _ result.2.1).mp result.1)
    (fun vertex live => fresh vertex (result.2.1 vertex live))

end PetaProof.SafetyExecution
