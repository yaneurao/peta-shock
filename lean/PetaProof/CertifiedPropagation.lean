import PetaProof.PropagationTransitions

/-!
固定した正閾値で、機械的な実行状態に順位付き方策と通知の意味を結びつける。
局所集合のFIFO投入は逐次だが、循環を含む集合の安全性は集合全体のSafeBatchで要求する。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

structure StateCertificate (indexed : G.IndexedMoves E) (state : PropagationState V E) where
  invariant : state.Invariant indexed
  region : G.RankedRegion state.won
  notifications : ∀ edge, state.notified edge = true → G.GoodExit state.won (indexed.move edge)

namespace StateCertificate

omit [DecidableEq V] [DecidableEq E] in
def initial (indexed : G.IndexedMoves E) : StateCertificate indexed (PropagationState.initial indexed) where
  invariant := PropagationState.initial_invariant indexed
  region := RankedRegion.empty.reindex (by intro vertex; simp [PropagationState.won, PropagationState.initial, HitCounter.initial])
  notifications := by intro edge impossible; cases impossible

/-- 新規確定なしなら既存方策を維持し、新規確定なら通常伝播のSafeBatchで拡張する。 -/
noncomputable def notify (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edge : E) (fresh : state.notified edge = false)
    (good : G.GoodExit state.won (indexed.move edge)) : StateCertificate indexed (state.notify indexed edge) := by
  classical
  let next := state.notify indexed edge
  have monotone := PropagationState.won_notify_mono indexed state edge
  have region : G.RankedRegion next.won := by
    by_cases added : next.won (indexed.source edge) ∧ ¬ state.won (indexed.source edge)
    · let batch := PropagationState.new_parent_batch indexed state certificate.invariant edge fresh added.2
        (fun other _ seen => certificate.notifications other seen) good added.1
      apply (certificate.region.extend batch).reindex
      intro vertex
      rw [PropagationState.won_notify_iff]
      constructor
      · rintro (old | equal)
        · exact Or.inl old
        · exact Or.inr ⟨equal, added.1⟩
      · rintro (old | ⟨equal, _⟩)
        · exact Or.inl old
        · exact Or.inr equal
    · apply certificate.region.reindex
      intro vertex
      constructor
      · exact monotone vertex
      · intro inside
        rcases (PropagationState.won_notify_iff indexed state edge vertex).mp inside with old | ⟨equal, ready⟩
        · exact old
        · have previous : state.won (indexed.source edge) := by
            apply Classical.byContradiction
            intro outside
            exact added ⟨ready, outside⟩
          simpa only [equal] using previous
  refine ⟨PropagationState.notify_preserves indexed state certificate.invariant edge fresh, region, ?_⟩
  intro other seen
  rcases (markSeen_true_iff state.notified edge other).mp seen with equal | previous
  · subst other
    exact goodExit_mono monotone _ good
  · exact goodExit_mono monotone _ (certificate.notifications other previous)

omit [DecidableEq V] [DecidableEq E] in
def pop (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) : StateCertificate indexed state.pop where
  invariant := PropagationState.pop_preserves indexed state certificate.invariant
  region := certificate.region
  notifications := certificate.notifications

omit [DecidableEq V] [DecidableEq E] in
/-- 子を取り出した事実から、その逆辺通知が良い出口を表すことを導く。 -/
theorem node_good (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (child : V) (popped : child ∈ state.queue.popped)
    (edge : E) (same : indexed.move edge = .node child) : G.GoodExit state.won (indexed.move edge) := by
  rw [same]
  change (state.counters child).admitted = true
  rw [certificate.invariant.agrees]
  apply (certificate.invariant.queue.covers child).mpr
  simp [AdmissionQueue.total, popped]

omit [DecidableEq E] in
/-- SafeBatchは新集合全体の証拠。循環集合の各頂点を独立の安全な追加とは扱わない。 -/
noncomputable def addBatch (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (vertices : List V)
    (batch : G.SafeBatch state.won (fun vertex => vertex ∈ vertices)) :
    StateCertificate indexed (state.addMany vertices) where
  invariant := PropagationState.addMany_preserves indexed state certificate.invariant vertices
  region := (certificate.region.extend batch).reindex (fun vertex =>
    (PropagationState.won_addMany_iff state vertices vertex).symm)
  notifications := by
    intro edge seen
    rw [PropagationState.addMany_notified] at seen
    apply goodExit_mono (fun vertex inside => (PropagationState.won_addMany_iff state vertices vertex).mpr (Or.inl inside))
    exact certificate.notifications edge seen

/-- 有効な通知と安全な局所集合だけを処理する実行列。証明用の履歴であり本番の履歴配列ではない。 -/
inductive SoundRun (indexed : G.IndexedMoves E) : PropagationState V E → Prop
  | initial : SoundRun indexed (PropagationState.initial indexed)
  | notify {state} : SoundRun indexed state → (edge : E) → state.notified edge = false →
      G.GoodExit state.won (indexed.move edge) → SoundRun indexed (state.notify indexed edge)
  | batch {state} : SoundRun indexed state → (vertices : List V) →
      Nonempty (G.SafeBatch state.won (fun vertex => vertex ∈ vertices)) → SoundRun indexed (state.addMany vertices)
  | pop {state} : SoundRun indexed state → SoundRun indexed state.pop

theorem SoundRun.certified (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) : Nonempty (StateCertificate indexed state) := by
  induction run with
  | initial => exact ⟨StateCertificate.initial indexed⟩
  | notify _ edge fresh good ih =>
    obtain ⟨certificate⟩ := ih
    exact ⟨StateCertificate.notify indexed _ certificate edge fresh good⟩
  | batch _ vertices safe ih =>
    obtain ⟨certificate⟩ := ih
    obtain ⟨batch⟩ := safe
    exact ⟨addBatch indexed _ certificate vertices batch⟩
  | pop _ ih =>
    obtain ⟨certificate⟩ := ih
    exact ⟨StateCertificate.pop indexed _ certificate⟩

/-- 確定局面は、任意の相手の全履歴依存戦略に対して閾値以上の利得を保証できる。 -/
theorem SoundRun.fourfold_winning (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) (root : V) (inside : state.won root) : G.FourfoldWinning root := by
  obtain ⟨certificate⟩ := run.certified indexed
  exact certificate.region.fourfold_winning root inside

theorem SoundRun.leaf_notification (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) (edge : E) (score : Int) (same : indexed.move edge = .leaf score)
    (fresh : state.notified edge = false) (good : G.threshold ≤ score) :
    SoundRun indexed (state.notify indexed edge) := by
  apply SoundRun.notify run edge fresh
  simpa only [same, GoodExit] using good

theorem SoundRun.node_notification (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) (edge : E) (child : V) (same : indexed.move edge = .node child)
    (popped : child ∈ state.queue.popped) (fresh : state.notified edge = false) :
    SoundRun indexed (state.notify indexed edge) := by
  obtain ⟨certificate⟩ := run.certified indexed
  exact SoundRun.notify run edge fresh (node_good indexed state certificate child popped edge same)

theorem SoundRun.lower_guarantee (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) (root : V) (inside : state.won root) :
    G.LowerGuarantee root G.threshold := run.fourfold_winning indexed root inside

/-- 完全な通知と局所削除の空性が確認できた停止点では、確定集合は閾値勝利領域と一致する。 -/
theorem SoundRun.stopped_exact (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : SoundRun indexed state) (empty_queue : state.queue.pending = [])
    (leaves : ∀ edge score, indexed.move edge = .leaf score →
      G.threshold ≤ score → state.notified edge = true)
    (nodes : ∀ child ∈ state.queue.popped, ∀ edge,
      indexed.move edge = .node child → state.notified edge = true)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (core : V → Prop) (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → core vertex)
    (rounds : Nat) (local_empty : ∀ vertex,
      ¬ G.pruneIter state.won (fun child => core child ∧ ¬ state.won child) rounds vertex)
    (root : V) : state.won root ↔ G.FourfoldWinning root := by
  obtain ⟨certificate⟩ := run.certified indexed
  exact G.stopped_exact_for_fourfold certificate.region
    (PropagationState.ordinary_closed indexed state certificate.invariant empty_queue leaves nodes)
    vertices covered core covers_core rounds local_empty root

end StateCertificate
end PetaProof.ThresholdGame
