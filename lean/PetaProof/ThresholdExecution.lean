import PetaProof.CertifiedPhase

/-!
全閾値でカウンター・FIFO・通知履歴・初回値配列を引き継ぐ、一つの有限な実行列。
各閾値の停止点は独立に仮定せず、同じ認証済み操作列の結果から構成する。
-/
namespace PetaProof.ThresholdGame

universe u v w
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

namespace IndexedMoves

def retune (indexed : G.IndexedMoves E) (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate) :
    (G.retune level positive bounded).IndexedMoves E where
  outgoing := indexed.outgoing
  source := indexed.source
  move := indexed.move
  unique := indexed.unique
  at_source := indexed.at_source
  source_of_mem := indexed.source_of_mem
  legal := indexed.legal
  covers := indexed.covers

end IndexedMoves

/-- snapshotsは各停止点の名前。stepの出力状態が次のstepの入力状態そのものである。 -/
inductive ThresholdExecution (indexed : G.IndexedMoves E) (snapshots : Int → PropagationState V E) :
    (ceiling : Int) → (positive : 0 < ceiling) → (bounded : ceiling ≤ G.mate) →
      PropagationState V E → (V → Int) → List Int → PropagationState V E → (V → Int) → Prop
  | done {ceiling positive bounded state values} :
      ThresholdExecution indexed snapshots ceiling positive bounded state values [] state values
  | step {ceiling positive bounded initial initialValues level rest nextValues final finalValues}
      (level_positive : 0 < level) (lower : level ≤ ceiling)
      (phase : CertifiedPhase (indexed.retune level level_positive (Int.le_trans lower bounded))
        initial initialValues (snapshots level) nextValues)
      (halt : Nonempty (HaltConditions (indexed.retune level level_positive (Int.le_trans lower bounded)) (snapshots level)))
      (tail : ThresholdExecution indexed snapshots level level_positive (Int.le_trans lower bounded)
        (snapshots level) nextValues rest final finalValues) :
      ThresholdExecution indexed snapshots ceiling positive bounded initial initialValues (level :: rest) final finalValues

/-- 初期の証明を低い閾値へ移し、同じ操作列から停止証拠と最終記録配列を同時に構成する。 -/
theorem ThresholdExecution.spec (indexed : G.IndexedMoves E) (snapshots : Int → PropagationState V E)
    {ceiling : Int} {positive : 0 < ceiling} {bounded : ceiling ≤ G.mate}
    {initial final : PropagationState V E} {initialValues finalValues : V → Int} {levels : List Int}
    (run : ThresholdExecution indexed snapshots ceiling positive bounded initial initialValues levels final finalValues)
    (certificate : StateCertificate (indexed.retune ceiling positive bounded) initial)
    (initial_rep : ∀ vertex, initial.won vertex ↔ initialValues vertex ≠ 0) :
    (∀ vertex, final.won vertex ↔ finalValues vertex ≠ 0) ∧
      finalValues = scanValues levels (fun level vertex => ((snapshots level).counters vertex).admitted) initialValues ∧
      ∀ level ∈ levels, ∃ (pos : 0 < level) (bound : level ≤ G.mate)
        (stopped : G.StoppedThreshold level pos bound), ∀ vertex, stopped.won vertex ↔ (snapshots level).won vertex := by
  induction run with
  | done =>
    exact ⟨initial_rep, rfl, by intro _ impossible; cases impossible⟩
  | @step ceiling positive bounded initial initialValues level rest nextValues final finalValues pos lower phase halt tail ih =>
    have lowered : StateCertificate (indexed.retune level pos (Int.le_trans lower bounded)) initial :=
      StateCertificate.lowerThreshold (indexed.retune ceiling positive bounded) initial certificate level pos lower
    obtain ⟨next_certificate⟩ := phase.certified _ lowered
    have phase_spec := RecordedPhase.invariants _ level pos initial initialValues initial_rep
      (CertifiedPhase.recorded _ phase)
    obtain ⟨final_rep, final_scan, later_stops⟩ := ih next_certificate phase_spec.1
    refine ⟨final_rep, ?_, ?_⟩
    · rw [final_scan, phase_spec.2]
      rfl
    · intro current member
      rcases List.mem_cons.mp member with same | remaining
      · subst current
        obtain ⟨conditions⟩ := halt
        refine ⟨pos, Int.le_trans lower bounded,
          StoppedThreshold.ofState level pos (Int.le_trans lower bounded) _ _ next_certificate
            conditions.queue_empty conditions.leaves_done conditions.nodes_done conditions.core
            conditions.covers_core conditions.rounds conditions.local_empty, ?_⟩
        intro vertex
        rfl
      · exact later_stops current remaining

/-- 0初期化からの一つの降順実行が全critical閾値で停止するなら、その最終配列は最大正値である。 -/
theorem ThresholdExecution.positive_maximum (indexed : G.IndexedMoves E)
    (snapshots : Int → PropagationState V E) (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    {levels : List Int} {final : PropagationState V E} {values : V → Int}
    (run : ThresholdExecution indexed snapshots G.mate G.mate_positive (Int.le_refl _)
      (PropagationState.initial indexed) (fun _ => 0) levels final values)
    (valid : ∀ level ∈ levels, G.CriticalLevel level)
    (levels_cover : ∀ level, G.CriticalLevel level → level ∈ levels)
    (descending : levels.Pairwise (fun a b => b < a)) (root : V) : G.PositiveMaximum root (values root) := by
  have seed : StateCertificate (indexed.retune G.mate G.mate_positive (Int.le_refl _)) (PropagationState.initial indexed) :=
    StateCertificate.initial _
  have initial_rep : ∀ vertex, (PropagationState.initial indexed).won vertex ↔ (0 : Int) ≠ 0 := by
    intro vertex
    simp [PropagationState.won, PropagationState.initial, HitCounter.initial]
  obtain ⟨_, output, stops⟩ := run.spec indexed snapshots seed initial_rep
  rw [output, scanValues_initial levels _ (fun level member => (valid level member).1)]
  apply G.firstWinning_complete leaves vertices covered levels valid levels_cover descending
  intro level member
  obtain ⟨pos, bound, stopped, represented⟩ := stops level member
  exact (represented root).symm.trans (stopped.correct vertices covered root)

/-- 空バケットを飛ばすC++型の閾値列にも、同じ単一実行の定理を適用できる。 -/
theorem ThresholdExecution.processed_maximum (indexed : G.IndexedMoves E)
    (snapshots : Int → PropagationState V E) (leaves : G.BoundedLeaves)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (hasLeaf : Int → Bool)
    (buckets : ∀ level, 0 < level → level ≤ G.mate →
      (hasLeaf level = true ↔ ∃ vertex, G.legal vertex (.leaf level)))
    {final : PropagationState V E} {values : V → Int}
    (run : ThresholdExecution indexed snapshots G.mate G.mate_positive (Int.le_refl _)
      (PropagationState.initial indexed) (fun _ => 0) (processedLevels G.mate.toNat hasLeaf) final values)
    (root : V) : G.PositiveMaximum root (values root) := by
  apply run.positive_maximum indexed snapshots leaves vertices covered
    (fun level member => (G.processedLevels_critical_iff hasLeaf buckets level).mp member)
    (fun level critical => (G.processedLevels_critical_iff hasLeaf buckets level).mpr critical)
    (processedLevels_ordered _ _) root

/-- 双方の正値解法をそれぞれ単一実行として認証すれば、最終配列の差が符号付きの最適値になる。 -/
theorem exact_from_processed_executions {F : Type w} [DecidableEq F]
    (own : G.IndexedMoves E) (other : G.opposite.IndexedMoves F)
    (ownSnapshots : Int → PropagationState V E) (otherSnapshots : Int → PropagationState V F)
    (leaves : G.BoundedLeaves) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (ownLeaf otherLeaf : Int → Bool)
    (ownBuckets : ∀ level, 0 < level → level ≤ G.mate →
      (ownLeaf level = true ↔ ∃ vertex, G.legal vertex (.leaf level)))
    (otherBuckets : ∀ level, 0 < level → level ≤ G.opposite.mate →
      (otherLeaf level = true ↔ ∃ vertex, G.opposite.legal vertex (.leaf level)))
    {ownFinal : PropagationState V E} {otherFinal : PropagationState V F} {ownValues otherValues : V → Int}
    (ownRun : ThresholdExecution own ownSnapshots G.mate G.mate_positive (Int.le_refl _)
      (PropagationState.initial own) (fun _ => 0) (processedLevels G.mate.toNat ownLeaf) ownFinal ownValues)
    (otherRun : ThresholdExecution other otherSnapshots G.opposite.mate G.opposite.mate_positive (Int.le_refl _)
      (PropagationState.initial other) (fun _ => 0) (processedLevels G.opposite.mate.toNat otherLeaf) otherFinal otherValues)
    (root : V) : G.ExactValue root (ownValues root - otherValues root) := by
  exact G.merge_positive_maxima leaves vertices covered root
    (ownRun.processed_maximum own ownSnapshots leaves vertices covered ownLeaf ownBuckets root)
    (otherRun.processed_maximum other otherSnapshots (G.opposite_bounded_leaves leaves)
      vertices covered otherLeaf otherBuckets root)

end PetaProof.ThresholdGame
