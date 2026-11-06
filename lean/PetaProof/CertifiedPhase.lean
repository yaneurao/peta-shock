import PetaProof.RecordedPhase

/-! 同じ通知・局所追加・popの列へ、値配列の記録と意味論的な安全性を同時に付ける。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

inductive CertifiedPhase (indexed : G.IndexedMoves E)
    (initial : PropagationState V E) (initialValues : V → Int) : PropagationState V E → (V → Int) → Prop
  | initial : CertifiedPhase indexed initial initialValues initial initialValues
  | notify {state values} : CertifiedPhase indexed initial initialValues state values → (edge : E) →
      state.notified edge = false → G.GoodExit state.won (indexed.move edge) →
      CertifiedPhase indexed initial initialValues (state.notify indexed edge)
        (if ((state.notify indexed edge).counters (indexed.source edge)).admitted then
          writeAdmission values G.threshold (indexed.source edge) else values)
  | batch {state values} : CertifiedPhase indexed initial initialValues state values → (vertices : List V) →
      Nonempty (G.SafeBatch state.won (fun vertex => vertex ∈ vertices)) →
      CertifiedPhase indexed initial initialValues (state.addMany vertices) (writeAdmissions values G.threshold vertices)
  | pop {state values} : CertifiedPhase indexed initial initialValues state values →
      CertifiedPhase indexed initial initialValues state.pop values

theorem CertifiedPhase.recorded (indexed : G.IndexedMoves E) {initial state : PropagationState V E}
    {initialValues values : V → Int} (run : CertifiedPhase indexed initial initialValues state values) :
    RecordedPhase indexed G.threshold initial initialValues state values := by
  induction run with
  | initial => exact RecordedPhase.initial
  | notify _ edge _ _ ih => exact RecordedPhase.notify ih edge
  | batch _ vertices _ ih => exact RecordedPhase.batch ih vertices
  | pop _ ih => exact RecordedPhase.pop ih

/-- 閾値を切り替えた後の証拠を出発点とし、同じ操作列の終端にも値保証を構成する。 -/
theorem CertifiedPhase.certified (indexed : G.IndexedMoves E) {initial state : PropagationState V E}
    {initialValues values : V → Int} (run : CertifiedPhase indexed initial initialValues state values)
    (certificate : StateCertificate indexed initial) : Nonempty (StateCertificate indexed state) := by
  induction run with
  | initial => exact ⟨certificate⟩
  | notify _ edge fresh good ih =>
    obtain ⟨previous⟩ := ih
    exact ⟨StateCertificate.notify indexed _ previous edge fresh good⟩
  | batch _ vertices safe ih =>
    obtain ⟨previous⟩ := ih
    obtain ⟨batch⟩ := safe
    exact ⟨StateCertificate.addBatch indexed _ previous vertices batch⟩
  | pop _ ih =>
    obtain ⟨previous⟩ := ih
    exact ⟨StateCertificate.pop indexed _ previous⟩

/-- プログラムが次の閾値へ進むために必要な停止条件。到達性自体は仮定している。 -/
structure HaltConditions (indexed : G.IndexedMoves E) (state : PropagationState V E) where
  queue_empty : state.queue.pending = []
  leaves_done : ∀ edge score, indexed.move edge = .leaf score →
    G.threshold ≤ score → state.notified edge = true
  nodes_done : ∀ child ∈ state.queue.popped, ∀ edge,
    indexed.move edge = .node child → state.notified edge = true
  core : V → Prop
  covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → core vertex
  rounds : Nat
  local_empty : ∀ vertex, ¬ G.pruneIter state.won (fun child => core child ∧ ¬ state.won child) rounds vertex

end PetaProof.ThresholdGame
