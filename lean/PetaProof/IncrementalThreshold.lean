import PetaProof.CertifiedPropagation

/-!
正閾値を下げても、確定領域・カウンター・FIFOを初期化し直す必要はない。
新しく良くなったleafの通知は安全性とは別に完了させる必要がある。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

theorem goodExit_lower {won : V → Prop} (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold)
    (move : Move V) (good : G.GoodExit won move) :
    (G.lowerThreshold t positive lower).GoodExit won move := by
  cases move with
  | node _ => exact good
  | leaf _ => exact Int.le_trans lower good

namespace SafeBatch

/-- 既存の安全な局所集合も、低い正閾値では同じ手で安全である。 -/
def weaken {won current : V → Prop} (batch : G.SafeBatch won current)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (G.lowerThreshold t positive lower).SafeBatch won current where
  fresh := batch.fresh
  choice := batch.choice
  chosen_legal := batch.chosen_legal
  safe := by
    intro vertex inside move follows
    have good := batch.safe vertex inside move follows
    cases move with
    | node _ => exact good
    | leaf _ => exact Int.le_trans lower good

end SafeBatch

namespace IndexedMoves

/-- 閾値は辺の列挙・親ID・指し手を変えない。 -/
def lowerThreshold (indexed : G.IndexedMoves E) (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    (G.lowerThreshold t positive lower).IndexedMoves E where
  outgoing := indexed.outgoing
  source := indexed.source
  move := indexed.move
  unique := indexed.unique
  at_source := indexed.at_source
  source_of_mem := indexed.source_of_mem
  legal := indexed.legal
  covers := indexed.covers

end IndexedMoves

namespace StateCertificate

/-- 同一の実行状態を引き継ぎ、方策の保証閾値だけを弱める。 -/
def lowerThreshold (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    StateCertificate (indexed.lowerThreshold t positive lower) state where
  invariant := {
    counters := certificate.invariant.counters
    queue := certificate.invariant.queue
    agrees := certificate.invariant.agrees
    history := certificate.invariant.history
  }
  region := certificate.region.weaken t positive lower
  notifications := fun edge seen => goodExit_lower t positive lower _ (certificate.notifications edge seen)

/-- 過去の操作列自体も低い閾値で有効である。カウンター・FIFO・履歴は同一である。 -/
theorem SoundRun.lowerThreshold [DecidableEq V] [DecidableEq E] (indexed : G.IndexedMoves E)
    {state : PropagationState V E} (run : SoundRun indexed state)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) :
    SoundRun (indexed.lowerThreshold t positive lower) state := by
  induction run with
  | initial => exact SoundRun.initial
  | notify _ edge fresh good ih =>
    exact SoundRun.notify ih edge fresh (goodExit_lower t positive lower _ good)
  | batch _ vertices safe ih =>
    obtain ⟨batch⟩ := safe
    exact SoundRun.batch ih vertices ⟨batch.weaken t positive lower⟩
  | pop _ ih => exact SoundRun.pop ih

/-- 旧閾値未満のleafは、旧実行の安全な通知履歴には現れない。 -/
theorem lower_leaf_fresh (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edge : E) (score : Int)
    (same : indexed.move edge = .leaf score) (below : score < G.threshold) : state.notified edge = false := by
  cases flag : state.notified edge with
  | false => rfl
  | true =>
    have good := certificate.notifications edge flag
    rw [same] at good
    change G.threshold ≤ score at good
    omega

variable [DecidableEq V] [DecidableEq E]

/-- 元の集合で良い出口である通知列を順に処理し、各更新後も値保証を維持する。 -/
noncomputable def notifyMany (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (edges : List E) (unique : edges.Nodup)
    (fresh : ∀ edge ∈ edges, state.notified edge = false)
    (good : ∀ edge ∈ edges, G.GoodExit state.won (indexed.move edge)) :
    StateCertificate indexed (state.notifyMany indexed edges) := by
  induction edges generalizing state with
  | nil => exact certificate
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    apply ih (state.notify indexed edge)
      (StateCertificate.notify indexed state certificate edge (fresh edge (by simp)) (good edge (by simp))) parts.2
    · intro other member
      have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
      change markSeen state.notified edge other = false
      simp only [markSeen, if_neg different]
      exact fresh other (by simp [member])
    · intro other member
      exact goodExit_mono (PropagationState.won_notify_mono indexed state edge) _ (good other (by simp [member]))

/-- [t,旧閾値)のleaf辺列を通知する増分処理。新規性は旧証拠から導き、再初期化しない。 -/
noncomputable def advanceLeaves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold)
    (edges : List E) (unique : edges.Nodup)
    (band : ∀ edge ∈ edges, ∃ score, indexed.move edge = .leaf score ∧ t ≤ score ∧ score < G.threshold) :
    StateCertificate (indexed.lowerThreshold t positive lower)
      (state.notifyMany (indexed.lowerThreshold t positive lower) edges) := by
  apply StateCertificate.notifyMany (indexed.lowerThreshold t positive lower) state
    (certificate.lowerThreshold indexed state t positive lower) edges unique
  · intro edge member
    obtain ⟨score, same, _, below⟩ := band edge member
    exact lower_leaf_fresh indexed state certificate edge score same below
  · intro edge member
    obtain ⟨score, same, good, _⟩ := band edge member
    change (G.lowerThreshold t positive lower).GoodExit state.won (indexed.move edge)
    rw [same]
    exact good

/-- 旧leafの通知完了と、新しい帯の全辺列挙から、低い閾値のleaf通知完了を導く。 -/
theorem advanceLeaves_complete (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) (edges : List E)
    (old_complete : ∀ edge score, indexed.move edge = .leaf score →
      G.threshold ≤ score → state.notified edge = true)
    (band_complete : ∀ edge score, indexed.move edge = .leaf score →
      t ≤ score → score < G.threshold → edge ∈ edges) :
    ∀ edge score, indexed.move edge = .leaf score → t ≤ score →
      (state.notifyMany (indexed.lowerThreshold t positive lower) edges).notified edge = true := by
  intro edge score same good
  apply (PropagationState.notifyMany_history (indexed.lowerThreshold t positive lower) state edges edge).mpr
  by_cases previous : G.threshold ≤ score
  · exact Or.inl (old_complete edge score same previous)
  · exact Or.inr (band_complete edge score same good (by omega))

end StateCertificate

namespace PropagationState

/-- leafバッチの通知自体は、既存の取り出し履歴を変えない。新規確定は待機列へ積む。 -/
theorem notify_popped [DecidableEq V] [DecidableEq E]
    (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge : E) :
    (state.notify indexed edge).queue.popped = state.queue.popped := by
  classical
  simp only [notify]
  split
  · simp only [AdmissionQueue.admit]
    split <;> rfl
  · rfl

theorem notifyMany_popped [DecidableEq V] [DecidableEq E] (indexed : G.IndexedMoves E)
    (state : PropagationState V E) (edges : List E) :
    (state.notifyMany indexed edges).queue.popped = state.queue.popped := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih => rw [notifyMany, ih, notify_popped]

end PropagationState

namespace StateCertificate

variable [DecidableEq V] [DecidableEq E]

/-- 低い閾値でleafを追加通知しても、既に取り出した子の通知完了は失われない。 -/
theorem advanceLeaves_nodes_complete (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (t : Int) (positive : 0 < t) (lower : t ≤ G.threshold) (edges : List E)
    (old_complete : ∀ child ∈ state.queue.popped, ∀ edge,
      indexed.move edge = .node child → state.notified edge = true) :
    ∀ child ∈ (state.notifyMany (indexed.lowerThreshold t positive lower) edges).queue.popped,
      ∀ edge, indexed.move edge = .node child →
        (state.notifyMany (indexed.lowerThreshold t positive lower) edges).notified edge = true := by
  intro child popped edge same
  rw [PropagationState.notifyMany_popped] at popped
  apply (PropagationState.notifyMany_history (indexed.lowerThreshold t positive lower) state edges edge).mpr
  exact Or.inl (old_complete child popped edge same)

end StateCertificate

namespace StoppedThreshold

/-- 証明付きの具体的な影の状態から、降順走査の定理が要求する停止証拠を作る。 -/
def ofState [DecidableEq V] [DecidableEq E] (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate)
    (indexed : (G.retune level positive bounded).IndexedMoves E) (state : PropagationState V E)
    (certificate : StateCertificate indexed state) (empty_queue : state.queue.pending = [])
    (leaves : ∀ edge score, indexed.move edge = .leaf score →
      level ≤ score → state.notified edge = true)
    (nodes : ∀ child ∈ state.queue.popped, ∀ edge,
      indexed.move edge = .node child → state.notified edge = true)
    (core : V → Prop) (covers_core : ∀ vertex,
      CyclicVertex (G.retune level positive bounded).OpponentChecking vertex → core vertex)
    (rounds : Nat) (local_empty : ∀ vertex,
      ¬ (G.retune level positive bounded).pruneIter state.won (fun child => core child ∧ ¬ state.won child) rounds vertex) :
    G.StoppedThreshold level positive bounded where
  won := state.won
  sound := certificate.region
  ordinary := PropagationState.ordinary_closed indexed state certificate.invariant empty_queue leaves nodes
  core := core
  covers_core := covers_core
  rounds := rounds
  empty := local_empty

end StoppedThreshold
end PetaProof.ThresholdGame
