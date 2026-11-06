import PetaProof.IndexedPropagation
import PetaProof.NotificationBatches

/-!
全局面のhitカウンター、FIFO、通知済み辺の履歴をまとめた影の実行状態。
通知履歴は証明用であり、本番C++に辺集合や履歴配列を追加しない。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

structure PropagationState (V : Type u) (E : Type v) where
  counters : V → HitCounter E
  queue : AdmissionQueue V
  notified : E → Bool

namespace PropagationState

def initial (indexed : G.IndexedMoves E) : PropagationState V E := {
  counters := fun vertex => HitCounter.initial (indexed.outgoing vertex)
  queue := AdmissionQueue.initial
  notified := fun _ => false
}

/-- 未確定局面では、親ごとのseenが全体の通知履歴と一致する。 -/
structure Invariant (indexed : G.IndexedMoves E) (state : PropagationState V E) : Prop where
  counters : ∀ vertex, HitCounter.Invariant (decide (G.owner vertex = G.player))
    (indexed.outgoing vertex) (state.counters vertex)
  queue : state.queue.Invariant
  agrees : ∀ vertex, (state.counters vertex).admitted = state.queue.admitted vertex
  history : ∀ vertex, (state.counters vertex).admitted = false →
    ∀ edge ∈ indexed.outgoing vertex, (state.counters vertex).seen edge = state.notified edge

omit [DecidableEq V] [DecidableEq E] in
theorem initial_invariant (indexed : G.IndexedMoves E) : Invariant indexed (initial indexed) := by
  exact ⟨indexed.initial_counter_invariant, AdmissionQueue.initial_invariant,
    fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- hitは親1局面だけを更新する。確定した場合は既存のadmitガードでFIFOに積む。 -/
def notify (indexed : G.IndexedMoves E) (state : PropagationState V E) (edge : E) :
    PropagationState V E :=
  let parent := indexed.source edge
  let next := HitCounter.hit (decide (G.owner parent = G.player)) (state.counters parent) edge
  { counters := fun vertex => if vertex = parent then next else state.counters vertex
    queue := if next.admitted then state.queue.admit parent else state.queue
    notified := markSeen state.notified edge }

/-- 局所安全集合からの追加。値の安全性はSafeBatchで別途検査する。 -/
def add (state : PropagationState V E) (vertex : V) : PropagationState V E := {
  counters := fun other => if other = vertex then
    { state.counters other with admitted := true } else state.counters other
  queue := state.queue.admit vertex
  notified := state.notified
}

def pop (state : PropagationState V E) : PropagationState V E :=
  { state with queue := state.queue.pop }

omit [DecidableEq E] in
theorem add_preserves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (vertex : V) : Invariant indexed (state.add vertex) := by
  constructor
  · intro other
    by_cases same : other = vertex
    · subst other
      simp only [add, if_pos rfl]
      constructor <;> simp
    · simpa only [add, if_neg same] using inv.counters other
  · exact AdmissionQueue.admit_preserves _ inv.queue _
  · intro other
    by_cases same : other = vertex
    · subst other
      cases flag : state.queue.admitted vertex <;>
        simp [add, AdmissionQueue.admit, flag, markSeen]
    · cases flag : state.queue.admitted vertex <;>
        simp [add, AdmissionQueue.admit, flag, markSeen, same, inv.agrees]
  · intro other pending edge member
    by_cases same : other = vertex
    · subst other
      simp [add] at pending
    · simpa only [add, if_neg same] using
        inv.history other (by simpa only [add, if_neg same] using pending) edge member

omit [DecidableEq V] [DecidableEq E] in
theorem pop_preserves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) : Invariant indexed state.pop := by
  exact ⟨inv.counters, AdmissionQueue.pop_preserves _ inv.queue,
    fun vertex => by simpa only [pop, AdmissionQueue.pop_admitted] using inv.agrees vertex,
    inv.history⟩

omit [DecidableEq V] [DecidableEq E] in
/-- 全体履歴で未通知なら、未確定の親のカウンターでも新規通知である。 -/
theorem fresh_at_parent (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (edge : E) (fresh : state.notified edge = false)
    (pending : (state.counters (indexed.source edge)).admitted = false) :
    (state.counters (indexed.source edge)).seen edge = false := by
  rw [inv.history _ pending edge (indexed.at_source edge), fresh]

theorem notify_preserves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (edge : E) (fresh : state.notified edge = false) :
    Invariant indexed (state.notify indexed edge) := by
  let parent := indexed.source edge
  let next := HitCounter.hit (decide (G.owner parent = G.player)) (state.counters parent) edge
  have next_inv : HitCounter.Invariant (decide (G.owner parent = G.player))
      (indexed.outgoing parent) next := by
    cases flag : (state.counters parent).admitted with
    | true => simpa [next, HitCounter.hit, flag] using inv.counters parent
    | false =>
      exact HitCounter.hit_preserves _ _ edge _ (inv.counters parent)
        (indexed.unique parent) (indexed.at_source edge) (fresh_at_parent indexed state inv edge fresh flag)
  have stayed : next.admitted = false → (state.counters parent).admitted = false := by
    cases flag : (state.counters parent).admitted <;> simp [next, HitCounter.hit, flag]
  constructor
  · intro vertex
    change HitCounter.Invariant (decide (G.owner vertex = G.player)) (indexed.outgoing vertex)
      (if vertex = parent then next else state.counters vertex)
    by_cases same : vertex = parent
    · subst vertex
      simpa only [if_pos rfl] using next_inv
    · simpa only [if_neg same] using inv.counters vertex
  · change (if next.admitted then state.queue.admit parent else state.queue).Invariant
    cases next.admitted
    · exact inv.queue
    · exact AdmissionQueue.admit_preserves _ inv.queue _
  · intro vertex
    change (if vertex = parent then next else state.counters vertex).admitted =
      (if next.admitted then state.queue.admit parent else state.queue).admitted vertex
    cases flag : next.admitted with
    | false =>
      have old := inv.agrees parent
      rw [stayed flag] at old
      by_cases same : vertex = parent
      · simp [same, flag, ← old]
      · simp [same, flag, inv.agrees]
    | true =>
      by_cases same : vertex = parent
      · subst vertex
        cases old : state.queue.admitted parent <;>
          simp [flag, AdmissionQueue.admit, old, markSeen]
      · cases old : state.queue.admitted parent <;>
          simp [same, flag, AdmissionQueue.admit, old, markSeen, inv.agrees]
  · intro vertex pending other member
    change (if vertex = parent then next else state.counters vertex).admitted = false at pending
    change (if vertex = parent then next else state.counters vertex).seen other =
      markSeen state.notified edge other
    by_cases same : vertex = parent
    · subst vertex
      simp only [if_pos rfl] at pending ⊢
      have old := stayed pending
      change (HitCounter.hit _ _ _).seen other = _
      simp only [HitCounter.hit, old, Bool.false_eq_true, ite_false]
      by_cases equal : other = edge
      · simp [markSeen, equal]
      · simp only [markSeen, if_neg equal]
        exact inv.history parent old other member
    · have old : (state.counters vertex).admitted = false := by simpa [same] using pending
      have different : other ≠ edge := by
        intro equal
        have source := indexed.source_of_mem vertex other member
        subst other
        exact same source.symm
      simp only [if_neg same, markSeen, if_neg different]
      exact inv.history vertex old other member

/-- 実行列の辺通知には新規性を要求する。局所追加とpopは任意に交錯してよい。 -/
inductive Run (indexed : G.IndexedMoves E) : PropagationState V E → Prop
  | initial : Run indexed (initial indexed)
  | notify {state} : Run indexed state → (edge : E) → state.notified edge = false →
      Run indexed (state.notify indexed edge)
  | add {state} : Run indexed state → (vertex : V) → Run indexed (state.add vertex)
  | pop {state} : Run indexed state → Run indexed state.pop

theorem Run.invariant (indexed : G.IndexedMoves E) {state : PropagationState V E}
    (run : Run indexed state) : Invariant indexed state := by
  induction run with
  | initial => exact initial_invariant indexed
  | notify _ edge fresh ih => exact notify_preserves indexed _ ih edge fresh
  | add _ vertex ih => exact add_preserves indexed _ ih vertex
  | pop _ ih => exact pop_preserves indexed _ ih

def notifyMany (indexed : G.IndexedMoves E) (state : PropagationState V E) :
    List E → PropagationState V E
  | [] => state
  | edge :: rest => notifyMany indexed (state.notify indexed edge) rest

/-- バッチ全体の一意性と過去履歴との非重複から、各hitの新規性を導く。 -/
theorem notifyMany_preserves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (edges : List E) (unique : edges.Nodup)
    (fresh : ∀ edge ∈ edges, state.notified edge = false) :
    Invariant indexed (state.notifyMany indexed edges) := by
  induction edges generalizing state with
  | nil => exact inv
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    apply ih (state.notify indexed edge) (notify_preserves indexed state inv edge (fresh edge (by simp))) parts.2
    intro other member
    have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
    change markSeen state.notified edge other = false
    simp only [markSeen, if_neg different]
    exact fresh other (by simp [member])

theorem notifyMany_history (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (edges : List E) (other : E) :
    (state.notifyMany indexed edges).notified other = true ↔
      state.notified other = true ∨ other ∈ edges := by
  induction edges generalizing state with
  | nil => simp [notifyMany]
  | cons edge rest ih =>
    rw [notifyMany, ih]
    change markSeen state.notified edge other = true ∨ other ∈ rest ↔ _
    rw [markSeen_true_iff, List.mem_cons]
    simp only [or_assoc, or_left_comm]

omit [DecidableEq V] [DecidableEq E] in
def won (state : PropagationState V E) (vertex : V) : Prop :=
  (state.counters vertex).admitted = true

/-- 全体の履歴を使って、実際にhitで追加する親のSafeBatchを構成する。
局所追加自体の安全性を、カウンター不変条件だけから仮定なく導くものではない。 -/
def new_parent_batch (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (edge : E) (fresh : state.notified edge = false)
    (pending : ¬ state.won (indexed.source edge))
    (sound : ∀ other ∈ indexed.outgoing (indexed.source edge), state.notified other = true →
      G.GoodExit state.won (indexed.move other))
    (good : G.GoodExit state.won (indexed.move edge))
    (ready : (state.notify indexed edge).won (indexed.source edge)) :
    G.SafeBatch state.won (fun vertex => vertex = indexed.source edge) := by
  have flag : (state.counters (indexed.source edge)).admitted = false := by
    cases h : (state.counters (indexed.source edge)).admitted
    · rfl
    · exact False.elim (pending h)
  apply indexed.hit_batch state.won (indexed.source edge) (state.counters (indexed.source edge)) edge
    (inv.counters _) (indexed.at_source edge) (fresh_at_parent indexed state inv edge fresh flag) flag pending
  · intro other member seen
    exact sound other member ((inv.history _ flag other member) ▸ seen)
  · exact good
  · simpa only [won, notify, if_pos rfl] using ready

omit [DecidableEq V] [DecidableEq E] in
/-- FIFOが空、良いleafと取り出した子の全逆辺が通知済みなら通常伝播は閉じる。 -/
theorem ordinary_closed (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (empty : state.queue.pending = [])
    (leaves : ∀ edge score, indexed.move edge = .leaf score →
      G.threshold ≤ score → state.notified edge = true)
    (nodes : ∀ child ∈ state.queue.popped, ∀ edge,
      indexed.move edge = .node child → state.notified edge = true) : G.OrdinaryClosed state.won := by
  apply indexed.ordinary_closed_when_drained state.won state.counters state.queue
    (fun _ => Iff.rfl) (fun vertex => by rw [won, inv.agrees]) inv.counters inv.queue empty
  · intro vertex outside edge member score equal good
    have pending : (state.counters vertex).admitted = false := by
      cases flag : (state.counters vertex).admitted
      · rfl
      · exact False.elim (outside flag)
    rw [inv.history vertex pending edge member]
    exact leaves edge score equal good
  · intro child popped vertex outside edge member equal
    have pending : (state.counters vertex).admitted = false := by
      cases flag : (state.counters vertex).admitted
      · rfl
      · exact False.elim (outside flag)
    rw [inv.history vertex pending edge member]
    exact nodes child popped edge equal

end PropagationState
end PetaProof.ThresholdGame
