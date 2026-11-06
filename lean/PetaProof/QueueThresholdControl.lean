import PetaProof.OrdinaryQueueClosure
import PetaProof.LocalQueueResult

/-!
固定閾値で同じ通常状態を保持し、通常FIFOの排出と局所削除キューを交互に実行する。
集合版settleとの一致を示す。閾値切替と値記録の全体統合は別の課題である。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]

/-- グラフの有限列挙と王手ラベル。停止証拠や勝敗の正解は含めない。 -/
structure QueueContext (G : ThresholdGame V) (E : Type v) where
  vertices : List V
  unique : vertices.Nodup
  covered : ∀ vertex, vertex ∈ vertices
  indexed : G.IndexedMoves E
  parents : ParentLists indexed
  core : V → Bool
  checked : V → V → Bool
  check_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

namespace QueueContext

variable (ctx : QueueContext G E)

def localInput (state : PropagationState V E) : SafetyClassification.Input G E where
  indexed := ctx.indexed
  won := fun vertex => (state.counters vertex).admitted
  core := ctx.core
  checked := ctx.checked
  check_correct := ctx.check_correct

def localState (state : PropagationState V E) : SafetyExecution.State V E :=
  SafetyClassification.queueResult (ctx.localInput state) ctx.vertices ctx.unique ctx.covered

/-- 生存局所集合を一度だけ列挙する。通常FIFOへ渡すのはこの頂点列である。 -/
def localMembers (state : PropagationState V E) : List V :=
  ctx.vertices.filter (fun vertex => !(ctx.localState state).deleted vertex)

theorem localMembers_iff (state : PropagationState V E) (vertex : V) :
    vertex ∈ ctx.localMembers state ↔ G.localResult ctx.vertices (fun vertex => ctx.core vertex = true) state.won vertex := by
  have same := SafetyClassification.queueResult_eq (ctx.localInput state) ctx.vertices ctx.unique ctx.covered
  have result := congrFun same vertex
  simpa only [localMembers, List.mem_filter, Bool.not_eq_true', ctx.covered vertex, true_and,
    SafetyExecution.alive, localState, localInput, PropagationState.won] using result.to_iff

def localBatch (state : PropagationState V E) : G.SafeBatch state.won (fun vertex => vertex ∈ ctx.localMembers state) := by
  let batch := SafetyClassification.queueResult_batch (ctx.localInput state) ctx.vertices ctx.unique ctx.covered
  have member : ∀ vertex, vertex ∈ ctx.localMembers state ↔ SafetyExecution.alive (ctx.localState state) vertex := by
    intro vertex
    simp only [localMembers, List.mem_filter, ctx.covered vertex, true_and, Bool.not_eq_true', SafetyExecution.alive]
  exact {
    fresh := fun vertex inside => batch.fresh vertex ((member vertex).mp inside)
    choice := batch.choice
    chosen_legal := fun vertex inside => batch.chosen_legal vertex ((member vertex).mp inside)
    safe := by
      intro vertex inside move follows
      have safe := batch.safe vertex ((member vertex).mp inside) move follows
      cases move with
      | leaf _ => exact safe
      | node child => exact safe.elim Or.inl (fun h => Or.inr ⟨(member child).mpr h.1, h.2⟩)
  }

def drain (state : PropagationState V E) : PropagationState V E :=
  PropagationState.drainQueue ctx.indexed ctx.parents ctx.vertices.length state

/-- 通常FIFOを開始してよい境界。終了時の空性や局所解の正しさは含めない。 -/
structure Boundary (state : PropagationState V E) : Prop where
  leaves : ∀ edge score, ctx.indexed.move edge = .leaf score → G.threshold ≤ score → state.notified edge = true
  nodes : PropagationState.NodesComplete ctx.indexed state

theorem drain_boundary (state : PropagationState V E) (boundary : ctx.Boundary state) : ctx.Boundary (ctx.drain state) := by
  exact ⟨fun edge score same good => PropagationState.drainQueue_history_mono ctx.indexed ctx.parents ctx.vertices.length
      state edge (boundary.leaves edge score same good),
    PropagationState.drainQueue_nodes_complete ctx.indexed ctx.parents ctx.vertices.length state boundary.nodes⟩

omit [DecidableEq E] in
theorem addMany_popped (state : PropagationState V E) (members : List V) :
    (state.addMany members).queue.popped = state.queue.popped := by
  induction members generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [PropagationState.addMany, ih]
    simp only [PropagationState.add, AdmissionQueue.admit]
    split <;> rfl

omit [DecidableEq E] in
theorem add_boundary (state : PropagationState V E) (boundary : ctx.Boundary state) (members : List V) :
    ctx.Boundary (state.addMany members) := by
  constructor
  · simpa only [PropagationState.addMany_notified] using boundary.leaves
  · intro child popped edge same
    rw [addMany_popped] at popped
    rw [PropagationState.addMany_notified]
    exact boundary.nodes child popped edge same

theorem local_add_won (state : PropagationState V E) :
    (state.addMany (ctx.localMembers state)).won =
      (fun vertex => state.won vertex ∨ G.localResult ctx.vertices (fun vertex => ctx.core vertex = true) state.won vertex) := by
  funext vertex
  apply propext
  rw [PropagationState.won_addMany_iff, ctx.localMembers_iff]

/-- fuelは非空の局所追加回数の証明用上界。毎回同じ通常状態を引き継ぐ。 -/
def settleQueue : Nat → PropagationState V E → PropagationState V E
  | 0, state => ctx.drain state
  | fuel + 1, state =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    if members = [] then closed else settleQueue fuel (closed.addMany members)

theorem settleQueue_certified (fuel : Nat) (state : PropagationState V E)
    (certificate : StateCertificate ctx.indexed state) :
    Nonempty (StateCertificate ctx.indexed (ctx.settleQueue fuel state)) := by
  induction fuel generalizing state with
  | zero => exact PropagationState.drainQueue_certified ctx.indexed ctx.parents ctx.vertices.length state certificate
  | succ fuel ih =>
    obtain ⟨closed⟩ := PropagationState.drainQueue_certified ctx.indexed ctx.parents ctx.vertices.length state certificate
    simp only [settleQueue]
    split
    · exact ⟨closed⟩
    · exact ih _ (StateCertificate.addBatch ctx.indexed (ctx.drain state) closed _ (ctx.localBatch _))

theorem settleQueue_boundary (fuel : Nat) (state : PropagationState V E) (boundary : ctx.Boundary state) :
    ctx.Boundary (ctx.settleQueue fuel state) := by
  induction fuel generalizing state with
  | zero => exact ctx.drain_boundary state boundary
  | succ fuel ih =>
    simp only [settleQueue]
    split
    · exact ctx.drain_boundary state boundary
    · exact ih _ (ctx.add_boundary (ctx.drain state) (ctx.drain_boundary state boundary) _)

theorem settleQueue_queue_empty (fuel : Nat) (state : PropagationState V E)
    (certificate : StateCertificate ctx.indexed state) : (ctx.settleQueue fuel state).queue.pending = [] := by
  induction fuel generalizing state with
  | zero =>
    exact PropagationState.drainQueue_drained ctx.indexed ctx.parents ctx.vertices ctx.covered
      ctx.vertices.length state certificate (by omega)
  | succ fuel ih =>
    obtain ⟨closed⟩ := PropagationState.drainQueue_certified ctx.indexed ctx.parents ctx.vertices.length state certificate
    have empty := PropagationState.drainQueue_drained ctx.indexed ctx.parents ctx.vertices ctx.covered
      ctx.vertices.length state certificate (by omega)
    simp only [settleQueue]
    split
    · exact empty
    · exact ih _ (StateCertificate.addBatch ctx.indexed (ctx.drain state) closed _ (ctx.localBatch _))

/-- 実際の通常排出・局所削除・FIFO追加からなる制御は、集合版と同じ集合を返す。 -/
theorem settleQueue_refines (fuel : Nat) (state : PropagationState V E)
    (certificate : StateCertificate ctx.indexed state) (boundary : ctx.Boundary state) :
    (ctx.settleQueue fuel state).won = G.settle ctx.vertices (fun vertex => ctx.core vertex = true) fuel state.won := by
  classical
  induction fuel generalizing state with
  | zero =>
    exact PropagationState.drainQueue_closure ctx.indexed ctx.parents ctx.vertices ctx.covered state
      certificate boundary.leaves boundary.nodes
  | succ fuel ih =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    obtain ⟨next_certificate⟩ := PropagationState.drainQueue_certified ctx.indexed ctx.parents ctx.vertices.length state certificate
    have next_boundary := ctx.drain_boundary state boundary
    have ordinary : closed.won = G.ordinaryClosure ctx.vertices state.won :=
      PropagationState.drainQueue_closure ctx.indexed ctx.parents ctx.vertices ctx.covered state certificate boundary.leaves boundary.nodes
    by_cases empty : members = []
    · have none : ¬ ∃ vertex, G.localResult ctx.vertices (fun vertex => ctx.core vertex = true)
          (G.ordinaryClosure ctx.vertices state.won) vertex := by
        rintro ⟨vertex, inside⟩
        rw [← ordinary] at inside
        have member := (ctx.localMembers_iff closed vertex).mpr inside
        change vertex ∈ members at member
        rw [empty] at member
        cases member
      change (if members = [] then closed else ctx.settleQueue fuel (closed.addMany members)).won = _
      rw [if_pos empty]
      simp only [ThresholdGame.settle, if_neg none]
      exact ordinary
    · have nonempty : ∃ vertex, G.localResult ctx.vertices (fun vertex => ctx.core vertex = true)
          (G.ordinaryClosure ctx.vertices state.won) vertex := by
        cases list : members with
        | nil => exact False.elim (empty list)
        | cons vertex rest =>
          refine ⟨vertex, ?_⟩
          rw [← ordinary]
          apply (ctx.localMembers_iff closed vertex).mp
          change vertex ∈ members
          simp [list]
      have added_certificate := StateCertificate.addBatch ctx.indexed closed next_certificate members (ctx.localBatch closed)
      have continuation := ih (closed.addMany members) added_certificate (ctx.add_boundary closed next_boundary members)
      change (if members = [] then closed else ctx.settleQueue fuel (closed.addMany members)).won = _
      rw [if_neg empty, continuation]
      simp only [ThresholdGame.settle, if_pos nonempty]
      rw [ctx.local_add_won, ordinary]

/-- 有限予算から停止条件を生成する。局所非空なら新規頂点が増えるため、N回で十分である。 -/
theorem settleQueue_stops (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) :
    G.OrdinaryClosed (ctx.settleQueue ctx.vertices.length state).won ∧
      ∀ vertex, ¬ G.localResult ctx.vertices (fun vertex => ctx.core vertex = true)
        (ctx.settleQueue ctx.vertices.length state).won vertex := by
  rw [ctx.settleQueue_refines ctx.vertices.length state certificate boundary]
  exact G.settle_stops ctx.vertices ctx.covered _ ctx.vertices.length state.won (by omega)

/-- 証明用の予算を使い切った返却でも、通常キューと局所追加候補の両方が実際に空である。 -/
theorem settleQueue_halted (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) :
    (ctx.settleQueue ctx.vertices.length state).queue.pending = [] ∧
      ctx.localMembers (ctx.settleQueue ctx.vertices.length state) = [] := by
  refine ⟨ctx.settleQueue_queue_empty ctx.vertices.length state certificate, ?_⟩
  have none := (ctx.settleQueue_stops state certificate boundary).2
  cases members : ctx.localMembers (ctx.settleQueue ctx.vertices.length state) with
  | nil => rfl
  | cons vertex rest =>
    have inside := (ctx.localMembers_iff (ctx.settleQueue ctx.vertices.length state) vertex).mp (by simp [members])
    exact False.elim (none vertex inside)

theorem settleQueue_exact (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state)
    (covers_core : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) (root : V) :
    (ctx.settleQueue ctx.vertices.length state).won root ↔ G.FourfoldWinning root := by
  rw [ctx.settleQueue_refines ctx.vertices.length state certificate boundary]
  exact G.settle_exact ctx.vertices ctx.covered _ covers_core ctx.vertices.length certificate.region (by omega) root

end QueueContext
end PetaProof.ThresholdGame
