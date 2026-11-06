import PetaProof.EscapeFifo
import PetaProof.EscapeCounter

/-! 子を一度popした処理枠で、親のカウンターと距離付きFIFOを同時に更新する。 -/
namespace PetaProof.EscapeFifo

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

structure Frame (V : Type u) where
  child : V
  distance : Nat
  queue : State V

namespace Frame

structure Invariant (frame : Frame V) : Prop where
  queue : EscapeFifo.Invariant frame.queue
  upper : Bound frame.queue (frame.distance + 1)
  width : Width frame.queue (frame.distance + 1)
  active_logged : (frame.child, frame.distance) ∈ frame.queue.popped
  past_bound : ∀ item ∈ frame.queue.popped, item.2 ≤ frame.distance

def begin (state : State V) : Option (Frame V) :=
  match state.pending with
  | [] => none
  | head :: _ => some ⟨head.1, head.2, pop state⟩

omit [DecidableEq V] in
theorem begin_preserves (state : State V) (inv : EscapeFifo.Invariant state)
    (head : V × Nat) (rest : List (V × Nat)) (pending : state.pending = head :: rest) :
    Invariant (⟨head.1, head.2, pop state⟩ : Frame V) := by
  refine ⟨pop_preserves state inv, popped_front_bound state inv head rest pending,
    popped_front_width state inv head rest pending, ?_, ?_⟩
  · simp only [pop, pending]
    simp
  · intro item member
    have inLog : item ∈ state.popped ++ [head] := by simpa only [pop, pending] using member
    rcases List.mem_append.mp inLog with old | singleton
    · exact (List.pairwise_append.mp inv.ordered).2.2 item old head (by simp [pending])
    · have same : item = head := by simpa using singleton
      subst item
      exact Nat.le_refl _

def commit (frame : Frame V) (parent : V) : Option Nat → Frame V
  | none => frame
  | some distance => { frame with queue := EscapeFifo.push frame.queue parent distance }

theorem commit_popped (frame : Frame V) (parent : V) (result : Option Nat) :
    (frame.commit parent result).queue.popped = frame.queue.popped := by
  cases result with
  | none => rfl
  | some distance =>
    cases seen : frame.queue.seen parent <;> simp [commit, EscapeFifo.push, seen]

theorem commit_preserves (frame : Frame V) (inv : Invariant frame) (parent : V) (result : Option Nat)
    (current : result = none ∨ result = some (frame.distance + 1)) : Invariant (frame.commit parent result) := by
  rcases current with absent | ready
  · simpa only [absent, commit] using inv
  · rw [ready]
    refine ⟨push_preserves frame.queue inv.queue parent (frame.distance + 1) inv.upper inv.width,
      push_bound frame.queue parent (frame.distance + 1) inv.upper,
      push_width frame.queue parent (frame.distance + 1) inv.width, ?_, ?_⟩
    · rw [commit_popped]
      exact inv.active_logged
    · rw [commit_popped]
      exact inv.past_bound

/-- seenは証明用。各通知済み元辺の子と距離が、実際の取り出しログに存在する。 -/
def Reported (frame : Frame V) (edges : List E) (child : E → V) (cost : E → Nat)
    (counter : EscapeCounter.State E) : Prop :=
  ∀ edge ∈ edges, counter.seen edge = true → (child edge, cost edge) ∈ frame.queue.popped

omit [DecidableEq V] [DecidableEq E] in
theorem reported_peak_bound (frame : Frame V) (inv : Invariant frame) (edges : List E)
    (child : E → V) (cost : E → Nat) (counter : EscapeCounter.State E)
    (counterInv : EscapeCounter.Invariant edges cost counter) (reported : frame.Reported edges child cost counter) :
    counter.peak ≤ frame.distance := by
  rw [counterInv.exact_peak, EscapeCounter.seenMaximum_bound]
  intro edge member seen
  exact inv.past_bound _ (reported edge member seen)

def notifyParent (own : Bool) (frame : Frame V) (parent : V) (counter : EscapeCounter.State E) (edge : E) :
    EscapeCounter.State E × Frame V :=
  if counter.result.isSome then (counter, frame) else
    let next := EscapeCounter.hit own counter edge frame.distance
    (next, frame.commit parent next.result)

theorem notifyParent_frozen (own : Bool) (frame : Frame V) (parent : V)
    (counter : EscapeCounter.State E) (edge : E) (finished : counter.result.isSome = true) :
    notifyParent own frame parent counter edge = (counter, frame) := by
  simp only [notifyParent, finished, ite_true]

/-- 今回の子の元辺通知で、残数・最大値・FIFO距離順・ログ対応を同時に保つ。 -/
theorem notifyParent_preserves (own : Bool) (frame : Frame V) (inv : Invariant frame) (parent : V)
    (edges : List E) (unique : edges.Nodup) (child : E → V) (cost : E → Nat)
    (counter : EscapeCounter.State E) (counterInv : EscapeCounter.Invariant edges cost counter)
    (reported : frame.Reported edges child cost counter) (edge : E) (member : edge ∈ edges)
    (fresh : counter.seen edge = false) (pending : counter.result = none)
    (currentChild : child edge = frame.child) (currentCost : cost edge = frame.distance) :
    let next := notifyParent own frame parent counter edge
    EscapeCounter.Invariant edges cost next.1 ∧ Invariant next.2 ∧ next.2.Reported edges child cost next.1 := by
  have peak := frame.reported_peak_bound inv edges child cost counter counterInv reported
  have counterNext := EscapeCounter.hit_preserves own counter edge edges cost counterInv unique member fresh
  rw [currentCost] at counterNext
  have form := EscapeCounter.hit_current_distance own counter edge frame.distance pending peak
  have options : (EscapeCounter.hit own counter edge frame.distance).result = none ∨
      (EscapeCounter.hit own counter edge frame.distance).result = some (frame.distance + 1) := by
    rw [form]
    split <;> simp
  simp only [notifyParent, pending, Option.isSome_none, Bool.false_eq_true, ite_false]
  refine ⟨counterNext, frame.commit_preserves inv parent _ options, ?_⟩
  intro other inRow seen
  rw [commit_popped]
  have newlySeen : markSeen counter.seen edge other = true := by
    simpa only [EscapeCounter.hit, pending, Option.isSome_none, Bool.false_eq_true, ite_false] using seen
  rcases (markSeen_true_iff counter.seen edge other).mp newlySeen with same | old
  · subst other
    rw [currentChild, currentCost]
    exact inv.active_logged
  · exact reported other inRow old

end Frame
end PetaProof.EscapeFifo
