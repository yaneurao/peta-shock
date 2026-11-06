import PetaProof.SparseStopped

/-!
positive()のhitを、親一局面の辺IDとleftカウンターで表す。
seenは証明用の通知履歴であり、C++に実行時の重複判定を追加するものではない。
同じ子局面へ進む複数の辺でも、辺IDが異なれば別々に数える。
-/
namespace PetaProof

universe u
variable {E : Type u} [DecidableEq E]

def markSeen (seen : E → Bool) (edge : E) (other : E) : Bool :=
  if other = edge then true else seen other

def remainingEdges (seen : E → Bool) : List E → Nat
  | [] => 0
  | edge :: rest => (if seen edge then 0 else 1) + remainingEdges seen rest

omit [DecidableEq E] in
theorem remaining_initial (edges : List E) : remainingEdges (fun _ => false) edges = edges.length := by
  induction edges with
  | nil => rfl
  | cons _ _ ih => simp [remainingEdges, ih, Nat.add_comm]

omit [DecidableEq E] in
theorem remaining_zero_iff (seen : E → Bool) (edges : List E) :
    remainingEdges seen edges = 0 ↔ ∀ edge ∈ edges, seen edge = true := by
  induction edges with
  | nil => simp [remainingEdges]
  | cons head rest ih =>
    cases flag : seen head <;> simp [remainingEdges, flag, ih, List.forall_mem_cons]

theorem remaining_mark_absent (seen : E → Bool) (edge : E) (edges : List E) (absent : edge ∉ edges) :
    remainingEdges (markSeen seen edge) edges = remainingEdges seen edges := by
  induction edges with
  | nil => rfl
  | cons head rest ih =>
    have different : head ≠ edge := by intro same; exact absent (by simp [same])
    have tail_absent : edge ∉ rest := fun member => absent (by simp [member])
    have head_same : markSeen seen edge head = seen head := by simp [markSeen, different]
    simp only [remainingEdges, head_same, ih tail_absent]

/-- 新しい辺IDの通知一つで、未通知本数が正確に1だけ減る。 -/
theorem remaining_mark_fresh (seen : E → Bool) (edge : E) (edges : List E)
    (unique : edges.Nodup) (member : edge ∈ edges) (fresh : seen edge = false) :
    remainingEdges (markSeen seen edge) edges + 1 = remainingEdges seen edges := by
  induction edges with
  | nil => cases member
  | cons head rest ih =>
    have nodup := List.nodup_cons.mp unique
    by_cases same : head = edge
    · subst head
      have tail_same := remaining_mark_absent seen edge rest nodup.1
      simp [remainingEdges, markSeen, fresh, tail_same, Nat.add_comm]
    · have tail_member : edge ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have tail := ih nodup.2 tail_member
      have head_same : markSeen seen edge head = seen head := by simp [markSeen, same]
      simp only [remainingEdges, head_same]
      omega

structure HitCounter (E : Type u) where
  seen : E → Bool
  left : Nat
  admitted : Bool

namespace HitCounter

/-- OR側は1本の通知で確定、AND側はleftを1減らし0になった時に確定する。 -/
def hit (own : Bool) (counter : HitCounter E) (edge : E) : HitCounter E :=
  if counter.admitted then counter else {
    seen := markSeen counter.seen edge
    left := if own then counter.left else counter.left - 1
    admitted := own || counter.left == 1
  }

def initial (edges : List E) : HitCounter E := {
  seen := fun _ => false
  left := edges.length
  admitted := false
}

/-- 確定後のleftは使わない。未確定なら未通知本数と一致し、OR側には通知済み辺がない。 -/
structure Invariant (own : Bool) (edges : List E) (counter : HitCounter E) : Prop where
  exact_count : counter.admitted = false → counter.left = remainingEdges counter.seen edges
  positive : counter.admitted = false → 0 < counter.left
  or_unseen : own = true → counter.admitted = false → ∀ edge ∈ edges, counter.seen edge = false

omit [DecidableEq E] in
theorem initial_invariant (own : Bool) (edges : List E) (nonempty : 0 < edges.length) :
    Invariant own edges (initial edges) := {
  exact_count := fun _ => (remaining_initial edges).symm
  positive := fun _ => nonempty
  or_unseen := fun _ _ _ _ => rfl
}

/-- Fresh条件が重要であり、hitそのものに重複通知ガードがあるとは仮定しない。 -/
theorem hit_preserves (own : Bool) (counter : HitCounter E) (edge : E) (edges : List E)
    (invariant : Invariant own edges counter) (unique : edges.Nodup)
    (member : edge ∈ edges) (fresh : counter.seen edge = false) :
    Invariant own edges (hit own counter edge) := by
  cases admitted : counter.admitted with
  | true => simpa only [hit, admitted, ite_true] using invariant
  | false =>
    have count := invariant.exact_count admitted
    have positive := invariant.positive admitted
    have decrement := remaining_mark_fresh counter.seen edge edges unique member fresh
    cases own with
    | true =>
      constructor <;> simp [hit, admitted]
    | false =>
      constructor
      · intro pending
        simp only [hit, admitted, Bool.false_eq_true, ite_false]
        omega
      · intro pending
        have not_last : counter.left ≠ 1 := by
          intro last
          simp [hit, admitted, last] at pending
        simp only [hit, admitted, Bool.false_eq_true, ite_false]
        omega
      · intro impossible
        cases impossible

omit [DecidableEq E] in
/-- 有効な新規通知に対して、AND側の符号なしカウンターが0から減算されることはない。 -/
theorem hit_no_underflow (own : Bool) (counter : HitCounter E) (edges : List E)
    (invariant : Invariant own edges counter) (pending : counter.admitted = false) :
    0 < counter.left := invariant.positive pending

/-- AND側が確定するのは、全ての辺IDの通知がそろった時に限る。 -/
theorem and_hit_iff_complete (counter : HitCounter E) (edge : E) (edges : List E)
    (invariant : Invariant false edges counter) (unique : edges.Nodup) (member : edge ∈ edges)
    (fresh : counter.seen edge = false) (pending : counter.admitted = false) :
    (hit false counter edge).admitted = true ↔
      ∀ other ∈ edges, markSeen counter.seen edge other = true := by
  have count := invariant.exact_count pending
  have decrement := remaining_mark_fresh counter.seen edge edges unique member fresh
  rw [← remaining_zero_iff]
  simp only [hit, pending, Bool.false_eq_true, ite_false, Bool.false_or, beq_iff_eq]
  omega

end HitCounter
end PetaProof
