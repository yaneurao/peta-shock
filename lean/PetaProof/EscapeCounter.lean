import PetaProof.HitCounter

/-! 最短脱出FIFOの親ごとの通知残数と最大子距離。元辺ID単位で数える。 -/
namespace PetaProof.EscapeCounter

universe u
variable {E : Type u} [DecidableEq E]

def seenMaximum (seen : E → Bool) (cost : E → Nat) : List E → Nat
  | [] => 0
  | edge :: rest => max (if seen edge then cost edge else 0) (seenMaximum seen cost rest)

omit [DecidableEq E] in
theorem seenMaximum_initial (cost : E → Nat) (edges : List E) :
    seenMaximum (fun _ => false) cost edges = 0 := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => simp [seenMaximum, ih]

theorem seenMaximum_mark_absent (seen : E → Bool) (cost : E → Nat) (edge : E)
    (edges : List E) (absent : edge ∉ edges) :
    seenMaximum (markSeen seen edge) cost edges = seenMaximum seen cost edges := by
  induction edges with
  | nil => rfl
  | cons head rest ih =>
    have different : head ≠ edge := by intro same; exact absent (by simp [same])
    have tailAbsent : edge ∉ rest := fun member => absent (by simp [member])
    simp only [seenMaximum, markSeen, if_neg different, ih tailAbsent]

theorem seenMaximum_mark_fresh (seen : E → Bool) (cost : E → Nat) (edge : E)
    (edges : List E) (unique : edges.Nodup) (member : edge ∈ edges) (fresh : seen edge = false) :
    seenMaximum (markSeen seen edge) cost edges = max (seenMaximum seen cost edges) (cost edge) := by
  induction edges with
  | nil => cases member
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = edge
    · subst head
      have tail := seenMaximum_mark_absent seen cost edge rest parts.1
      simp [seenMaximum, markSeen, fresh, tail, Nat.max_comm]
    · have tailMember : edge ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have tail := ih parts.2 tailMember
      simp only [seenMaximum, markSeen, if_neg same, tail, Nat.max_assoc]

omit [DecidableEq E] in
theorem seenMaximum_bound (seen : E → Bool) (cost : E → Nat) (edges : List E) (bound : Nat) :
    seenMaximum seen cost edges ≤ bound ↔ ∀ edge ∈ edges, seen edge = true → cost edge ≤ bound := by
  induction edges with
  | nil => simp [seenMaximum]
  | cons edge rest ih =>
    cases present : seen edge <;> simp [seenMaximum, present, ih, List.forall_mem_cons, Nat.max_le]

omit [DecidableEq E] in
theorem seenMaximum_complete (seen : E → Bool) (cost : E → Nat) (edges : List E)
    (complete : ∀ edge ∈ edges, seen edge = true) :
    seenMaximum seen cost edges = seenMaximum (fun _ => true) cost edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
    simp only [seenMaximum, complete edge (by simp), ite_true,
      ih (fun other member => complete other (by simp [member]))]

structure State (E : Type u) where
  seen : E → Bool
  left : Nat
  peak : Nat
  result : Option Nat

def initial (edges : List E) : State E := ⟨fun _ => false, edges.length, 0, none⟩

/-- 確定後は凍結する。seenは証明用履歴で、実際の辺通知の一意性からfreshを得る。 -/
def hit (own : Bool) (state : State E) (edge : E) (distance : Nat) : State E :=
  if state.result.isSome then state else {
    seen := markSeen state.seen edge
    left := if own then state.left else state.left - 1
    peak := max state.peak distance
    result := if own then some (distance + 1)
      else if state.left == 1 then some (max state.peak distance + 1) else none
  }

structure Invariant (edges : List E) (cost : E → Nat) (state : State E) : Prop where
  exact_count : state.result = none → state.left = remainingEdges state.seen edges
  positive : state.result = none → 0 < state.left
  exact_peak : state.peak = seenMaximum state.seen cost edges

omit [DecidableEq E] in
theorem initial_invariant (edges : List E) (cost : E → Nat) (nonempty : 0 < edges.length) :
    Invariant edges cost (initial edges) := by
  constructor
  · intro _; exact (remaining_initial edges).symm
  · intro _; exact nonempty
  · exact (seenMaximum_initial cost edges).symm

theorem hit_preserves (own : Bool) (state : State E) (edge : E) (edges : List E) (cost : E → Nat)
    (inv : Invariant edges cost state) (unique : edges.Nodup) (member : edge ∈ edges)
    (fresh : state.seen edge = false) : Invariant edges cost (hit own state edge (cost edge)) := by
  cases result : state.result with
  | some value => simpa only [hit, result, Option.isSome_some, ite_true] using inv
  | none =>
    have count := inv.exact_count result
    have positive := inv.positive result
    have decrease := remaining_mark_fresh state.seen edge edges unique member fresh
    have peak := seenMaximum_mark_fresh state.seen cost edge edges unique member fresh
    cases own with
    | true =>
      constructor
      · simp [hit, result]
      · simp [hit, result]
      · simp only [hit, result, Option.isSome_none, Bool.false_eq_true, ite_false]
        rw [peak, inv.exact_peak]
    | false =>
      constructor
      · intro pending
        simp only [hit, result, Option.isSome_none, Bool.false_eq_true, ite_false] at pending ⊢
        omega
      · intro pending
        have notLast : state.left ≠ 1 := by intro same; simp [hit, result, same] at pending
        simp only [hit, result, Option.isSome_none, Bool.false_eq_true, ite_false]
        omega
      · simp only [hit, result, Option.isSome_none, Bool.false_eq_true, ite_false]
        rw [peak, inv.exact_peak]

/-- FIFOで古い通知距離が現在距離以下なら、今回確定する親距離は必ず現在+1。 -/
theorem hit_current_distance (own : Bool) (state : State E) (edge : E) (distance : Nat)
    (pending : state.result = none) (ordered : state.peak ≤ distance) :
    (hit own state edge distance).result =
      if own || state.left == 1 then some (distance + 1) else none := by
  cases own <;> simp [hit, pending, Nat.max_eq_right ordered]

theorem and_hit_complete (state : State E) (edge : E) (edges : List E) (cost : E → Nat)
    (inv : Invariant edges cost state) (unique : edges.Nodup) (member : edge ∈ edges)
    (fresh : state.seen edge = false) (pending : state.result = none) :
    (hit false state edge (cost edge)).result.isSome = true ↔
      ∀ other ∈ edges, markSeen state.seen edge other = true := by
  have count := inv.exact_count pending
  have positive := inv.positive pending
  have decrease := remaining_mark_fresh state.seen edge edges unique member fresh
  rw [← remaining_zero_iff]
  simp only [hit, pending, Option.isSome_none, Bool.false_eq_true, ite_false]
  split <;> simp_all <;> omega

theorem and_result_maximum (state : State E) (edge : E) (edges : List E) (cost : E → Nat)
    (inv : Invariant edges cost state) (unique : edges.Nodup) (member : edge ∈ edges)
    (fresh : state.seen edge = false) (pending : state.result = none) (distance : Nat)
    (finished : (hit false state edge (cost edge)).result = some distance) :
    distance = seenMaximum (fun _ => true) cost edges + 1 := by
  have complete := (and_hit_complete state edge edges cost inv unique member fresh pending).mp
    (by rw [finished]; rfl)
  have peak := seenMaximum_mark_fresh state.seen cost edge edges unique member fresh
  have all := seenMaximum_complete (markSeen state.seen edge) cost edges complete
  have maximum : max state.peak (cost edge) = seenMaximum (fun _ => true) cost edges := by
    rw [inv.exact_peak, ← peak, all]
  simp only [hit, pending, Option.isSome_none, Bool.false_eq_true, ite_false] at finished
  split at finished
  · simp only [Option.some.injEq] at finished
    omega
  · cases finished

end PetaProof.EscapeCounter
