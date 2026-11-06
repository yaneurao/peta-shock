import PetaProof.SccReportFlag

/-!
第二DFSのpush/pop実行列にUInt32のcountを重ねる。
一意な訪問集合により各pop前にcount+1<=Nが成立し、機械整数の更新は折り返さない。
訪問表・スタック自体の有限配列化ではない。
-/
namespace PetaProof.ReverseDfsCounter32

universe u
variable {V : Type u} [DecidableEq V]

theorem total_bound (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (id : Nat) (state : ReverseDfsStack.State V) (valid : ReverseDfsStack.Invariant id state) :
    state.total.length ≤ vertices.length := by
  have same : ∀ vertex, vertex ∈ state.total ↔ vertex ∈ vertices.filter (fun vertex => decide (vertex ∈ state.total)) := by
    intro vertex
    simp [covered vertex]
  have perm := ReverseDfsStack.nodup_perm_of_mem _ _ valid.unique (unique.filter _) same
  rw [perm.length_eq]
  exact List.length_filter_le _ _

def popCount (state : ReverseDfsStack.State V) (counter : UInt32) : UInt32 :=
  if state.pending.isEmpty then counter else counter + 1

theorem pop_refines (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (id : Nat) (state : ReverseDfsStack.State V) (valid : ReverseDfsStack.Invariant id state)
    (fits : vertices.length < UInt32.size) (counter : UInt32) (same : counter.toNat = state.count) :
    (popCount state counter).toNat = (ReverseDfsStack.pop state).count := by
  have upper := total_bound vertices unique covered id state valid
  cases pending : state.pending with
  | nil => simpa only [popCount, pending, List.isEmpty_nil, ↓reduceIte, ReverseDfsStack.pop] using same
  | cons vertex rest =>
    have counted := valid.counted
    simp only [ReverseDfsStack.State.total, List.length_append, pending, List.length_cons] at upper
    have small : counter.toNat + 1 < UInt32.size := by omega
    simp only [popCount, pending, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, UInt32.toNat_add,
      ReverseDfsStack.pop]
    change (counter.toNat + 1) % 4294967296 = state.count + 1
    rw [Nat.mod_eq_of_lt small, same]

inductive Trace (id : Nat) : (ReverseDfsStack.State V × UInt32) → (ReverseDfsStack.State V × UInt32) → Prop
  | refl (state) : Trace id state state
  | push {start state} : Trace id start state → (vertex : V) →
      Trace id start (ReverseDfsStack.push id state.1 vertex, state.2)
  | pop {start state} : Trace id start state → Trace id start (ReverseDfsStack.pop state.1, popCount state.1 state.2)

theorem lift (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (fits : vertices.length < UInt32.size) (id : Nat) (start last : ReverseDfsStack.State V)
    (run : ReverseDfsStack.Run id start last) (valid : ReverseDfsStack.Invariant id start)
    (counter : UInt32) (same : counter.toNat = start.count) :
    ∃ finalCounter, Trace id (start, counter) (last, finalCounter) ∧ finalCounter.toNat = last.count := by
  induction run with
  | refl => exact ⟨counter, .refl _, same⟩
  | @push state prior vertex ih =>
    obtain ⟨current, trace, exact_count⟩ := ih
    refine ⟨current, .push trace vertex, ?_⟩
    cases found : state.result vertex <;> simpa [ReverseDfsStack.push, found] using exact_count
  | @pop state prior ih =>
    obtain ⟨current, trace, exact_count⟩ := ih
    exact ⟨popCount state current, .pop trace,
      pop_refines vertices unique covered id state (prior.preserves valid) fits current exact_count⟩

/-- 外側ループの一回のdescendに適用し、初期count=0からの実更新列を得る。 -/
theorem descend (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (fits : vertices.length < UInt32.size) (parents : V → List V)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state) (root : V) :
    ∃ counter, Trace state.roots.length (ReverseDfsStack.initial state.result, 0)
        (ComponentNumbering.descend vertices.length parents state root, counter) ∧
      counter.toNat = (ComponentNumbering.descend vertices.length parents state root).count := by
  apply lift vertices unique covered fits state.roots.length _ _
    (ComponentNumbering.descend_run vertices.length parents state root)
  · apply ReverseDfsStack.initial_invariant
    intro vertex assigned
    have bad := valid.bounded vertex state.roots.length assigned
    omega
  · rfl

end PetaProof.ReverseDfsCounter32
