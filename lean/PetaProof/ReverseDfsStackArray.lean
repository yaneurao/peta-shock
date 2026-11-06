import PetaProof.VertexStack32

/-!
第二DFSのpendingもUInt32配列にする。配列の末尾がスタックの上。
poppedは証明専用。復号失敗分岐は全域化のためであり、Validの下では到達しない。
-/
namespace PetaProof.ReverseDfsStackArray

variable {n : Nat}

structure State (n : Nat) where
  result : Array UInt32
  pending : Array UInt32
  popped : List (Fin n)
  count : Nat

def unpack (state : State n) : ReverseDfsResultArray.State n :=
  ⟨state.result, VertexStack32.model n state.pending, state.popped, state.count⟩

def Valid (state : State n) : Prop := VertexStack32.Valid n state.pending

def top (state : State n) : Option (Fin n) := state.pending.back?.bind (VertexStack32.decode n)

def initial (previous : Array UInt32) : State n := ⟨previous, #[], [], 0⟩

def push (id : Nat) (state : State n) (vertex : Fin n) : State n :=
  if ComponentLabels32.get state.result vertex = ComponentLabels32.unset then
    { state with
      result := ComponentLabels32.write state.result vertex id
      pending := state.pending.push (VertexStack32.encode vertex) }
  else state

def pop (state : State n) : State n :=
  match top state with
  | none => state
  | some vertex => { state with
      pending := state.pending.pop
      popped := state.popped ++ [vertex]
      count := state.count + 1 }

theorem top_exact (state : State n) (valid : Valid state) :
    top state = (unpack state).pending.head? :=
  (VertexStack32.model_top state.pending valid).symm

/-- 空でないスタックから得た生番号は、有効な頂点番号かつresultの範囲内である。 -/
theorem top_word_safe (state : State n) (valid : Valid state) (size : state.result.size = n)
    (word : UInt32) (found : state.pending.back? = some word) :
    ∃ vertex : Fin n, top state = some vertex ∧ vertex.val = word.toNat ∧ vertex.val < state.result.size := by
  have inside := VertexStack32.top_range state.pending valid word found
  refine ⟨⟨word.toNat, inside⟩, ?_, rfl, ?_⟩
  · simp [top, found, VertexStack32.decode, inside]
  · simpa only [size] using inside

theorem push_assigned (id : Nat) (state : State n) (vertex : Fin n)
    (assigned : ComponentLabels32.get state.result vertex ≠ ComponentLabels32.unset) :
    push id state vertex = state := by
  simp only [push, if_neg assigned]

theorem push_valid (fits : n ≤ UInt32.size) (id : Nat) (state : State n)
    (valid : Valid state) (vertex : Fin n) : Valid (push id state vertex) := by
  unfold push
  split
  · exact VertexStack32.valid_push_word _ valid _ (by rw [VertexStack32.encode_toNat fits]; exact vertex.isLt)
  · exact valid

theorem pop_valid (state : State n) (valid : Valid state) : Valid (pop state) := by
  unfold pop
  split
  · exact valid
  · exact VertexStack32.valid_pop _ valid

theorem push_refines (fits : n ≤ UInt32.size) (id : Nat) (state : State n) (vertex : Fin n) :
    unpack (push id state vertex) = ReverseDfsResultArray.push id (unpack state) vertex := by
  unfold push ReverseDfsResultArray.push unpack
  split <;> simp only [VertexStack32.model_push fits]

theorem pop_refines (state : State n) (valid : Valid state) :
    unpack (pop state) = ReverseDfsResultArray.pop (unpack state) := by
  have exact_top := top_exact state valid
  cases pending : (unpack state).pending with
  | nil =>
    have empty : top state = none := by simpa only [pending, List.head?_nil] using exact_top
    simp only [pop, empty, ReverseDfsResultArray.pop, pending]
  | cons vertex rest =>
    have found : top state = some vertex := by simpa only [pending, List.head?_cons] using exact_top
    have tail : VertexStack32.model n state.pending.pop = rest := by
      rw [VertexStack32.model_pop _ valid]
      change (unpack state).pending.tail = rest
      rw [pending]
      rfl
    change VertexStack32.model n state.pending = vertex :: rest at pending
    simp only [pop, found, unpack, ReverseDfsResultArray.pop, pending, tail]

def scan (id : Nat) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => scan id rest (push id state vertex)

theorem scan_valid (fits : n ≤ UInt32.size) (id : Nat) (parents : List (Fin n))
    (state : State n) (valid : Valid state) : Valid (scan id parents state) := by
  induction parents generalizing state with
  | nil => exact valid
  | cons vertex rest ih => exact ih _ (push_valid fits id state valid vertex)

theorem scan_refines (fits : n ≤ UInt32.size) (id : Nat) (parents : List (Fin n)) (state : State n) :
    unpack (scan id parents state) = ReverseDfsResultArray.scan id parents (unpack state) := by
  induction parents generalizing state with
  | nil => rfl
  | cons vertex rest ih => rw [scan, ih, push_refines fits, ReverseDfsResultArray.scan]

def visit (id : Nat) (parents : Fin n → List (Fin n)) (state : State n) : State n :=
  match top state with
  | none => state
  | some vertex => scan id (parents vertex) (pop state)

theorem visit_valid (fits : n ≤ UInt32.size) (id : Nat) (parents : Fin n → List (Fin n))
    (state : State n) (valid : Valid state) : Valid (visit id parents state) := by
  unfold visit
  split
  · exact valid
  · exact scan_valid fits id _ _ (pop_valid state valid)

theorem visit_refines (fits : n ≤ UInt32.size) (id : Nat) (parents : Fin n → List (Fin n))
    (state : State n) (valid : Valid state) :
    unpack (visit id parents state) = ReverseDfsResultArray.visit id parents (unpack state) := by
  have exact_top := top_exact state valid
  cases pending : (unpack state).pending with
  | nil =>
    have empty : top state = none := by simpa only [pending, List.head?_nil] using exact_top
    simp only [visit, empty, ReverseDfsResultArray.visit, pending]
  | cons vertex rest =>
    have found : top state = some vertex := by simpa only [pending, List.head?_cons] using exact_top
    rw [visit, found, scan_refines fits, pop_refines state valid, ReverseDfsResultArray.visit, pending]

def walk (id : Nat) (parents : Fin n → List (Fin n)) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state => walk id parents fuel (visit id parents state)

theorem walk_valid (fits : n ≤ UInt32.size) (id : Nat) (parents : Fin n → List (Fin n))
    (fuel : Nat) (state : State n) (valid : Valid state) : Valid (walk id parents fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih _ (visit_valid fits id parents state valid)

theorem walk_refines (fits : n ≤ UInt32.size) (id : Nat) (parents : Fin n → List (Fin n))
    (fuel : Nat) (state : State n) (valid : Valid state) :
    unpack (walk id parents fuel state) = ReverseDfsResultArray.walk id parents fuel (unpack state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [walk, ih _ (visit_valid fits id parents state valid), visit_refines fits id parents state valid,
      ReverseDfsResultArray.walk]

def explore (id : Nat) (previous : Array UInt32) (parents : Fin n → List (Fin n)) (root : Fin n) : State n :=
  walk id parents n (push id (initial previous) root)

theorem explore_valid (fits : n ≤ UInt32.size) (id : Nat) (previous : Array UInt32)
    (parents : Fin n → List (Fin n)) (root : Fin n) : Valid (explore id previous parents root) :=
  walk_valid fits id parents n _ (push_valid fits id (initial previous) (VertexStack32.valid_empty n) root)

theorem explore_refines (fits : n ≤ UInt32.size) (id : Nat) (previous : Array UInt32)
    (parents : Fin n → List (Fin n)) (root : Fin n) :
    unpack (explore id previous parents root) = ReverseDfsResultArray.explore id previous parents root := by
  rw [explore, walk_refines fits id parents n _ (push_valid fits id (initial previous) (VertexStack32.valid_empty n) root),
    push_refines fits]
  rfl

/-- 実スタックの長さにもN上界が移る。経路数を数える必要はない。 -/
theorem stack_bound (id : Nat) (state : State n) (valid : Valid state)
    (invariant : ReverseDfsStack.Invariant id (ReverseDfsResultArray.unpack (unpack state))) :
    state.pending.size ≤ n := by
  have bound := ReverseDfsStack.total_bound (List.finRange n)
    (CoreEnumeration.finRange_unique n) (CoreEnumeration.finRange_covers n) id _ invariant
  simp only [ReverseDfsStack.State.total, ReverseDfsResultArray.unpack, unpack,
    List.length_append, VertexStack32.model_length _ valid, List.length_finRange] at bound
  omega

theorem explore_abstract (fits : n ≤ UInt32.size) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (previous : Array UInt32) (size : previous.size = n) (parents : Fin n → List (Fin n)) (root : Fin n) :
    ReverseDfsResultArray.unpack (unpack (explore id previous parents root)) =
      ReverseDfsStack.explore (List.finRange n) id (ComponentLabels32.model previous) parents root := by
  rw [explore_refines fits]
  exact ReverseDfsResultArray.explore_refines id bounded previous size parents root

/-- 高々N回のvisitで実配列も空になる。fuelは証明上の上界で本番の追加ループではない。 -/
theorem explore_drains (fits : n ≤ UInt32.size) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (previous : Array UInt32) (size : previous.size = n) (parents : Fin n → List (Fin n)) (root : Fin n)
    (unused : ∀ vertex : Fin n, ComponentLabels32.model previous vertex ≠ some id)
    (fresh : ComponentLabels32.model previous root = none) :
    (explore id previous parents root).pending.size = 0 := by
  have empty := ReverseDfsStack.explore_drains (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) id (ComponentLabels32.model previous) parents root unused fresh
  rw [← explore_abstract fits id bounded previous size parents root] at empty
  have length := congrArg List.length empty
  simpa only [ReverseDfsResultArray.unpack, unpack,
    VertexStack32.model_length _ (explore_valid fits id previous parents root), List.length_nil] using length

/-- 中間状態も含め、既存の一意性・割当・countの不変条件が保存される。 -/
theorem walk_invariant (fits : n ≤ UInt32.size) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (parents : Fin n → List (Fin n)) (fuel : Nat) (state : State n) (valid : Valid state)
    (size : state.result.size = n)
    (invariant : ReverseDfsStack.Invariant id (ReverseDfsResultArray.unpack (unpack state))) :
    ReverseDfsStack.Invariant id (ReverseDfsResultArray.unpack (unpack (walk id parents fuel state))) := by
  rw [walk_refines fits id parents fuel state valid,
    ReverseDfsResultArray.walk_refines id bounded parents fuel (unpack state) size]
  exact ReverseDfsStack.walk_preserves id parents fuel _ invariant

theorem walk_stack_bound (fits : n ≤ UInt32.size) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (parents : Fin n → List (Fin n)) (fuel : Nat) (state : State n) (valid : Valid state)
    (size : state.result.size = n)
    (invariant : ReverseDfsStack.Invariant id (ReverseDfsResultArray.unpack (unpack state))) :
    (walk id parents fuel state).pending.size ≤ n :=
  stack_bound id _ (walk_valid fits id parents fuel state valid)
    (walk_invariant fits id bounded parents fuel state valid size invariant)

end PetaProof.ReverseDfsStackArray
