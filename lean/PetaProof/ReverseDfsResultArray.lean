import PetaProof.ComponentLabels32

/-!
第二DFSのresultをArray UInt32にする。pendingは既存のLIFOリスト、poppedは証明用履歴。
ラベルを書いてからpushすることと、各更新の抽象DFSへの一致を証明する。
-/
namespace PetaProof.ReverseDfsResultArray

variable {n : Nat}

structure State (n : Nat) where
  result : Array UInt32
  pending : List (Fin n)
  popped : List (Fin n)
  count : Nat

def unpack (state : State n) : ReverseDfsStack.State (Fin n) :=
  ⟨ComponentLabels32.model state.result, state.pending, state.popped, state.count⟩

def initial (previous : Array UInt32) : State n := ⟨previous, [], [], 0⟩

def push (id : Nat) (state : State n) (vertex : Fin n) : State n :=
  if ComponentLabels32.get state.result vertex = ComponentLabels32.unset then
    { state with result := ComponentLabels32.write state.result vertex id, pending := vertex :: state.pending }
  else state

def pop (state : State n) : State n :=
  match state.pending with
  | [] => state
  | vertex :: rest => { state with pending := rest, popped := state.popped ++ [vertex], count := state.count + 1 }

theorem push_size (id : Nat) (state : State n) (vertex : Fin n) : (push id state vertex).result.size = state.result.size := by
  unfold push
  split <;> simp [ComponentLabels32.write_size]

theorem pop_size (state : State n) : (pop state).result.size = state.result.size := by
  cases pending : state.pending <;> simp [pop, pending]

theorem push_assigned (id : Nat) (state : State n) (vertex : Fin n)
    (assigned : ComponentLabels32.get state.result vertex ≠ ComponentLabels32.unset) : push id state vertex = state := by
  simp only [push, if_neg assigned]

theorem push_refines (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (state : State n) (size : state.result.size = n) (vertex : Fin n) :
    unpack (push id state vertex) = ReverseDfsStack.push id (unpack state) vertex := by
  by_cases fresh : ComponentLabels32.get state.result vertex = ComponentLabels32.unset
  · have found := (ComponentLabels32.guard_exact state.result vertex).mp fresh
    simp only [push, if_pos fresh, unpack, ReverseDfsStack.push, found,
      ComponentLabels32.model_write state.result size vertex id bounded]
  · have assigned : ComponentLabels32.model state.result vertex ≠ none := by
      intro found
      exact fresh ((ComponentLabels32.guard_exact state.result vertex).mpr found)
    cases found : ComponentLabels32.model state.result vertex with
    | none => exact False.elim (assigned found)
    | some label => simp only [push, if_neg fresh, unpack, ReverseDfsStack.push, found]

theorem pop_refines (state : State n) : unpack (pop state) = ReverseDfsStack.pop (unpack state) := by
  cases pending : state.pending <;> simp only [pop, pending, unpack, ReverseDfsStack.pop]

def scan (id : Nat) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => scan id rest (push id state vertex)

theorem scan_size (id : Nat) (parents : List (Fin n)) (state : State n) : (scan id parents state).result.size = state.result.size := by
  induction parents generalizing state with
  | nil => rfl
  | cons vertex rest ih => simpa only [scan, push_size] using ih (push id state vertex)

theorem scan_refines (id : Nat) (bounded : id < ComponentLabels32.unset.toNat) (parents : List (Fin n))
    (state : State n) (size : state.result.size = n) :
    unpack (scan id parents state) = ReverseDfsStack.scan id parents (unpack state) := by
  induction parents generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [scan, ih _ (by rw [push_size]; exact size), push_refines id bounded state size, ReverseDfsStack.scan]

def visit (id : Nat) (parents : Fin n → List (Fin n)) (state : State n) : State n :=
  match state.pending with
  | [] => state
  | vertex :: _ => scan id (parents vertex) (pop state)

theorem visit_size (id : Nat) (parents : Fin n → List (Fin n)) (state : State n) :
    (visit id parents state).result.size = state.result.size := by
  cases pending : state.pending <;> simp only [visit, pending, scan_size, pop_size]

theorem visit_refines (id : Nat) (bounded : id < ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (state : State n) (size : state.result.size = n) :
    unpack (visit id parents state) = ReverseDfsStack.visit id parents (unpack state) := by
  cases pending : state.pending with
  | nil => simp only [visit, pending, ReverseDfsStack.visit, unpack]
  | cons vertex rest =>
    have visible : (unpack state).pending = vertex :: rest := pending
    rw [visit, pending, ReverseDfsStack.visit, visible,
      scan_refines id bounded _ _ (by rw [pop_size]; exact size), pop_refines]

def walk (id : Nat) (parents : Fin n → List (Fin n)) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state => walk id parents fuel (visit id parents state)

theorem walk_size (id : Nat) (parents : Fin n → List (Fin n)) (fuel : Nat) (state : State n) :
    (walk id parents fuel state).result.size = state.result.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simpa only [walk, visit_size] using ih (visit id parents state)

theorem walk_refines (id : Nat) (bounded : id < ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (fuel : Nat) (state : State n) (size : state.result.size = n) :
    unpack (walk id parents fuel state) = ReverseDfsStack.walk id parents fuel (unpack state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [walk, ih _ (by rw [visit_size]; exact size), visit_refines id bounded parents state size, ReverseDfsStack.walk]

def explore (id : Nat) (previous : Array UInt32) (parents : Fin n → List (Fin n)) (root : Fin n) : State n :=
  walk id parents n (push id (initial previous) root)

theorem explore_size (id : Nat) (previous : Array UInt32) (parents : Fin n → List (Fin n)) (root : Fin n) :
    (explore id previous parents root).result.size = previous.size := by
  simp only [explore, walk_size, push_size, initial]

theorem explore_refines (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (previous : Array UInt32) (size : previous.size = n) (parents : Fin n → List (Fin n)) (root : Fin n) :
    unpack (explore id previous parents root) =
      ReverseDfsStack.explore (List.finRange n) id (ComponentLabels32.model previous) parents root := by
  rw [explore, walk_refines id bounded _ _ _ (by rw [push_size]; exact size),
    push_refines id bounded _ size]
  simp only [ReverseDfsStack.explore, List.length_finRange]
  rfl

end PetaProof.ReverseDfsResultArray
