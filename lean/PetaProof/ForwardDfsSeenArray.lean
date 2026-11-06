import PetaProof.SeenArray8

/-!
第一DFSのseenをUInt8配列へ置き換える。フレームと終了順は従来のリストのまま。
配列の長さ・0/1性を保ち、各tickと根走査を既存の第一DFSへ精密化する。
-/
namespace PetaProof.ForwardDfsSeenArray

variable {n : Nat}

structure State (n : Nat) where
  seen : Array UInt8
  stack : List (ForwardDfs.Frame (Fin n))
  finished : List (Fin n)

structure Valid (state : State n) : Prop where
  size : state.seen.size = n
  binary : SeenArray8.Binary state.seen

def unpack (state : State n) : ForwardDfs.State (Fin n) := ⟨SeenArray8.model state.seen, state.stack, state.finished⟩
def initial (n : Nat) : State n := ⟨SeenArray8.empty n, [], []⟩

theorem initial_valid (n : Nat) : Valid (initial n) := ⟨SeenArray8.empty_size n, SeenArray8.empty_binary n⟩
theorem initial_refines (n : Nat) : unpack (initial n) = ForwardDfs.initial := by
  simp only [unpack, initial, SeenArray8.empty_model, ForwardDfs.initial]

def discover (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  if SeenArray8.model state.seen vertex then state else
    { state with
      seen := SeenArray8.mark state.seen vertex
      stack := ⟨vertex, outgoing vertex⟩ :: state.stack }

theorem discover_valid (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) : Valid (discover outgoing state vertex) := by
  unfold discover
  split
  · exact valid
  · exact ⟨(SeenArray8.mark_size _ _).trans valid.size, SeenArray8.mark_binary _ valid.binary _⟩

theorem discover_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) :
    unpack (discover outgoing state vertex) = ForwardDfs.discover outgoing (unpack state) vertex := by
  simp only [discover, unpack, ForwardDfs.discover]
  split <;> simp only [unpack, SeenArray8.model_mark _ valid.size]

theorem discover_seen_byte (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) : SeenArray8.get (discover outgoing state vertex).seen vertex = 1 := by
  unfold discover
  split
  · exact (SeenArray8.binary_seen_iff_one _ valid.size valid.binary vertex).mp (by assumption)
  · exact SeenArray8.marked_at _ valid.size vertex

theorem discover_visited (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n)
    (seen : SeenArray8.model state.seen vertex = true) : discover outgoing state vertex = state := by
  simp only [discover, seen, ↓reduceIte]

def trim (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with stack := { frame with todo := frame.todo.tail } :: rest }

def retire (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with stack := rest, finished := state.finished ++ [frame.vertex] }

theorem trim_valid (state : State n) (valid : Valid state) : Valid (trim state) := by
  cases stack : state.stack <;> exact ⟨by simpa only [trim, stack] using valid.size,
    by simpa only [trim, stack] using valid.binary⟩

theorem retire_valid (state : State n) (valid : Valid state) : Valid (retire state) := by
  cases stack : state.stack <;> exact ⟨by simpa only [retire, stack] using valid.size,
    by simpa only [retire, stack] using valid.binary⟩

theorem trim_refines (state : State n) : unpack (trim state) = ForwardDfs.trim (unpack state) := by
  cases stack : state.stack <;> simp only [trim, stack, unpack, ForwardDfs.trim]

theorem retire_refines (state : State n) : unpack (retire state) = ForwardDfs.retire (unpack state) := by
  cases stack : state.stack <;> simp only [retire, stack, unpack, ForwardDfs.retire]

def tick (outgoing : Fin n → List (Option (Fin n))) (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: _ =>
    match frame.todo with
    | [] => retire state
    | none :: _ => trim state
    | some child :: _ => discover outgoing (trim state) child

theorem tick_valid (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) : Valid (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa only [tick, stack] using valid
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa only [tick, stack, todo] using retire_valid state valid
    | cons target remaining =>
      cases target with
      | none => simpa only [tick, stack, todo] using trim_valid state valid
      | some child => simpa only [tick, stack, todo] using discover_valid outgoing _ (trim_valid state valid) child

theorem tick_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) : unpack (tick outgoing state) = ForwardDfs.tick outgoing (unpack state) := by
  cases stack : state.stack with
  | nil => simp only [tick, stack, unpack, ForwardDfs.tick]
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa only [tick, stack, todo, ForwardDfs.tick, unpack] using retire_refines state
    | cons target remaining =>
      cases target with
      | none => simpa only [tick, stack, todo, ForwardDfs.tick, unpack] using trim_refines state
      | some child =>
        have same := discover_refines outgoing (trim state) (trim_valid state valid) child
        rw [trim_refines] at same
        simpa only [tick, stack, todo, ForwardDfs.tick, unpack] using same

def walk (outgoing : Fin n → List (Option (Fin n))) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state =>
    match state.stack with
    | [] => state
    | _ :: _ => walk outgoing fuel (tick outgoing state)

theorem walk_valid (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n)
    (valid : Valid state) : Valid (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa only [walk, stack] using valid
    | cons frame rest => simpa only [walk, stack] using ih _ (tick_valid outgoing state valid)

theorem walk_refines (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n)
    (valid : Valid state) : unpack (walk outgoing fuel state) = ForwardDfs.walk outgoing fuel (unpack state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp only [walk, stack, unpack, ForwardDfs.walk]
    | cons frame rest =>
      rw [walk, stack, ih _ (tick_valid outgoing state valid), tick_refines outgoing state valid]
      simp only [ForwardDfs.walk, unpack, stack]

theorem walk_empty (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n)
    (empty : state.stack = []) : walk outgoing fuel state = state := by
  cases fuel <;> simp only [walk, empty]

def root (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  walk outgoing (ForwardDfs.capacity (List.finRange n) outgoing) (discover outgoing state vertex)

theorem root_valid (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) : Valid (root outgoing state vertex) :=
  walk_valid outgoing _ _ (discover_valid outgoing state valid vertex)

theorem root_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) :
    unpack (root outgoing state vertex) = ForwardDfs.root (List.finRange n) outgoing (unpack state) vertex := by
  rw [root, walk_refines outgoing _ _ (discover_valid outgoing state valid vertex), discover_refines outgoing state valid]
  rfl

/-- 外側ループで既訪問の根を飛ばす操作に一致する。根走査の間はstackが空である。 -/
theorem root_visited_noop (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (empty : state.stack = []) (vertex : Fin n) (seen : SeenArray8.model state.seen vertex = true) :
    root outgoing state vertex = state := by
  rw [root, discover_visited outgoing state vertex seen]
  exact walk_empty outgoing _ state empty

def forest (outgoing : Fin n → List (Option (Fin n))) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => forest outgoing rest (root outgoing state vertex)

theorem forest_valid (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) (state : State n)
    (valid : Valid state) : Valid (forest outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact valid
  | cons vertex rest ih => exact ih _ (root_valid outgoing state valid vertex)

theorem forest_refines (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) (state : State n)
    (valid : Valid state) :
    unpack (forest outgoing roots state) = ForwardDfs.forest (List.finRange n) outgoing roots (unpack state) := by
  induction roots generalizing state with
  | nil => rfl
  | cons vertex rest ih =>
    rw [forest, ih _ (root_valid outgoing state valid vertex), root_refines outgoing state valid, ForwardDfs.forest]

def finish (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) : State n := forest outgoing roots (initial n)
def order (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) : List (Fin n) :=
  (finish outgoing roots).finished.reverse

theorem finish_valid (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) : Valid (finish outgoing roots) :=
  forest_valid outgoing roots _ (initial_valid n)

theorem finish_refines (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    unpack (finish outgoing roots) = ForwardDfs.finish (List.finRange n) roots outgoing := by
  rw [finish, forest_refines outgoing roots _ (initial_valid n), initial_refines, ForwardDfs.finish]

theorem order_exact (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    order outgoing roots = ForwardDfs.order (List.finRange n) roots outgoing := by
  have same := congrArg ForwardDfs.State.finished (finish_refines outgoing roots)
  exact congrArg List.reverse same

/-- 全根を走査した後の生の訪問表は、全要素が1になる。 -/
theorem finish_byte_one (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n))
    (covered : ∀ vertex, vertex ∈ roots) (vertex : Fin n) : SeenArray8.get (finish outgoing roots).seen vertex = 1 := by
  have seen := ForwardDfs.forest_member_seen (List.finRange n) outgoing roots ForwardDfs.initial vertex (covered vertex)
  change (ForwardDfs.finish (List.finRange n) roots outgoing).seen vertex = true at seen
  rw [← finish_refines outgoing roots] at seen
  exact (SeenArray8.binary_seen_iff_one _ (finish_valid outgoing roots).size
    (finish_valid outgoing roots).binary vertex).mp seen

theorem root_drains (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (empty : state.stack = []) (vertex : Fin n) :
    (root outgoing state vertex).stack = [] := by
  have drained := ForwardDfs.root_drains (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) outgoing (unpack state) empty vertex
  rw [← root_refines outgoing state valid vertex] at drained
  exact drained

theorem finish_stack_empty (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).stack = [] := by
  have drained := ForwardDfs.forest_drains (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) outgoing roots ForwardDfs.initial rfl
  change (ForwardDfs.finish (List.finRange n) roots outgoing).stack = [] at drained
  rw [← finish_refines outgoing roots] at drained
  exact drained

theorem order_covers (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n))
    (covered : ∀ vertex, vertex ∈ roots) (vertex : Fin n) : vertex ∈ order outgoing roots := by
  rw [order_exact]
  exact ForwardDfs.order_covers (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) roots covered outgoing vertex

theorem finish_unique (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).finished.Nodup := by
  have unique := ForwardDfs.finish_unique (List.finRange n) roots outgoing
  rw [← finish_refines outgoing roots] at unique
  exact unique

theorem walk_invariant (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n)
    (valid : Valid state) (invariant : ForwardDfs.Invariant (unpack state)) :
    ForwardDfs.Invariant (unpack (walk outgoing fuel state)) := by
  rw [walk_refines outgoing fuel state valid]
  exact ForwardDfs.walk_preserves outgoing fuel _ invariant

/-- 非空tickの会計は訪問表を配列化しても変わらない。予算は証明用の関数である。 -/
theorem tick_budget (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (active : state.stack ≠ []) :
    ForwardDfs.budget (List.finRange n) outgoing (unpack (tick outgoing state)) + 1 =
      ForwardDfs.budget (List.finRange n) outgoing (unpack state) := by
  rw [tick_refines outgoing state valid]
  exact ForwardDfs.tick_budget (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) outgoing _ active

theorem tick_byte_stable (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) (seen : SeenArray8.get state.seen vertex = 1) :
    SeenArray8.get (tick outgoing state).seen vertex = 1 := by
  have visited := (SeenArray8.binary_seen_iff_one _ valid.size valid.binary vertex).mpr seen
  have stable := ForwardDfs.tick_seen_stable outgoing (unpack state) vertex visited
  rw [← tick_refines outgoing state valid] at stable
  exact (SeenArray8.binary_seen_iff_one _ (tick_valid outgoing state valid).size
    (tick_valid outgoing state valid).binary vertex).mp stable

end PetaProof.ForwardDfsSeenArray
