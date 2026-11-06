import PetaProof.ArrayLifo

/-!
第一DFSのフレームコンテナを有限Arrayへ置き換える。
フレームのvertexはFin N、todoは既存の未走査部分リストで、UInt32カーソルへの精密化は別段階。
-/
namespace PetaProof.ForwardDfsFrameArray

variable {n : Nat}

structure State (n : Nat) where
  seen : Array UInt8
  stack : Array (ForwardDfs.Frame (Fin n))
  finished : Array UInt32

def unpack (state : State n) : ForwardDfsOrderArray.State n :=
  ⟨state.seen, ArrayLifo.model state.stack, state.finished⟩

def Valid (state : State n) : Prop := ForwardDfsOrderArray.Valid (unpack state)

def initial (n : Nat) : State n := ⟨SeenArray8.empty n, #[], #[]⟩

theorem initial_refines (n : Nat) : unpack (initial n) = ForwardDfsOrderArray.initial n := rfl
theorem initial_valid (n : Nat) : Valid (initial n) := ForwardDfsOrderArray.initial_valid n

def discover (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  if SeenArray8.model state.seen vertex then state else
    { state with
      seen := SeenArray8.mark state.seen vertex
      stack := state.stack.push ⟨vertex, outgoing vertex⟩ }

def trim (state : State n) : State n :=
  match state.stack.back? with
  | none => state
  | some frame => { state with stack := ArrayLifo.replaceBack state.stack { frame with todo := frame.todo.tail } }

def retire (state : State n) : State n :=
  match state.stack.back? with
  | none => state
  | some frame => { state with
      stack := state.stack.pop
      finished := state.finished.push (VertexStack32.encode frame.vertex) }

theorem discover_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) :
    unpack (discover outgoing state vertex) = ForwardDfsOrderArray.discover outgoing (unpack state) vertex := by
  unfold discover ForwardDfsOrderArray.discover unpack
  split <;> simp only [ArrayLifo.model_push]

theorem trim_refines (state : State n) : unpack (trim state) = ForwardDfsOrderArray.trim (unpack state) := by
  have back := (ArrayLifo.model_back state.stack).symm
  cases stack : ArrayLifo.model state.stack with
  | nil =>
    have empty : state.stack.back? = none := by simpa only [stack, List.head?_nil] using back
    simp only [trim, empty, unpack, ForwardDfsOrderArray.trim, stack]
  | cons frame rest =>
    have top : state.stack.back? = some frame := by simpa only [stack, List.head?_cons] using back
    simp only [trim, top, unpack, ForwardDfsOrderArray.trim, ArrayLifo.model_replace, stack]

theorem retire_refines (state : State n) : unpack (retire state) = ForwardDfsOrderArray.retire (unpack state) := by
  have back := (ArrayLifo.model_back state.stack).symm
  cases stack : ArrayLifo.model state.stack with
  | nil =>
    have empty : state.stack.back? = none := by simpa only [stack, List.head?_nil] using back
    simp only [retire, empty, unpack, ForwardDfsOrderArray.retire, stack]
  | cons frame rest =>
    have top : state.stack.back? = some frame := by simpa only [stack, List.head?_cons] using back
    simp only [retire, top, unpack, ForwardDfsOrderArray.retire, ArrayLifo.model_pop, stack, List.tail_cons]

theorem discover_valid (outgoing : Fin n → List (Option (Fin n))) (state : State n) (valid : Valid state) (vertex : Fin n) :
    Valid (discover outgoing state vertex) := by
  unfold Valid
  rw [discover_refines]
  exact ForwardDfsOrderArray.discover_valid outgoing _ valid vertex

theorem trim_valid (state : State n) (valid : Valid state) : Valid (trim state) := by
  unfold Valid
  rw [trim_refines]
  exact ForwardDfsOrderArray.trim_valid _ valid

theorem retire_valid (fits : n ≤ UInt32.size) (state : State n) (valid : Valid state) : Valid (retire state) := by
  unfold Valid
  rw [retire_refines]
  exact ForwardDfsOrderArray.retire_valid fits _ valid

def tick (outgoing : Fin n → List (Option (Fin n))) (state : State n) : State n :=
  match state.stack.back? with
  | none => state
  | some frame =>
    match frame.todo with
    | [] => retire state
    | none :: _ => trim state
    | some child :: _ => discover outgoing (trim state) child

theorem tick_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n) :
    unpack (tick outgoing state) = ForwardDfsOrderArray.tick outgoing (unpack state) := by
  have back := (ArrayLifo.model_back state.stack).symm
  cases stack : ArrayLifo.model state.stack with
  | nil =>
    have empty : state.stack.back? = none := by simpa only [stack, List.head?_nil] using back
    simp only [tick, empty, unpack, ForwardDfsOrderArray.tick, stack]
  | cons frame rest =>
    have top : state.stack.back? = some frame := by simpa only [stack, List.head?_cons] using back
    cases todo : frame.todo with
    | nil => simpa only [tick, top, todo, unpack, ForwardDfsOrderArray.tick, stack] using retire_refines state
    | cons target remaining =>
      cases target with
      | none => simpa only [tick, top, todo, unpack, ForwardDfsOrderArray.tick, stack] using trim_refines state
      | some child =>
        have same := discover_refines outgoing (trim state) child
        rw [trim_refines] at same
        simpa only [tick, top, todo, unpack, ForwardDfsOrderArray.tick, stack] using same

theorem tick_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) : Valid (tick outgoing state) := by
  unfold Valid
  rw [tick_refines]
  exact ForwardDfsOrderArray.tick_valid fits outgoing _ valid

def walk (outgoing : Fin n → List (Option (Fin n))) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state =>
    match state.stack.back? with
    | none => state
    | some _ => walk outgoing fuel (tick outgoing state)

theorem walk_refines (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n) :
    unpack (walk outgoing fuel state) = ForwardDfsOrderArray.walk outgoing fuel (unpack state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have back := (ArrayLifo.model_back state.stack).symm
    cases stack : ArrayLifo.model state.stack with
    | nil =>
      have empty : state.stack.back? = none := by simpa only [stack, List.head?_nil] using back
      simp only [walk, empty, unpack, ForwardDfsOrderArray.walk, stack]
    | cons frame rest =>
      have top : state.stack.back? = some frame := by simpa only [stack, List.head?_cons] using back
      rw [walk, top, ih, tick_refines]
      simp only [unpack, ForwardDfsOrderArray.walk, stack]

theorem walk_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) : Valid (walk outgoing fuel state) := by
  unfold Valid
  rw [walk_refines]
  exact ForwardDfsOrderArray.walk_valid fits outgoing fuel _ valid

def root (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  walk outgoing (ForwardDfs.capacity (List.finRange n) outgoing) (discover outgoing state vertex)

theorem root_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) :
    unpack (root outgoing state vertex) = ForwardDfsOrderArray.root outgoing (unpack state) vertex := by
  rw [root, walk_refines, discover_refines]
  rfl

def forest (outgoing : Fin n → List (Option (Fin n))) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => forest outgoing rest (root outgoing state vertex)

theorem forest_refines (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) (state : State n) :
    unpack (forest outgoing roots state) = ForwardDfsOrderArray.forest outgoing roots (unpack state) := by
  induction roots generalizing state with
  | nil => rfl
  | cons vertex rest ih => rw [forest, ih, root_refines, ForwardDfsOrderArray.forest]

theorem forest_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n))
    (state : State n) (valid : Valid state) : Valid (forest outgoing roots state) := by
  unfold Valid
  rw [forest_refines]
  exact ForwardDfsOrderArray.forest_valid fits outgoing roots _ valid

def finish (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) : State n := forest outgoing roots (initial n)

theorem finish_refines (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    unpack (finish outgoing roots) = ForwardDfsOrderArray.finish outgoing roots := by
  rw [finish, forest_refines, initial_refines, ForwardDfsOrderArray.finish]

theorem finish_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    Valid (finish outgoing roots) := forest_valid fits outgoing roots _ (initial_valid n)

theorem finish_array_exact (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).finished = (ForwardDfsOrderArray.finish outgoing roots).finished :=
  congrArg ForwardDfsOrderArray.State.finished (finish_refines outgoing roots)

theorem finish_seen_exact (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).seen = (ForwardDfsOrderArray.finish outgoing roots).seen :=
  congrArg ForwardDfsOrderArray.State.seen (finish_refines outgoing roots)

def abstract (state : State n) : ForwardDfs.State (Fin n) :=
  ForwardDfsSeenArray.unpack (ForwardDfsOrderArray.unpack (unpack state))

theorem discover_abstract (outgoing : Fin n → List (Option (Fin n)))
    (state : State n) (valid : Valid state) (vertex : Fin n) :
    abstract (discover outgoing state vertex) = ForwardDfs.discover outgoing (abstract state) vertex := by
  unfold abstract
  rw [discover_refines, ForwardDfsOrderArray.discover_refines,
    ForwardDfsSeenArray.discover_refines outgoing _ (ForwardDfsOrderArray.seen_valid _ valid)]

theorem discover_invariant (outgoing : Fin n → List (Option (Fin n)))
    (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) (vertex : Fin n) :
    ForwardDfs.Invariant (abstract (discover outgoing state vertex)) := by
  rw [discover_abstract outgoing state valid vertex]
  exact ForwardDfs.discover_preserves outgoing _ invariant vertex

theorem initial_invariant (n : Nat) : ForwardDfs.Invariant (abstract (initial n)) := by
  have same : abstract (initial n) = ForwardDfs.initial := by
    unfold abstract
    rw [initial_refines, ForwardDfsOrderArray.initial_refines, ForwardDfsSeenArray.initial_refines]
  rw [same]
  exact ForwardDfs.initial_invariant

theorem walk_abstract (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) :
    abstract (walk outgoing fuel state) = ForwardDfs.walk outgoing fuel (abstract state) := by
  unfold abstract
  rw [walk_refines, ForwardDfsOrderArray.walk_refines fits,
    ForwardDfsSeenArray.walk_refines outgoing fuel _ (ForwardDfsOrderArray.seen_valid _ valid)]

theorem walk_invariant (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) :
    ForwardDfs.Invariant (abstract (walk outgoing fuel state)) := by
  rw [walk_abstract fits outgoing fuel state valid]
  exact ForwardDfs.walk_preserves outgoing fuel _ invariant

/-- 活動中の頂点の一意性から、経路数でなく頂点数で実配列長を抑える。 -/
theorem stack_bound (state : State n) (invariant : ForwardDfs.Invariant (abstract state)) : state.stack.size ≤ n := by
  let active := (ArrayLifo.model state.stack).map ForwardDfs.Frame.vertex
  have unique : active.Nodup := (List.pairwise_append.mp invariant.unique).2.1
  have perm := ReverseDfsStack.nodup_perm_of_mem active
    ((List.finRange n).filter (fun vertex => decide (vertex ∈ active))) unique
    ((CoreEnumeration.finRange_unique n).filter _) (by
      intro vertex
      simp [CoreEnumeration.finRange_covers])
  have bound := List.length_filter_le (fun vertex => decide (vertex ∈ active)) (List.finRange n)
  rw [← perm.length_eq] at bound
  simpa only [active, List.length_map, ArrayLifo.model_length, List.length_finRange] using bound

theorem walk_stack_bound (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) :
    (walk outgoing fuel state).stack.size ≤ n :=
  stack_bound _ (walk_invariant fits outgoing fuel state valid invariant)

theorem seeded_walk_bound (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) (vertex : Fin n) :
    (walk outgoing fuel (discover outgoing state vertex)).stack.size ≤ n :=
  walk_stack_bound fits outgoing fuel _ (discover_valid outgoing state valid vertex)
    (discover_invariant outgoing state valid invariant vertex)

theorem finish_abstract (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    abstract (finish outgoing roots) = ForwardDfs.finish (List.finRange n) roots outgoing := by
  unfold abstract
  rw [finish_refines, ForwardDfsOrderArray.finish_abstract fits]

theorem finish_stack_empty (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).stack = #[] := by
  have drained := ForwardDfs.forest_drains (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) outgoing roots ForwardDfs.initial rfl
  change (ForwardDfs.finish (List.finRange n) roots outgoing).stack = [] at drained
  rw [← finish_abstract fits outgoing roots] at drained
  have size := congrArg List.length drained
  simp only [abstract, ForwardDfsSeenArray.unpack, ForwardDfsOrderArray.unpack, unpack,
    ArrayLifo.model_length, List.length_nil] at size
  exact Array.eq_empty_of_size_eq_zero size

theorem root_abstract (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (state : State n) (valid : Valid state) (vertex : Fin n) :
    abstract (root outgoing state vertex) = ForwardDfs.root (List.finRange n) outgoing (abstract state) vertex := by
  unfold abstract
  rw [root_refines, ForwardDfsOrderArray.root_refines fits,
    ForwardDfsSeenArray.root_refines outgoing _ (ForwardDfsOrderArray.seen_valid _ valid)]

theorem root_drains (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (state : State n) (valid : Valid state) (empty : state.stack = #[]) (vertex : Fin n) :
    (root outgoing state vertex).stack = #[] := by
  have before : (abstract state).stack = [] := by
    simp only [abstract, ForwardDfsSeenArray.unpack, ForwardDfsOrderArray.unpack, unpack, empty, ArrayLifo.model_empty]
  have drained := ForwardDfs.root_drains (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) outgoing (abstract state) before vertex
  rw [← root_abstract fits outgoing state valid vertex] at drained
  have size := congrArg List.length drained
  simp only [abstract, ForwardDfsSeenArray.unpack, ForwardDfsOrderArray.unpack, unpack,
    ArrayLifo.model_length, List.length_nil] at size
  exact Array.eq_empty_of_size_eq_zero size

theorem root_invariant (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) (vertex : Fin n) :
    ForwardDfs.Invariant (abstract (root outgoing state vertex)) := by
  rw [root_abstract fits outgoing state valid vertex]
  exact ForwardDfs.root_preserves (List.finRange n) outgoing _ invariant vertex

theorem forest_abstract (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (roots : List (Fin n)) (state : State n) (valid : Valid state) :
    abstract (forest outgoing roots state) = ForwardDfs.forest (List.finRange n) outgoing roots (abstract state) := by
  unfold abstract
  rw [forest_refines, ForwardDfsOrderArray.forest_refines fits,
    ForwardDfsSeenArray.forest_refines outgoing roots _ (ForwardDfsOrderArray.seen_valid _ valid)]

theorem forest_invariant (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (roots : List (Fin n)) (state : State n) (valid : Valid state) (invariant : ForwardDfs.Invariant (abstract state)) :
    ForwardDfs.Invariant (abstract (forest outgoing roots state)) := by
  rw [forest_abstract fits outgoing roots state valid]
  exact ForwardDfs.forest_preserves (List.finRange n) outgoing roots _ invariant

/-- 子を積む前の末尾が親であり、その未走査部分だけを先に進める。 -/
theorem descend_stack (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (frame : ForwardDfs.Frame (Fin n)) (child : Fin n) (remaining : List (Option (Fin n)))
    (top : state.stack.back? = some frame) (todo : frame.todo = some child :: remaining)
    (unseen : SeenArray8.model state.seen child = false) :
    (tick outgoing state).stack =
      (ArrayLifo.replaceBack state.stack { frame with todo := remaining }).push ⟨child, outgoing child⟩ := by
  simp only [tick, top, todo, trim, discover]
  simp only [unseen, Bool.false_eq_true, ↓reduceIte, todo, List.tail_cons]

end PetaProof.ForwardDfsFrameArray
