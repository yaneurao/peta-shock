import PetaProof.FinishingArray32

/-!
第一DFSのseenと終了列を配列で保持する。フレームはまだ既存のリスト表現。
終了した頂点だけをUInt32で末尾追加し、根走査の間も同じ終了列を引き継ぐ。
-/
namespace PetaProof.ForwardDfsOrderArray

variable {n : Nat}

structure State (n : Nat) where
  seen : Array UInt8
  stack : List (ForwardDfs.Frame (Fin n))
  finished : Array UInt32

def unpack (state : State n) : ForwardDfsSeenArray.State n :=
  ⟨state.seen, state.stack, FinishingArray32.model n state.finished⟩

structure Valid (state : State n) : Prop where
  size : state.seen.size = n
  binary : SeenArray8.Binary state.seen
  finished : VertexStack32.Valid n state.finished

theorem seen_valid (state : State n) (valid : Valid state) : ForwardDfsSeenArray.Valid (unpack state) :=
  ⟨valid.size, valid.binary⟩

def initial (n : Nat) : State n := ⟨SeenArray8.empty n, [], #[]⟩

theorem initial_valid (n : Nat) : Valid (initial n) :=
  ⟨SeenArray8.empty_size n, SeenArray8.empty_binary n, VertexStack32.valid_empty n⟩

theorem initial_refines (n : Nat) : unpack (initial n) = ForwardDfsSeenArray.initial n := rfl

def discover (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  if SeenArray8.model state.seen vertex then state else
    { state with
      seen := SeenArray8.mark state.seen vertex
      stack := ⟨vertex, outgoing vertex⟩ :: state.stack }

def trim (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with stack := { frame with todo := frame.todo.tail } :: rest }

def retire (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with
      stack := rest
      finished := state.finished.push (VertexStack32.encode frame.vertex) }

theorem discover_valid (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) : Valid (discover outgoing state vertex) := by
  unfold discover
  split
  · exact valid
  · exact ⟨(SeenArray8.mark_size _ _).trans valid.size, SeenArray8.mark_binary _ valid.binary _, valid.finished⟩

theorem trim_valid (state : State n) (valid : Valid state) : Valid (trim state) := by
  cases stack : state.stack <;> exact ⟨by simpa only [trim, stack] using valid.size,
    by simpa only [trim, stack] using valid.binary, by simpa only [trim, stack] using valid.finished⟩

theorem retire_valid (fits : n ≤ UInt32.size) (state : State n) (valid : Valid state) : Valid (retire state) := by
  cases stack : state.stack with
  | nil => simpa only [retire, stack] using valid
  | cons frame rest =>
    simp only [retire, stack]
    refine ⟨valid.size, valid.binary, ?_⟩
    exact VertexStack32.valid_push_word state.finished valid.finished _ (by
      rw [VertexStack32.encode_toNat fits]; exact frame.vertex.isLt)

theorem discover_refines (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) :
    unpack (discover outgoing state vertex) = ForwardDfsSeenArray.discover outgoing (unpack state) vertex := by
  unfold discover ForwardDfsSeenArray.discover unpack
  split <;> rfl

theorem trim_refines (state : State n) : unpack (trim state) = ForwardDfsSeenArray.trim (unpack state) := by
  cases stack : state.stack <;> simp only [trim, stack, unpack, ForwardDfsSeenArray.trim]

theorem retire_refines (fits : n ≤ UInt32.size) (state : State n) :
    unpack (retire state) = ForwardDfsSeenArray.retire (unpack state) := by
  cases stack : state.stack <;> simp only [retire, stack, unpack, ForwardDfsSeenArray.retire, FinishingArray32.model_push fits]

def tick (outgoing : Fin n → List (Option (Fin n))) (state : State n) : State n :=
  match state.stack with
  | [] => state
  | frame :: _ =>
    match frame.todo with
    | [] => retire state
    | none :: _ => trim state
    | some child :: _ => discover outgoing (trim state) child

theorem tick_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) : Valid (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa only [tick, stack] using valid
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa only [tick, stack, todo] using retire_valid fits state valid
    | cons target remaining =>
      cases target with
      | none => simpa only [tick, stack, todo] using trim_valid state valid
      | some child => simpa only [tick, stack, todo] using discover_valid outgoing _ (trim_valid state valid) child

theorem tick_refines (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (state : State n) :
    unpack (tick outgoing state) = ForwardDfsSeenArray.tick outgoing (unpack state) := by
  cases stack : state.stack with
  | nil => simp only [tick, stack, unpack, ForwardDfsSeenArray.tick]
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa only [tick, stack, todo, ForwardDfsSeenArray.tick, unpack] using retire_refines fits state
    | cons target remaining =>
      cases target with
      | none => simpa only [tick, stack, todo, ForwardDfsSeenArray.tick, unpack] using trim_refines state
      | some child =>
        have same := discover_refines outgoing (trim state) child
        rw [trim_refines] at same
        simpa only [tick, stack, todo, ForwardDfsSeenArray.tick, unpack] using same

def walk (outgoing : Fin n → List (Option (Fin n))) : Nat → State n → State n
  | 0, state => state
  | fuel + 1, state =>
    match state.stack with
    | [] => state
    | _ :: _ => walk outgoing fuel (tick outgoing state)

theorem walk_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat)
    (state : State n) (valid : Valid state) : Valid (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa only [walk, stack] using valid
    | cons frame rest => simpa only [walk, stack] using ih _ (tick_valid fits outgoing state valid)

theorem walk_refines (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (fuel : Nat) (state : State n) :
    unpack (walk outgoing fuel state) = ForwardDfsSeenArray.walk outgoing fuel (unpack state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simp only [walk, stack, unpack, ForwardDfsSeenArray.walk]
    | cons frame rest =>
      rw [walk, stack, ih, tick_refines fits]
      simp only [ForwardDfsSeenArray.walk, unpack, stack]

def root (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) : State n :=
  walk outgoing (ForwardDfs.capacity (List.finRange n) outgoing) (discover outgoing state vertex)

theorem root_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (state : State n)
    (valid : Valid state) (vertex : Fin n) : Valid (root outgoing state vertex) :=
  walk_valid fits outgoing _ _ (discover_valid outgoing state valid vertex)

theorem root_refines (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (state : State n) (vertex : Fin n) :
    unpack (root outgoing state vertex) = ForwardDfsSeenArray.root outgoing (unpack state) vertex := by
  rw [root, walk_refines fits, discover_refines]
  rfl

def forest (outgoing : Fin n → List (Option (Fin n))) : List (Fin n) → State n → State n
  | [], state => state
  | vertex :: rest, state => forest outgoing rest (root outgoing state vertex)

theorem forest_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n))
    (state : State n) (valid : Valid state) : Valid (forest outgoing roots state) := by
  induction roots generalizing state with
  | nil => exact valid
  | cons vertex rest ih => exact ih _ (root_valid fits outgoing state valid vertex)

theorem forest_refines (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) (state : State n) :
    unpack (forest outgoing roots state) = ForwardDfsSeenArray.forest outgoing roots (unpack state) := by
  induction roots generalizing state with
  | nil => rfl
  | cons vertex rest ih => rw [forest, ih, root_refines fits, ForwardDfsSeenArray.forest]

def finish (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) : State n := forest outgoing roots (initial n)

theorem finish_valid (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    Valid (finish outgoing roots) := forest_valid fits outgoing roots _ (initial_valid n)

theorem finish_refines (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    unpack (finish outgoing roots) = ForwardDfsSeenArray.finish outgoing roots := by
  rw [finish, forest_refines fits, initial_refines, ForwardDfsSeenArray.finish]

theorem finish_abstract (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    ForwardDfsSeenArray.unpack (unpack (finish outgoing roots)) = ForwardDfs.finish (List.finRange n) roots outgoing := by
  rw [finish_refines fits, ForwardDfsSeenArray.finish_refines]

theorem reverse_order_exact (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    VertexStack32.model n (finish outgoing roots).finished = ForwardDfs.order (List.finRange n) roots outgoing := by
  rw [FinishingArray32.reverse_model]
  have same := congrArg ForwardDfs.State.finished (finish_abstract fits outgoing roots)
  exact congrArg List.reverse same

/-- 全根を網羅した場合だけ、完成した実配列の長さがNに等しい。 -/
theorem finish_size (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n))
    (covered : ∀ vertex, vertex ∈ roots) : (finish outgoing roots).finished.size = n := by
  have same := congrArg ForwardDfs.State.finished (finish_abstract fits outgoing roots)
  have length := (ForwardDfs.finish_perm (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) roots covered outgoing).length_eq
  rw [← same] at length
  simpa only [ForwardDfsSeenArray.unpack, unpack,
    FinishingArray32.model_length _ (finish_valid fits outgoing roots).finished, List.length_finRange] using length

theorem finish_words_unique (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n))) (roots : List (Fin n)) :
    (finish outgoing roots).finished.toList.Nodup := by
  have unique := ForwardDfsSeenArray.finish_unique outgoing roots
  rw [← finish_refines fits outgoing roots] at unique
  change (FinishingArray32.model n (finish outgoing roots).finished).Nodup at unique
  rw [← FinishingArray32.reencode _ (finish_valid fits outgoing roots).finished]
  exact List.Pairwise.map VertexStack32.encode
    (fun a b different same => different (FinishingArray32.encode_injective fits same)) unique

end PetaProof.ForwardDfsOrderArray
