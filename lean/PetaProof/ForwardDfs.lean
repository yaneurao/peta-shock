import PetaProof.ReverseDfsLabels
import PetaProof.DeletionQueue

/-!
第一DFSの出辺カーソルを、各フレームの未走査リストで表す。
noneはleafまたは不許可辺の走査枠。親は残り出辺を保持したまま子へ降りる。
-/
namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

structure Frame (V : Type u) where
  vertex : V
  todo : List (Option V)

structure State (V : Type u) where
  seen : V → Bool
  stack : List (Frame V)
  finished : List V

def State.active (state : State V) : List V := state.stack.map Frame.vertex
def State.total (state : State V) : List V := state.finished ++ state.active
open State

def initial : State V := ⟨fun _ => false, [], []⟩

/-- 未訪問フラグを立ててから新しいフレームを積む。既訪問なら何もしない。 -/
def discover (outgoing : V → List (Option V)) (state : State V) (vertex : V) : State V :=
  if state.seen vertex then state else
    { state with seen := markSeen state.seen vertex
                 stack := ⟨vertex, outgoing vertex⟩ :: state.stack }

/-- 親のカーソルを一つ進める。子を積む前に実行する。 -/
def trim (state : State V) : State V :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with stack := { frame with todo := frame.todo.tail } :: rest }

/-- 呼出し元tickはtodoが空のときだけ使用する。終了順へ積んでフレームを取り除く。 -/
def retire (state : State V) : State V :=
  match state.stack with
  | [] => state
  | frame :: rest => { state with stack := rest, finished := state.finished ++ [frame.vertex] }

def tick (outgoing : V → List (Option V)) (state : State V) : State V :=
  match state.stack with
  | [] => state
  | frame :: _ =>
    match frame.todo with
    | [] => retire state
    | none :: _ => trim state
    | some child :: _ => discover outgoing (trim state) child

structure Invariant (state : State V) : Prop where
  unique : state.total.Nodup
  covers : ∀ vertex, state.seen vertex = true ↔ vertex ∈ state.total

omit [DecidableEq V] in
theorem initial_invariant : Invariant (initial : State V) := by
  constructor
  · simp [initial, total, active]
  · intro vertex; simp [initial, total, active]

theorem discover_preserves (outgoing : V → List (Option V)) (state : State V)
    (valid : Invariant state) (vertex : V) : Invariant (discover outgoing state vertex) := by
  cases visited : state.seen vertex with
  | true => simpa [discover, visited] using valid
  | false =>
    have fresh : vertex ∉ state.total := by
      intro member
      have seen := (valid.covers vertex).mpr member
      rw [visited] at seen
      cases seen
    have unique := List.nodup_cons.mpr ⟨fresh, valid.unique⟩
    constructor
    · simpa [discover, visited, total, active] using List.perm_middle.nodup_iff.mpr unique
    · intro other
      change (discover outgoing state vertex).seen other = true ↔ _
      simp only [discover, visited, Bool.false_eq_true, ite_false, total, active, List.map_cons]
      rw [markSeen_true_iff, valid.covers other]
      simp only [total, active, List.mem_append, List.mem_cons]
      constructor
      · rintro (rfl | old)
        · exact Or.inr (Or.inl rfl)
        · rcases old with left | right
          · exact Or.inl left
          · exact Or.inr (Or.inr right)
      · rintro (left | same | right)
        · exact Or.inr (Or.inl left)
        · exact Or.inl same
        · exact Or.inr (Or.inr right)

omit [DecidableEq V] in
theorem trim_total (state : State V) : (trim state).total = state.total := by
  cases stack : state.stack <;> simp [trim, stack, total, active]

omit [DecidableEq V] in
theorem retire_total (state : State V) : (retire state).total = state.total := by
  cases stack : state.stack <;> simp [retire, stack, total, active, List.append_assoc]

omit [DecidableEq V] in
theorem trim_seen (state : State V) : (trim state).seen = state.seen := by
  cases stack : state.stack <;> simp [trim, stack]

omit [DecidableEq V] in
theorem retire_seen (state : State V) : (retire state).seen = state.seen := by
  cases stack : state.stack <;> simp [retire, stack]

omit [DecidableEq V] in
theorem trim_preserves (state : State V) (valid : Invariant state) : Invariant (trim state) := by
  constructor
  · rw [trim_total]; exact valid.unique
  · intro vertex; rw [trim_seen, trim_total]; exact valid.covers vertex

omit [DecidableEq V] in
theorem retire_preserves (state : State V) (valid : Invariant state) : Invariant (retire state) := by
  constructor
  · rw [retire_total]; exact valid.unique
  · intro vertex; rw [retire_seen, retire_total]; exact valid.covers vertex

theorem tick_preserves (outgoing : V → List (Option V)) (state : State V)
    (valid : Invariant state) : Invariant (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa [tick, stack] using valid
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa [tick, stack, todo] using retire_preserves state valid
    | cons target remaining =>
      cases target with
      | none => simpa [tick, stack, todo] using trim_preserves state valid
      | some child => simpa [tick, stack, todo] using
          discover_preserves outgoing (trim state) (trim_preserves state valid) child

theorem discover_seen_at (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    (discover outgoing state vertex).seen vertex = true := by
  cases visited : state.seen vertex <;> simp [discover, visited, markSeen]

theorem discover_seen_stable (outgoing : V → List (Option V)) (state : State V)
    (target vertex : V) (seen : state.seen vertex = true) :
    (discover outgoing state target).seen vertex = true := by
  cases visited : state.seen target <;> simp [discover, visited, markSeen_true_iff, seen]

theorem tick_seen_stable (outgoing : V → List (Option V)) (state : State V) (vertex : V)
    (seen : state.seen vertex = true) : (tick outgoing state).seen vertex = true := by
  cases stack : state.stack with
  | nil => simpa [tick, stack] using seen
  | cons frame rest =>
    cases todo : frame.todo with
    | nil => simpa [tick, stack, todo, retire_seen] using seen
    | cons target remaining =>
      cases target with
      | none => simpa [tick, stack, todo, trim_seen] using seen
      | some child => simpa [tick, stack, todo] using
          discover_seen_stable outgoing (trim state) child vertex (by simpa [trim_seen] using seen)

end PetaProof.ForwardDfs
