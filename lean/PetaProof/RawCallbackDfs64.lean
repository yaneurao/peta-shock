import PetaProof.MachineCsrParents64

/-!
CSRの生callback対を順に第二DFSへ適用する。先に親列を生成する処理は仕様との照合用。
pending/resultの更新は既存のUInt32配列を使い、親の元jで許可を判定する。
-/
namespace PetaProof.RawCallbackDfs64

variable {n : Nat}
abbrev State (n : Nat) := ReverseDfsStackArray.State n

def callback (id : Nat) (allow : UInt32 → UInt32 → Bool) (edge : MoveRowsCsr32.Pair) (state : State n) : State n :=
  match VertexStack32.decode n edge.1 with
  | none => state
  | some parent =>
    if ComponentLabels32.get state.result parent = ComponentLabels32.unset then
      if allow edge.1 edge.2 then ReverseDfsStackArray.push id state parent else state
    else state

/-- 割当済みガードを先に調べても、純粋なallowによる親列の選別と同じ更新になる。 -/
theorem callback_as_filter (id : Nat) (allow : UInt32 → UInt32 → Bool) (edge : MoveRowsCsr32.Pair) (state : State n) :
    callback id allow edge state = if allow edge.1 edge.2 then
      match VertexStack32.decode n edge.1 with
      | none => state
      | some parent => ReverseDfsStackArray.push id state parent
    else state := by
  cases decoded : VertexStack32.decode n edge.1 with
  | none => cases permitted : allow edge.1 edge.2 <;> simp [callback, decoded, permitted]
  | some parent =>
    by_cases fresh : ComponentLabels32.get state.result parent = ComponentLabels32.unset
    · cases permitted : allow edge.1 edge.2 <;> simp [callback, decoded, fresh, permitted]
    · cases permitted : allow edge.1 edge.2 <;>
        simp [callback, decoded, fresh, permitted, ReverseDfsStackArray.push_assigned id state parent fresh]

def scan (id : Nat) (allow : UInt32 → UInt32 → Bool) : List MoveRowsCsr32.Pair → State n → State n
  | [], state => state
  | edge :: rest, state => scan id allow rest (callback id allow edge state)

/-- 順序・重複を保った逐次callbackは、許可した親列のscanに状態全体で一致する。 -/
theorem scan_exact (id : Nat) (allow : UInt32 → UInt32 → Bool) (edges : List MoveRowsCsr32.Pair) (state : State n) :
    scan id allow edges state = ReverseDfsStackArray.scan id
      (((edges.filter (fun edge => allow edge.1 edge.2)).map Prod.fst).filterMap (VertexStack32.decode n)) state := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    rw [scan, ih, callback_as_filter]
    cases permitted : allow edge.1 edge.2 <;>
      cases decoded : VertexStack32.decode n edge.1 <;>
      simp [permitted, decoded, ReverseDfsStackArray.scan]

def visit (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id : Nat) (state : State (2 * n)) : State (2 * n) :=
  match ReverseDfsStackArray.top state with
  | none => state
  | some vertex => scan id allow (MachineCsrParents64.callbacks book seed vertex) (ReverseDfsStackArray.pop state)

theorem visit_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id : Nat) (state : State (2 * n)) :
    visit book seed allow id state = ReverseDfsStackArray.visit id (MachineCsrParents64.parents book seed allow) state := by
  cases found : ReverseDfsStackArray.top state with
  | none => simp only [visit, ReverseDfsStackArray.visit, found]
  | some vertex =>
    simp only [visit, ReverseDfsStackArray.visit, found]
    exact scan_exact id allow _ _

def walk (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id : Nat) : Nat → State (2 * n) → State (2 * n)
  | 0, state => state
  | fuel + 1, state => walk book seed allow id fuel (visit book seed allow id state)

theorem walk_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id fuel : Nat) (state : State (2 * n)) :
    walk book seed allow id fuel state = ReverseDfsStackArray.walk id (MachineCsrParents64.parents book seed allow) fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [walk, ih, visit_exact, ReverseDfsStackArray.walk]

def explore (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id : Nat) (previous : Array UInt32) (root : Fin (2 * n)) : State (2 * n) :=
  walk book seed allow id (2 * n) (ReverseDfsStackArray.push id (ReverseDfsStackArray.initial previous) root)

theorem explore_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (id : Nat) (previous : Array UInt32) (root : Fin (2 * n)) :
    explore book seed allow id previous root =
      ReverseDfsStackArray.explore id previous (MachineCsrParents64.parents book seed allow) root :=
  walk_exact book seed allow id (2 * n) _

theorem walk_valid (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id fuel : Nat) (state : State (2 * n))
    (valid : ReverseDfsStackArray.Valid state) : ReverseDfsStackArray.Valid (walk book seed allow id fuel state) := by
  rw [walk_exact]
  exact ReverseDfsStackArray.walk_valid (MachineCsrParents64.word_capacity fits) id _ fuel state valid

theorem explore_valid (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id : Nat) (previous : Array UInt32) (root : Fin (2 * n)) :
    ReverseDfsStackArray.Valid (explore book seed allow id previous root) := by
  rw [explore_exact]
  exact ReverseDfsStackArray.explore_valid (MachineCsrParents64.word_capacity fits) id previous _ root

/-- callbackとpopは番号表の長さを変えないため、開始時の読取り範囲を途中状態へ引き継げる。 -/
theorem walk_result_size (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id fuel : Nat) (state : State (2 * n))
    (valid : ReverseDfsStackArray.Valid state) :
    (walk book seed allow id fuel state).result.size = state.result.size := by
  rw [walk_exact]
  have same := congrArg (fun state : ReverseDfsResultArray.State (2 * n) => state.result.size)
    (ReverseDfsStackArray.walk_refines (MachineCsrParents64.word_capacity fits) id
      (MachineCsrParents64.parents book seed allow) fuel state valid)
  change (ReverseDfsStackArray.walk id _ fuel state).result.size = _ at same
  dsimp only at same
  rw [ReverseDfsResultArray.walk_size] at same
  exact same

theorem explore_result_size (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id : Nat) (previous : Array UInt32) (root : Fin (2 * n)) :
    (explore book seed allow id previous root).result.size = previous.size := by
  rw [explore_exact]
  have same := congrArg (fun state : ReverseDfsResultArray.State (2 * n) => state.result.size)
    (ReverseDfsStackArray.explore_refines (MachineCsrParents64.word_capacity fits) id previous
      (MachineCsrParents64.parents book seed allow) root)
  change (ReverseDfsStackArray.explore id previous _ root).result.size = _ at same
  dsimp only at same
  rw [ReverseDfsResultArray.explore_size] at same
  exact same

theorem walk_stack_bound (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (fuel : Nat) (state : State (2 * n)) (valid : ReverseDfsStackArray.Valid state)
    (size : state.result.size = 2 * n)
    (invariant : ReverseDfsStack.Invariant id (ReverseDfsResultArray.unpack (ReverseDfsStackArray.unpack state))) :
    (walk book seed allow id fuel state).pending.size ≤ 2 * n := by
  rw [walk_exact]
  exact ReverseDfsStackArray.walk_stack_bound (MachineCsrParents64.word_capacity fits) id bounded _ fuel state valid size invariant

theorem explore_drains (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (id : Nat) (bounded : id < ComponentLabels32.unset.toNat)
    (previous : Array UInt32) (size : previous.size = 2 * n) (root : Fin (2 * n))
    (unused : ∀ vertex : Fin (2 * n), ComponentLabels32.model previous vertex ≠ some id)
    (fresh : ComponentLabels32.model previous root = none) :
    (explore book seed allow id previous root).pending.size = 0 := by
  rw [explore_exact]
  exact ReverseDfsStackArray.explore_drains (MachineCsrParents64.word_capacity fits) id bounded previous size _ root unused fresh

end PetaProof.RawCallbackDfs64
