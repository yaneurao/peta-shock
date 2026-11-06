import PetaProof.SccIndexedView

/-!
逆辺callbackの逐次処理と、第二DFSの自己ループフラグ。
自己ループ判定はpushのガードの外に置く。poppedは既存の証明用履歴である。
-/
namespace PetaProof.SccParentCallback

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]
open SccIndexedView

abbrev State (V : Type u) := ReverseDfsStack.State V × Bool

def callback (id : Nat) (view : View V E) (allow : E → Bool) (vertex : V) (edge : E)
    (state : State V) : State V :=
  (if state.1.result (view.source edge) = none ∧ allow edge = true then
      ReverseDfsStack.push id state.1 (view.source edge) else state.1,
   state.2 || (decide (view.source edge = vertex) && allow edge))

def scan (id : Nat) (view : View V E) (allow : E → Bool) (vertex : V) : List E → State V → State V
  | [], state => state
  | edge :: rest, state => scan id view allow vertex rest (callback id view allow vertex edge state)

theorem callback_graph (id : Nat) (view : View V E) (allow : E → Bool) (vertex : V) (edge : E)
    (state : State V) :
    (callback id view allow vertex edge state).1 =
      if allow edge then ReverseDfsStack.push id state.1 (view.source edge) else state.1 := by
  cases permitted : allow edge <;> cases found : state.1.result (view.source edge) <;>
    simp [callback, ReverseDfsStack.push, permitted, found]

/-- 辺IDごとの逐次callbackの訪問結果は、allow済み親ID列の既存scanと一致する。 -/
theorem scan_graph (id : Nat) (view : View V E) (allow : E → Bool) (vertex : V)
    (edges : List E) (state : State V) :
    (scan id view allow vertex edges state).1 =
      ReverseDfsStack.scan id ((edges.filter allow).map view.source) state.1 := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    rw [scan, ih, callback_graph]
    cases permitted : allow edge <;> simp [permitted, ReverseDfsStack.scan]

theorem scan_flag (id : Nat) (view : View V E) (allow : E → Bool) (vertex : V)
    (edges : List E) (state : State V) :
    (scan id view allow vertex edges state).2 =
      (state.2 || edges.any (fun edge => decide (view.source edge = vertex) && allow edge)) := by
  induction edges generalizing state with
  | nil => simp [scan]
  | cons edge rest ih =>
    rw [scan, ih]
    simp [callback, List.any_cons, Bool.or_assoc]

def visit (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool) (state : State V) : State V :=
  match state.1.pending with
  | [] => state
  | vertex :: _ => scan id view allow vertex (incoming view vertices vertex) (ReverseDfsStack.pop state.1, state.2)

def walk (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool) : Nat → State V → State V
  | 0, state => state
  | fuel + 1, state => walk id view vertices allow fuel (visit id view vertices allow state)

theorem visit_graph (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool) (state : State V) :
    (visit id view vertices allow state).1 = ReverseDfsStack.visit id (parents view vertices allow) state.1 := by
  cases pending : state.1.pending with
  | nil => simp [visit, ReverseDfsStack.visit, pending]
  | cons vertex rest =>
    simp only [visit, ReverseDfsStack.visit, pending]
    exact scan_graph id view allow vertex _ _

theorem walk_graph (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool)
    (fuel : Nat) (state : State V) :
    (walk id view vertices allow fuel state).1 = ReverseDfsStack.walk id (parents view vertices allow) fuel state.1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [walk, ih, visit_graph, ReverseDfsStack.walk]

/-- 一回のpopと全callbackを終えた境界で、フラグはpop済み頂点の自己辺のORである。 -/
theorem visit_flag (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool) (state : State V)
    (valid : state.2 = state.1.popped.any (selfLoop view vertices allow)) :
    (visit id view vertices allow state).2 =
      (visit id view vertices allow state).1.popped.any (selfLoop view vertices allow) := by
  cases pending : state.1.pending with
  | nil => simpa [visit, pending] using valid
  | cons vertex rest =>
    simp only [visit, pending]
    rw [scan_flag, scan_graph, ReverseDfsStack.scan_popped]
    simp [ReverseDfsStack.pop, pending, List.any_append, valid, selfLoop]

theorem walk_flag (id : Nat) (view : View V E) (vertices : List V) (allow : E → Bool)
    (fuel : Nat) (state : State V) (valid : state.2 = state.1.popped.any (selfLoop view vertices allow)) :
    (walk id view vertices allow fuel state).2 =
      (walk id view vertices allow fuel state).1.popped.any (selfLoop view vertices allow) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih _ (visit_flag id view vertices allow state valid)

def explore (view : View V E) (vertices : List V) (allow : E → Bool) (previous : V → Option Nat)
    (id : Nat) (root : V) : State V :=
  walk id view vertices allow vertices.length
    (ReverseDfsStack.push id (ReverseDfsStack.initial previous) root, false)

theorem explore_graph (view : View V E) (vertices : List V) (allow : E → Bool) (previous : V → Option Nat)
    (id : Nat) (root : V) :
    (explore view vertices allow previous id root).1 =
      ReverseDfsStack.explore vertices id previous (parents view vertices allow) root :=
  walk_graph id view vertices allow vertices.length _

theorem explore_flag (view : View V E) (vertices : List V) (allow : E → Bool) (previous : V → Option Nat)
    (id : Nat) (root : V) :
    (explore view vertices allow previous id root).2 =
      (explore view vertices allow previous id root).1.popped.any (selfLoop view vertices allow) := by
  apply walk_flag
  cases found : previous root <;> simp [ReverseDfsStack.push, ReverseDfsStack.initial, found]

/-- 終了時の自己ループフラグを、新規番号を持つ頂点の自己辺の存在へ接続する。 -/
theorem explore_flag_exact (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool) (previous : V → Option Nat)
    (id : Nat) (unused : ∀ vertex, previous vertex ≠ some id) (root : V) (fresh : previous root = none) :
    (explore view vertices allow previous id root).2 = true ↔
      ∃ vertex, (explore view vertices allow previous id root).1.result vertex = some id ∧
        ForwardDfs.Edge (outgoing view allow) vertex vertex := by
  rw [explore_flag, List.any_eq_true]
  have graph := explore_graph view vertices allow previous id root
  have valid := ReverseDfsStack.explore_valid vertices id previous (parents view vertices allow) root unused fresh
  have empty := ReverseDfsStack.explore_drains vertices unique covered id previous (parents view vertices allow) root unused fresh
  have members := ReverseDfsStack.drained_members id _ valid.base empty
  simp only [graph, ← members, selfLoop_correct view vertices covered]

/-- 実際のcountと逐次更新したself_loopから、その根が循環上にあることを判定する。 -/
theorem descend_cycle_iff (view : View V E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (allow : E → Bool)
    (last : ForwardDfs.State V) (run : ForwardDfs.Timeline (outgoing view allow) ForwardDfs.initial last)
    (empty_first : last.stack = []) (listed : ∀ vertex, vertex ∈ last.finished)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state)
    (whole : KosarajuStep.Saturated (outgoing view allow) state.result)
    (root : V) (fresh : state.result root = none)
    (highest : KosarajuStep.Highest last.finished state.result root) :
    let report := explore view vertices allow state.result state.roots.length root
    (decide (1 < report.1.count) || report.2) = true ↔
      CyclicVertex (ForwardDfs.Edge (outgoing view allow)) root := by
  let report := explore view vertices allow state.result state.roots.length root
  have graph : report.1 = ComponentNumbering.descend vertices.length (parents view vertices allow) state root :=
    explore_graph view vertices allow state.result state.roots.length root
  have exact_component : ∀ vertex, report.1.result vertex = some state.roots.length ↔
      ForwardDfs.Mutual (outgoing view allow) root vertex := by
    rw [graph]
    exact KosarajuStep.descend_one_component vertices unique covered _ _
      (parents_transpose view vertices covered allow) last run empty_first listed state valid whole root fresh highest
  have assigned := (exact_component root).mpr ⟨⟨.nil root⟩, ⟨.nil root⟩⟩
  have report_valid : ReverseDfsStack.Invariant state.roots.length report.1 := by
    rw [graph]
    exact ComponentNumbering.descend_invariant _ _ state valid root
  have drained : report.1.pending = [] := by
    rw [graph]
    exact ComponentNumbering.descend_drains vertices unique covered _ state valid root
  have multiple := ReverseDfsStack.drained_multiple_iff vertices unique covered state.roots.length _ report_valid drained root assigned
  have unused : ∀ vertex, state.result vertex ≠ some state.roots.length := by
    intro vertex found
    have impossible := valid.bounded vertex state.roots.length found
    omega
  have flag := explore_flag_exact view vertices unique covered allow state.result state.roots.length unused root fresh
  change (decide (1 < report.1.count) || report.2) = true ↔ _
  rw [Bool.or_eq_true, decide_eq_true_eq, multiple, flag]
  change (∃ other, other ≠ root ∧ report.1.result other = some state.roots.length) ∨
    (∃ vertex, report.1.result vertex = some state.roots.length ∧
      ForwardDfs.Edge (outgoing view allow) vertex vertex) ↔ _
  simp only [exact_component]
  have closes (other : V) (different : other ≠ root)
      (same : ForwardDfs.Mutual (outgoing view allow) root other) :
      CyclicVertex (ForwardDfs.Edge (outgoing view allow)) root := by
    obtain ⟨forward⟩ := same.1
    obtain ⟨back⟩ := same.2
    cases forward with
    | nil => exact False.elim (different rfl)
    | cons edge tail => exact ⟨_, edge, ⟨tail.append back⟩⟩
  constructor
  · rintro (⟨other, different, same⟩ | ⟨vertex, same, self⟩)
    · exact closes other different same
    · by_cases equal : vertex = root
      · subst vertex; exact ⟨root, self, ⟨.nil root⟩⟩
      · exact closes vertex equal same
  · rintro ⟨child, edge, back⟩
    by_cases equal : child = root
    · subst child
      exact Or.inr ⟨root, ⟨⟨.nil root⟩, ⟨.nil root⟩⟩, edge⟩
    · exact Or.inl ⟨child, equal, ⟨⟨.cons edge (.nil child)⟩, back⟩⟩

end PetaProof.SccParentCallback
