import PetaProof.SelectedDepthDiscovery

/-! 有限局面一覧に沿う「探索・巻き戻し・確定」の全走査。
関数表とリストは数学的参照モデルであり、C++の配列やhashの実行時間は主張しない。 -/
namespace PetaProof.SelectedDepth

universe u
variable {V : Type u} [DecidableEq V]

structure State (V : Type u) where
  table : V → Nat
  done : V → Bool

def initial (cap : Nat) : State V := ⟨fun _ => cap, fun _ => false⟩

def Invariant (next : V → Option V) (cap : Nat) (state : State V) : Prop :=
  (∀ x, state.done x = true → state.table x = computed next cap x) ∧
  (∀ x, state.done x ≠ true → state.table x = cap)

def visit (next : V → Option V) (cap fuel : Nat) (state : State V) (root : V) : Option (State V) :=
  if state.done root = true then some state else
  match discover next state.done fuel root [] with
  | none => none
  | some stack => some {
      table := unwind next cap stack state.table
      done := fun x => state.done x || decide (x ∈ stack)
    }

def scan (next : V → Option V) (cap fuel : Nat) : List V → State V → Option (State V)
  | [], state => some state
  | root :: rest, state => (visit next cap fuel state root).bind (scan next cap fuel rest)

omit [DecidableEq V] in
theorem initial_invariant (next : V → Option V) (cap : Nat) : Invariant next cap (initial (V := V) cap) := by
  constructor
  · intro x impossible; simp [initial] at impossible
  · intro x _; rfl

/-- N+1を与えた各visitは失敗せず、rootを確定し、以前の確定済み局面を保つ。 -/
theorem visit_total_correct (next : V → Option V) (cap : Nat) (vertices : List V)
    (covered : ∀ x, x ∈ vertices) (state : State V) (valid : Invariant next cap state) (root : V) :
    ∃ after, visit next cap (vertices.length + 1) state root = some after ∧
      Invariant next cap after ∧ after.done root = true ∧
      (∀ x, state.done x = true → after.done x = true) := by
  by_cases already : state.done root = true
  · exact ⟨state, by simp [visit, already], valid, already, fun _ h => h⟩
  · obtain ⟨stack, found⟩ := discover_exists next state.done vertices covered
      (vertices.length + 1) root [] (by simp) (by simp; omega)
    have afterCorrect := discovered_sweep_correct next cap state.done state.table
      (vertices.length + 1) root stack valid.1 valid.2 found
    let after : State V := {
      table := unwind next cap stack state.table
      done := fun x => state.done x || decide (x ∈ stack)
    }
    refine ⟨after, by simp [visit, already, found, after], ?_, ?_, ?_⟩
    · constructor
      · intro x done
        exact afterCorrect.1 x (by simpa [after] using done)
      · intro x outside
        exact afterCorrect.2.1 x (by simpa [after] using outside)
    · simp [after, afterCorrect.2.2]
    · intro x done
      simp [after, done]

/-- 外側の全走査も停止し、訪問したrootは全て確定済みになる。 -/
theorem scan_total_correct (next : V → Option V) (cap : Nat) (vertices : List V)
    (covered : ∀ x, x ∈ vertices) (roots : List V) (state : State V)
    (valid : Invariant next cap state) :
    ∃ after, scan next cap (vertices.length + 1) roots state = some after ∧
      Invariant next cap after ∧ (∀ x ∈ roots, after.done x = true) ∧
      (∀ x, state.done x = true → after.done x = true) := by
  induction roots generalizing state with
  | nil => exact ⟨state, rfl, valid, by simp, fun _ h => h⟩
  | cons root rest ih =>
    obtain ⟨middle, visited, middleValid, rootDone, kept⟩ :=
      visit_total_correct next cap vertices covered state valid root
    obtain ⟨after, scanned, afterValid, tailDone, tailKept⟩ := ih middle middleValid
    refine ⟨after, ?_, afterValid, ?_, ?_⟩
    · simp only [scan, visited, Option.bind_some]
      exact scanned
    · intro x member
      rcases List.mem_cons.mp member with same | tail
      · subst x; exact tailKept root rootDone
      · exact tailDone x tail
    · exact fun x old => tailKept x (kept x old)

def reconstruct (next : V → Option V) (cap : Nat) (vertices : List V) : Option (V → Nat) :=
  (scan next cap (vertices.length + 1) vertices (initial cap)).map State.table

/-- 正しい表を入力せず、初期値capからの全走査の出力が参照距離と完全に一致する。 -/
theorem reconstruct_exact (next : V → Option V) (cap : Nat) (vertices : List V)
    (covered : ∀ x, x ∈ vertices) :
    reconstruct next cap vertices = some (computed next cap) := by
  obtain ⟨after, scanned, valid, allDone, _⟩ := scan_total_correct next cap vertices covered
    vertices (initial cap) (initial_invariant next cap)
  have tableExact : after.table = computed next cap := by
    funext x
    exact valid.1 x (allDone x (covered x))
  simp only [reconstruct, scanned, Option.map, tableExact]

theorem reconstructed_equation (next : V → Option V) (cap : Nat) (vertices : List V)
    (covered : ∀ x, x ∈ vertices) (table : V → Nat)
    (found : reconstruct next cap vertices = some table) (vertex : V) :
    table vertex = match next vertex with
      | none => 0
      | some child => bump cap (table child) := by
  have exactRun := reconstruct_exact next cap vertices covered
  rw [found] at exactRun
  have same : table = computed next cap := Option.some.inj exactRun
  rw [same]
  exact equation next cap vertex

theorem reconstructed_bounds (next : V → Option V) (cap : Nat) (vertices : List V)
    (covered : ∀ x, x ∈ vertices) (table : V → Nat)
    (found : reconstruct next cap vertices = some table) (vertex : V) : table vertex ≤ cap := by
  have exactRun := reconstruct_exact next cap vertices covered
  rw [found] at exactRun
  have same : table = computed next cap := Option.some.inj exactRun
  rw [same]
  exact bounded next cap vertex

theorem order_independent (next : V → Option V) (cap : Nat) (first second : List V)
    (firstCovers : ∀ x, x ∈ first) (secondCovers : ∀ x, x ∈ second) :
    reconstruct next cap first = reconstruct next cap second := by
  rw [reconstruct_exact next cap first firstCovers, reconstruct_exact next cap second secondCovers]

end PetaProof.SelectedDepth
