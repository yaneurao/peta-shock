import PetaProof.SelectedDepth

/-! 選択経路を逆順にpopしてdepth表へ書き込む操作の不変条件。
探索済みの子、leaf、または飽和が証明された循環の入口を種として用いる。 -/
namespace PetaProof.SelectedDepth

universe u
variable {V : Type u} [DecidableEq V]

def write (next : V → Option V) (cap : Nat) (table : V → Nat) (vertex : V) : V → Nat :=
  fun x => if x = vertex then match next vertex with
    | none => 0
    | some child => bump cap (table child)
  else table x

/-- stackはC++のpop順、すなわち発見した経路の逆順。 -/
def unwind (next : V → Option V) (cap : Nat) : List V → (V → Nat) → V → Nat
  | [], table => table
  | vertex :: rest, table => unwind next cap rest (write next cap table vertex)

/-- 各pop時点で、子は既に値を利用できる集合に入っている。leafなら条件は空。 -/
def Ready (next : V → Option V) : List V → (V → Prop) → Prop
  | [], _ => True
  | vertex :: rest, known =>
    (∀ child, next vertex = some child → known child) ∧
      Ready next rest (fun x => x = vertex ∨ known x)

/-- 逆順の経路上では、一つ古い局面の選択手が直前の局面を指す。 -/
def Linked (next : V → Option V) : List V → Prop
  | [] => True
  | [_] => True
  | child :: parent :: rest => next parent = some child ∧ Linked next (parent :: rest)

omit [DecidableEq V] in
theorem ready_of_linked (next : V → Option V) (head : V) (rest : List V)
    (known : V → Prop) (linked : Linked next (head :: rest))
    (first : ∀ child, next head = some child → known child) :
    Ready next (head :: rest) known := by
  induction rest generalizing head known with
  | nil => exact ⟨first, trivial⟩
  | cons parent rest ih =>
    refine ⟨first, ih parent (fun x => x = head ∨ known x) linked.2 ?_⟩
    intro child step
    have same : child = head := Option.some.inj (step.symm.trans linked.1)
    exact Or.inl same

omit [DecidableEq V] in
theorem linked_reaches_head (next : V → Option V) (head : V) (rest : List V)
    (linked : Linked next (head :: rest)) (x : V) (member : x ∈ head :: rest) :
    Nonempty (Walk (fun a b => next a = some b) x head) := by
  induction rest generalizing head with
  | nil =>
    have same : x = head := by simpa using member
    subst x
    exact ⟨.nil head⟩
  | cons parent rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst x; exact ⟨.nil head⟩
    · obtain ⟨path⟩ := ih parent linked.2 tail
      exact ⟨path.append (.cons linked.1 (.nil head))⟩

omit [DecidableEq V] in
/-- 経路中の局面へ戻るとき、その経路全体の正しいdepthはcapである。 -/
theorem cycle_stack_saturated (next : V → Option V) (cap : Nat) (head : V) (rest : List V)
    (linked : Linked next (head :: rest)) (target : V)
    (step : next head = some target) (repeated : target ∈ head :: rest) :
    ∀ x ∈ head :: rest, computed next cap x = cap := by
  obtain ⟨back⟩ := linked_reaches_head next head rest linked target repeated
  have saturated := cycle_saturated next cap step back
  intro x member
  obtain ⟨path⟩ := linked_reaches_head next head rest linked x member
  exact reaches_saturated next cap path saturated

theorem write_correct (next : V → Option V) (cap : Nat) (table : V → Nat) (vertex : V)
    (children : ∀ child, next vertex = some child → table child = computed next cap child) :
    write next cap table vertex vertex = computed next cap vertex := by
  rw [equation next cap vertex]
  cases step : next vertex with
  | none => simp [write, step]
  | some child => simp [write, step, children child step]

theorem write_preserves (next : V → Option V) (cap : Nat) (table : V → Nat)
    (vertex : V) (known : V → Prop)
    (correct : ∀ x, known x → table x = computed next cap x)
    (ready : ∀ child, next vertex = some child → known child) :
    ∀ x, x = vertex ∨ known x → write next cap table vertex x = computed next cap x := by
  intro x included
  by_cases same : x = vertex
  · subst x
    exact write_correct next cap table vertex (fun child step => correct child (ready child step))
  · have before : known x := included.resolve_left same
    simpa [write, same] using correct x before

/-- 経路の巻き戻しは、元の確定局面と全pop局面の正しいdepthを保つ。 -/
theorem unwind_correct (next : V → Option V) (cap : Nat) (stack : List V)
    (table : V → Nat) (known : V → Prop)
    (correct : ∀ x, known x → table x = computed next cap x)
    (ready : Ready next stack known) :
    ∀ x, x ∈ stack ∨ known x → unwind next cap stack table x = computed next cap x := by
  induction stack generalizing table known with
  | nil =>
    intro x included
    exact correct x (by simpa using included)
  | cons vertex rest ih =>
    have after := write_preserves next cap table vertex known correct ready.1
    have tail := ih (write next cap table vertex) (fun x => x = vertex ∨ known x) after ready.2
    intro x included
    apply tail x
    rcases included with member | old
    · rcases List.mem_cons.mp member with head | rest
      · exact Or.inr (Or.inl head)
      · exact Or.inl rest
    · exact Or.inr (Or.inr old)

/-- popしなかった局面は変更しない。未訪問局面の初期値capを維持できる。 -/
theorem unwind_untouched (next : V → Option V) (cap : Nat) (stack : List V)
    (table : V → Nat) (x : V) (outside : x ∉ stack) : unwind next cap stack table x = table x := by
  induction stack generalizing table with
  | nil => rfl
  | cons vertex rest ih =>
    have notHead : x ≠ vertex := by intro same; exact outside (by simp [same])
    have notTail : x ∉ rest := fun h => outside (by simp [h])
    rw [unwind, ih _ notTail]
    simp [write, notHead]

omit [DecidableEq V] in
/-- 確定局面と、循環に属して初期値capが残る入口を種としてまとめる。 -/
theorem cycle_seed (next : V → Option V) (cap : Nat) (table : V → Nat)
    (done anchor : V → Prop)
    (settled : ∀ x, done x → table x = computed next cap x)
    (untouched : ∀ x, ¬ done x → table x = cap)
    (cycle : ∀ x, anchor x → computed next cap x = cap) :
    ∀ x, done x ∨ anchor x → table x = computed next cap x := by
  intro x included
  by_cases old : done x
  · exact settled x old
  · have target : anchor x := included.resolve_left old
    rw [untouched x old, cycle x target]

/-- 一回の探索経路の巻き戻しを、確定済み/未訪問の表の不変条件へ接続する。 -/
theorem sweep_preserves (next : V → Option V) (cap : Nat) (table : V → Nat)
    (done anchor : V → Prop) (stack : List V)
    (settled : ∀ x, done x → table x = computed next cap x)
    (untouched : ∀ x, ¬ done x → table x = cap)
    (cycle : ∀ x, anchor x → computed next cap x = cap)
    (ready : Ready next stack (fun x => done x ∨ anchor x)) :
    (∀ x, done x ∨ x ∈ stack → unwind next cap stack table x = computed next cap x) ∧
    (∀ x, ¬ (done x ∨ x ∈ stack) → unwind next cap stack table x = cap) := by
  have seeds := cycle_seed next cap table done anchor settled untouched cycle
  have after := unwind_correct next cap stack table (fun x => done x ∨ anchor x) seeds ready
  constructor
  · intro x included
    apply after x
    rcases included with old | member
    · exact Or.inr (Or.inl old)
    · exact Or.inl member
  · intro x outside
    rw [unwind_untouched next cap stack table x (fun h => outside (Or.inr h))]
    exact untouched x (fun h => outside (Or.inl h))

/-- leaf・確定済み局面・現在の経路への再訪という三つの停止理由を全て扱う。
循環入口の正しいdepthは追加の仮定にせず、経路の戻りから導く。 -/
theorem path_sweep_correct (next : V → Option V) (cap : Nat) (table : V → Nat)
    (done : V → Prop) (head : V) (rest : List V)
    (linked : Linked next (head :: rest))
    (settled : ∀ x, done x → table x = computed next cap x)
    (untouched : ∀ x, ¬ done x → table x = cap)
    (stopped : ∀ child, next head = some child → done child ∨ child ∈ head :: rest) :
    (∀ x, done x ∨ x ∈ head :: rest →
      unwind next cap (head :: rest) table x = computed next cap x) ∧
    (∀ x, ¬ (done x ∨ x ∈ head :: rest) → unwind next cap (head :: rest) table x = cap) := by
  cases step : next head with
  | none =>
    apply sweep_preserves next cap table done (fun _ => False) (head :: rest)
      settled untouched (by intro _ impossible; exact False.elim impossible)
    apply ready_of_linked next head rest _ linked
    intro child edge
    simp [step] at edge
  | some child =>
    rcases stopped child step with old | repeated
    · apply sweep_preserves next cap table done (fun _ => False) (head :: rest)
        settled untouched (by intro _ impossible; exact False.elim impossible)
      apply ready_of_linked next head rest _ linked
      intro target edge
      have same : target = child := Option.some.inj (edge.symm.trans step)
      exact Or.inl (same ▸ old)
    · have saturated := cycle_stack_saturated next cap head rest linked child step repeated
      apply sweep_preserves next cap table done (fun x => x = child) (head :: rest) settled untouched
      · intro x same
        exact saturated x (same ▸ repeated)
      · apply ready_of_linked next head rest _ linked
        intro target edge
        exact Or.inr (Option.some.inj (edge.symm.trans step))

end PetaProof.SelectedDepth
