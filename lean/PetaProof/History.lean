import PetaProof.Certificate

/-!
有限局面集合における反復の回数上界。
盤面の有限性そのものや実装の停止性は証明せず、与えられた有限列挙と訪問列の回数から証明する。
-/

namespace PetaProof

universe u
variable {V : Type u} [DecidableEq V]

/-- 列挙した各頂点について履歴内の出現数を足す。列挙に重複があっても使える。 -/
def totalVisits (vertices : List V) (history : List V) : Nat :=
  match vertices with
  | [] => 0
  | v :: rest => history.count v + totalVisits rest history

theorem totalVisits_cons (vertices : List V) (v : V) (history : List V) :
    totalVisits vertices (v :: history) = totalVisits vertices history + vertices.count v := by
  induction vertices with
  | nil => simp [totalVisits]
  | cons x rest ih =>
    by_cases same : x = v
    · subst x
      simp [totalVisits, ih]
      omega
    · have reverse : v ≠ x := Ne.symm same
      simp [totalVisits, List.count_cons, same, reverse, ih, Nat.add_assoc]

/-- 全ての訪問先が列挙内にあれば、訪問数の合計は履歴長以上。 -/
theorem length_le_totalVisits (vertices : List V) (history : List V)
    (covered : ∀ v ∈ history, v ∈ vertices) : history.length ≤ totalVisits vertices history := by
  induction history with
  | nil =>
    induction vertices <;> simp_all [totalVisits]
  | cons v rest ih =>
    have tail := ih (by intro x hx; exact covered x (by simp [hx]))
    have positive : 0 < vertices.count v := List.count_pos_iff.mpr (covered v (by simp))
    rw [totalVisits_cons]
    simp only [List.length_cons]
    omega

theorem totalVisits_le (vertices : List V) (history : List V) (cap : Nat)
    (bounded : ∀ v ∈ vertices, history.count v ≤ cap) :
    totalVisits vertices history ≤ vertices.length * cap := by
  induction vertices with
  | nil => simp [totalVisits]
  | cons v rest ih =>
    have head := bounded v (by simp)
    have tail := ih (by intro x hx; exact bounded x (by simp [hx]))
    simp only [totalVisits, List.length_cons]
    rw [Nat.add_mul]
    omega

/-- k回目の出現がまだなければ、履歴長は局面数*(k-1)以下。 -/
theorem history_length_bound (vertices : List V) (history : List V) (k : Nat)
    (covered : ∀ v ∈ history, v ∈ vertices)
    (not_repeated : ∀ v ∈ vertices, history.count v < k) :
    history.length ≤ vertices.length * (k - 1) := by
  apply Nat.le_trans (length_le_totalVisits vertices history covered)
  exact totalVisits_le vertices history (k - 1) (by
    intro v hv
    have := not_repeated v hv
    omega)

/-- 上界を1つ超えた履歴には、k回以上出現した局面が必ずある。 -/
theorem repetition_exists (vertices : List V) (history : List V) (k : Nat)
    (covered : ∀ v ∈ history, v ∈ vertices)
    (long : vertices.length * (k - 1) < history.length) :
    ∃ v ∈ vertices, k ≤ history.count v := by
  classical
  apply Classical.byContradiction
  intro none
  have bounded : ∀ v ∈ vertices, history.count v < k := by
    intro v hv
    apply Classical.byContradiction
    intro high
    exact none ⟨v, hv, by omega⟩
  have := history_length_bound vertices history k covered bounded
  omega

/-- 四回出現なら、3N+1回の局面訪問までに必ず条件を満たす。 -/
theorem fourfold_exists (vertices : List V) (history : List V)
    (covered : ∀ v ∈ history, v ∈ vertices)
    (long : 3 * vertices.length < history.length) :
    ∃ v ∈ vertices, 4 ≤ history.count v := by
  apply repetition_exists vertices history 4 covered
  simpa [Nat.mul_comm] using long

namespace Walk

variable {R : V → V → Prop}

/-- 始点と終点を含む実際の訪問列。途中の重複もそのまま保持する。 -/
def visits : {a b : V} → Walk R a b → List V
  | a, _, .nil _ => [a]
  | a, _, .cons _ tail => a :: visits tail

def steps : {a b : V} → Walk R a b → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => steps tail + 1

omit [DecidableEq V] in
theorem visits_length {a b : V} (h : Walk R a b) : h.visits.length = h.steps + 1 := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [visits, steps, ih]

/-- 歩道を連結すると中継点だけが二重に数えられる。 -/
theorem visits_count_append {a b c : V} (left : Walk R a b) (right : Walk R b c)
    (v : V) :
    (left.append right).visits.count v + (if b = v then 1 else 0) =
      left.visits.count v + right.visits.count v := by
  induction left with
  | nil => simp [append, visits, List.count_cons, Nat.add_comm]
  | @cons a middle _ e tail ih =>
    have tailCount := ih right
    by_cases same : a = v
    · subst a
      simp only [append, visits, List.count_cons_self]
      omega
    · simp only [append, visits, List.count_cons_of_ne same]
      exact tailCount

/-- k回目の訪問で、元の歩道を正確に分割する。証拠の再構成等式も残す。 -/
theorem split_kth_visit {a b : V} (h : Walk R a b) (v : V) (k : Nat)
    (positive : 0 < k) (many : k ≤ h.visits.count v) :
    ∃ (left : Walk R a v) (right : Walk R v b),
      h = left.append right ∧ left.visits.count v = k := by
  induction h generalizing k with
  | nil a =>
    by_cases same : a = v
    · subst a
      have one : k = 1 := by simp [visits] at many; omega
      subst k
      exact ⟨.nil v, .nil v, rfl, by simp [visits]⟩
    · simp [visits, List.count_cons_of_ne same] at many
      omega
  | @cons a b c e tail ih =>
    by_cases same : a = v
    · subst a
      by_cases first : k = 1
      · subst k
        exact ⟨.nil v, .cons e tail, rfl, by simp [visits]⟩
      · have kpos : 0 < k - 1 := by omega
        have enough : k - 1 ≤ tail.visits.count v := by
          simp only [visits, List.count_cons_self] at many
          omega
        obtain ⟨left, right, original, count⟩ := ih (k - 1) kpos enough
        refine ⟨.cons e left, right, ?_, ?_⟩
        · simp only [append]
          rw [← original]
        · simp only [visits, List.count_cons_self, count]
          omega
    · have enough : k ≤ tail.visits.count v := by
        simpa only [visits, List.count_cons_of_ne same] using many
      obtain ⟨left, right, original, count⟩ := ih k positive enough
      refine ⟨.cons e left, right, ?_, ?_⟩
      · simp only [append]
        rw [← original]
      · simpa only [visits, List.count_cons_of_ne same] using count

/-- 四回目までの実際の手順から、最初から四回目までの非空反復区間を切り出す。 -/
theorem fourfold_interval {a b : V} (h : Walk R a b) (v : V)
    (many : 4 ≤ h.visits.count v) :
    ∃ (stem : Walk R a v) (next : V) (edge : R v next)
      (back : Walk R next v) (suffix : Walk R v b),
      h = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 := by
  obtain ⟨toFourth, suffix, original, four⟩ := h.split_kth_visit v 4 (by decide) many
  obtain ⟨stem, loop, middle, one⟩ := toFourth.split_kth_visit v 1 (by decide) (by omega)
  have counts := visits_count_append stem loop v
  rw [← middle] at counts
  have loopFour : loop.visits.count v = 4 := by
    rw [four, one] at counts
    simp at counts
    omega
  cases loop with
  | nil => simp [visits] at loopFour
  | cons edge back =>
    refine ⟨stem, _, edge, back, suffix, ?_, one, loopFour⟩
    rw [original, middle]

/-- N局面なら、3N手進んだ歩道には実際の四回出現区間がある。 -/
theorem fourfold_on_long_walk {a b : V} (vertices : List V) (h : Walk R a b)
    (covered : ∀ v ∈ h.visits, v ∈ vertices)
    (long : 3 * vertices.length ≤ h.steps) :
    ∃ v, ∃ (stem : Walk R a v) (next : V) (edge : R v next)
      (back : Walk R next v) (suffix : Walk R v b),
      h = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 := by
  obtain ⟨v, _, repeated⟩ := fourfold_exists vertices h.visits covered (by
    have := h.visits_length
    omega)
  exact ⟨v, h.fourfold_interval v repeated⟩

/-- 四回出現で止める限り、内部手を3N手以上指し続ける未終局の歩道はない。 -/
theorem steps_before_fourfold {a b : V} (vertices : List V) (h : Walk R a b)
    (covered : ∀ v ∈ h.visits, v ∈ vertices)
    (not_repeated : ∀ v ∈ vertices, h.visits.count v < 4) :
    h.steps < 3 * vertices.length := by
  have limit := history_length_bound vertices h.visits 4 covered not_repeated
  have length := h.visits_length
  simp only [Nat.reduceSub] at limit
  omega

end Walk

namespace Certificate

/-- rootからの実際の歩道で四回出現を検出した場合、その終局区間も下限保証を満たす。 -/
theorem fourfold_from_walk (C : Certificate V) {a b : V} (h : Walk C.edge a b)
    (v : V) (many : 4 ≤ h.visits.count v) :
    ∃ (stem : Walk C.edge a v) (next : V) (edge : C.edge v next)
      (back : Walk C.edge next v) (suffix : Walk C.edge v b),
      h = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 ∧
      C.value a ≤ C.repetitionPayoff edge back := by
  obtain ⟨stem, next, edge, back, suffix, original, first, fourth⟩ :=
    h.fourfold_interval v many
  exact ⟨stem, next, edge, back, suffix, original, first, fourth,
    C.repetition_from_root stem edge back⟩

end Certificate

end PetaProof
