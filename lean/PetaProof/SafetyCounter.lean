import PetaProof.IndexedPropagation
import PetaProof.Pruning

/-!
safety()の親一局面のcount。seenは逆辺の削除通知履歴であり、子のaliveとは区別する。
親の削除後はcountを使わない。以下の更新はaliveガードを通過した親に対応する。
-/
namespace PetaProof.SafetyCounter

universe u
variable {E : Type u} [DecidableEq E]

structure Counter (E : Type u) where
  seen : E → Bool
  count : Nat

def initial (good : Nat) (internal : List E) : Counter E :=
  ⟨fun _ => false, good + internal.length⟩

def removeEdge (counter : Counter E) (edge : E) : Counter E :=
  ⟨markSeen counter.seen edge, counter.count - 1⟩

def Exact (good : Nat) (internal : List E) (counter : Counter E) : Prop :=
  counter.count = good + remainingEdges counter.seen internal

omit [DecidableEq E] in
theorem initial_exact (good : Nat) (internal : List E) : Exact good internal (initial good internal) := by
  simp [Exact, initial, remaining_initial]

/-- 異なる辺IDなら同じ子への手でも別々に数え、新規通知一件で正確に一つ減る。 -/
theorem remove_exact (good : Nat) (internal : List E) (unique : internal.Nodup)
    (counter : Counter E) (invariant : Exact good internal counter) (edge : E)
    (member : edge ∈ internal) (fresh : counter.seen edge = false) :
    Exact good internal (removeEdge counter edge) ∧ 0 < counter.count ∧
      (removeEdge counter edge).count + 1 = counter.count := by
  have decrement := remaining_mark_fresh counter.seen edge internal unique member fresh
  unfold Exact at *
  simp only [removeEdge]
  omega

omit [DecidableEq E] in
theorem remaining_positive_iff (seen : E → Bool) (edges : List E) :
    0 < remainingEdges seen edges ↔ ∃ e ∈ edges, seen e = false := by
  induction edges with
  | nil => simp [remainingEdges]
  | cons e rest ih =>
    cases flag : seen e <;> simp [remainingEdges, flag, ih]
    omega

/-- 初期走査で分類した出辺。badは良い出口でも局所内部辺でもない手。
    good判定を先に行うため、同じ辺がinternalへも入ることはない。 -/
structure View (E : Type u) where
  good : List E
  internal : List E
  bad : List E
  internal_unique : internal.Nodup
  internal_not_good : ∀ e ∈ internal, e ∉ good
  bad_disjoint : ∀ e ∈ bad, e ∉ good ∧ e ∉ internal

def View.outgoing (view : View E) : List E := view.good ++ view.internal ++ view.bad

def View.safe (view : View E) (counter : Counter E) (edge : E) : Prop :=
  edge ∈ view.good ∨ (edge ∈ view.internal ∧ counter.seen edge = false)

def View.canStay (view : View E) (own : Bool) (counter : Counter E) : Prop :=
  (own = true → ∃ e ∈ view.outgoing, view.safe counter e) ∧
  (own = false → ∀ e ∈ view.outgoing, view.safe counter e)

omit [DecidableEq E] in
theorem or_count_iff (view : View E) (counter : Counter E)
    (invariant : Exact view.good.length view.internal counter) :
    view.canStay true counter ↔ 0 < counter.count := by
  have exists_good : (∃ e, e ∈ view.good) ↔ 0 < view.good.length := by
    constructor
    · rintro ⟨e, member⟩; exact List.length_pos_of_mem member
    · intro positive
      cases h : view.good with
      | nil => simp [h] at positive
      | cons e rest => exact ⟨e, by simp [h]⟩
  have exists_internal := remaining_positive_iff counter.seen view.internal
  have represented : view.canStay true counter ↔
      (∃ e, e ∈ view.good) ∨ ∃ e ∈ view.internal, counter.seen e = false := by
    constructor
    · intro stay
      obtain ⟨e, _, safe⟩ := stay.1 rfl
      exact safe.elim (fun h => Or.inl ⟨e, h⟩) (fun h => Or.inr ⟨e, h⟩)
    · intro witness
      constructor
      · intro _
        rcases witness with ⟨e, good⟩ | ⟨e, member, fresh⟩
        · exact ⟨e, by simp [View.outgoing, good], Or.inl good⟩
        · exact ⟨e, by simp [View.outgoing, member], Or.inr ⟨member, fresh⟩⟩
      · intro impossible; cases impossible
  rw [represented, exists_good, ← exists_internal]
  unfold Exact at invariant
  omega

omit [DecidableEq E] in
theorem and_unseen_iff (view : View E) (counter : Counter E) :
    view.canStay false counter ↔ view.bad = [] ∧ ∀ e ∈ view.internal, counter.seen e = false := by
  constructor
  · intro stay
    constructor
    · cases bad : view.bad with
      | nil => rfl
      | cons e rest =>
        have member : e ∈ view.bad := by simp [bad]
        have safe := stay.2 rfl e (by simp [View.outgoing, member])
        rcases safe with good | internal
        · exact False.elim ((view.bad_disjoint e member).1 good)
        · exact False.elim ((view.bad_disjoint e member).2 internal.1)
    · intro e member
      have safe := stay.2 rfl e (by simp [View.outgoing, member])
      exact safe.elim (fun good => False.elim (view.internal_not_good e member good)) And.right
  · rintro ⟨empty, unseen⟩
    constructor
    · intro impossible; cases impossible
    · intro _ e member
      simp only [View.outgoing, empty, List.append_nil, List.mem_append] at member
      exact member.elim Or.inl (fun h => Or.inr ⟨h, unseen e h⟩)

/-- AND側は一本でも内部辺を失えば、countがまだ正でも削除候補になる。 -/
theorem and_remove_invalid (view : View E) (counter : Counter E) (edge : E)
    (member : edge ∈ view.internal) : ¬ view.canStay false (removeEdge counter edge) := by
  intro stay
  have unseen := ((and_unseen_iff view _).mp stay).2 edge member
  simp [removeEdge, markSeen] at unseen

/-- OR側の通知後の投入条件count==0は、安全な手がなくなったことと同値。 -/
theorem or_remove_invalid_iff (view : View E) (counter : Counter E)
    (invariant : Exact view.good.length view.internal counter) (edge : E)
    (member : edge ∈ view.internal) (fresh : counter.seen edge = false) :
    (removeEdge counter edge).count = 0 ↔ ¬ view.canStay true (removeEdge counter edge) := by
  have next := (remove_exact view.good.length view.internal view.internal_unique counter invariant edge member fresh).1
  rw [or_count_iff view _ next]
  omega

omit [DecidableEq E] in
/-- 初期badフラグとOR側のcount==0が、初期投入すべき局面を過不足なく表す。 -/
theorem initial_invalid_iff (view : View E) (own : Bool) :
    ¬ view.canStay own (initial view.good.length view.internal) ↔
      (own = true ∧ (initial view.good.length view.internal).count = 0) ∨
      (own = false ∧ view.bad ≠ []) := by
  cases own with
  | true =>
    rw [or_count_iff view _ (initial_exact _ _)]
    simp only [Bool.true_eq_false, and_false, false_and, or_false, and_true, true_and]
    omega
  | false => simp [and_unseen_iff, initial]

theorem safe_remove_subset (view : View E) (counter : Counter E) (edge other : E)
    (safe : view.safe (removeEdge counter edge) other) : view.safe counter other := by
  rcases safe with good | ⟨internal, unseen⟩
  · exact Or.inl good
  · right
    refine ⟨internal, ?_⟩
    by_cases same : other = edge
    · subst other; simp [removeEdge, markSeen] at unseen
    · simpa [removeEdge, markSeen, same] using unseen

/-- 候補は減るだけなので、一度投入理由が成立すれば、待機中にも有効なままである。 -/
theorem invalid_persists (view : View E) (own : Bool) (counter : Counter E) (edge : E)
    (invalid : ¬ view.canStay own counter) : ¬ view.canStay own (removeEdge counter edge) := by
  intro stay
  apply invalid
  constructor
  · intro self
    obtain ⟨e, member, safe⟩ := stay.1 self
    exact ⟨e, member, safe_remove_subset view counter edge e safe⟩
  · intro opponent e member
    exact safe_remove_subset view counter edge e (stay.2 opponent e member)

/-- 逆辺通知の交錯順は任意。辺IDの新規性だけを要求する。 -/
inductive Notifications (view : View E) : Counter E → Counter E → Prop
  | done (counter) : Notifications view counter counter
  | next {start middle finish} (edge : E) : edge ∈ view.internal → start.seen edge = false →
      middle = removeEdge start edge → Notifications view middle finish → Notifications view start finish

theorem notifications_exact (view : View E) {start finish : Counter E}
    (run : Notifications view start finish) (invariant : Exact view.good.length view.internal start) :
    Exact view.good.length view.internal finish := by
  induction run with
  | done => exact invariant
  | next edge member fresh same tail ih =>
    subst same
    exact ih (remove_exact _ _ view.internal_unique _ invariant edge member fresh).1

theorem notifications_invalid (view : View E) (own : Bool) {start finish : Counter E}
    (run : Notifications view start finish) (invalid : ¬ view.canStay own start) :
    ¬ view.canStay own finish := by
  induction run with
  | done => exact invalid
  | next edge member fresh same tail ih =>
    subst same
    exact ih (invalid_persists view own _ edge invalid)

end PetaProof.SafetyCounter
