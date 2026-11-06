import PetaProof.SafetyCounterSemantics

namespace PetaProof.SafetyCounter.Examples

inductive Edge where
  | first | second | exit | bad
  deriving DecidableEq

def pair : View Edge := {
  good := []
  internal := [.first, .second]
  bad := []
  internal_unique := by decide
  internal_not_good := by simp
  bad_disjoint := by simp
}

def c0 := initial pair.good.length pair.internal
def c1 := removeEdge c0 Edge.first
def c2 := removeEdge c1 Edge.second

theorem counts : c0.count = 2 ∧ c1.count = 1 ∧ c2.count = 0 := by decide

theorem first_exact : Exact pair.good.length pair.internal c1 :=
  (remove_exact _ _ pair.internal_unique c0 (initial_exact _ _) Edge.first (by decide) (by decide)).1

theorem second_exact : Exact pair.good.length pair.internal c2 :=
  (remove_exact _ _ pair.internal_unique c1 first_exact Edge.second (by decide) (by decide)).1

-- 二本の辺が同じ子を指していても、AND親は最初の通知で不適格、OR親は二本目で不適格。
theorem first_or_survives : pair.canStay true c1 := (or_count_iff _ _ first_exact).mpr (by decide)
theorem first_and_invalid : ¬ pair.canStay false c1 := and_remove_invalid _ _ Edge.first (by decide)
theorem last_or_invalid : ¬ pair.canStay true c2 := by
  rw [or_count_iff _ _ second_exact]
  decide

theorem positive_before_last : 0 < c1.count :=
  (remove_exact _ _ pair.internal_unique c1 first_exact Edge.second (by decide) (by decide)).2.1

-- 同じ辺を誤って再通知すると、自然数減算が走れても意味上の本数は壊れる。
theorem duplicate_notification_breaks_count :
    ¬ Exact pair.good.length pair.internal (removeEdge c1 Edge.first) := by
  unfold Exact
  decide

def withExit : View Edge := {
  good := [.exit]
  internal := [.first, .second]
  bad := []
  internal_unique := by decide
  internal_not_good := by intro e member; cases e <;> simp_all
  bad_disjoint := by simp
}

def exitCounter := removeEdge (removeEdge (initial 1 withExit.internal) Edge.first) Edge.second

theorem good_exit_preserved : exitCounter.count = 1 ∧ withExit.canStay true exitCounter := by
  constructor
  · rfl
  · constructor
    · intro _; exact ⟨Edge.exit, by decide, Or.inl (by decide)⟩
    · intro impossible; cases impossible

def initialBad : View Edge := {
  good := []
  internal := []
  bad := [.bad]
  internal_unique := by decide
  internal_not_good := by simp
  bad_disjoint := by simp
}

theorem initial_bad_rejected : ¬ initialBad.canStay false (initial 0 []) := by
  rw [and_unseen_iff]
  simp [initialBad]

theorem pair_notifications : Notifications pair c0 c2 :=
  Notifications.next Edge.first (by decide) (by decide) rfl
    (Notifications.next Edge.second (by decide) (by decide) rfl (Notifications.done _))

theorem exact_after_notifications : Exact pair.good.length pair.internal c2 :=
  notifications_exact pair pair_notifications (initial_exact _ _)

theorem invalid_while_waiting : ¬ pair.canStay false c2 :=
  invalid_persists pair false c1 Edge.second first_and_invalid

theorem partially_notified_support : pair.safe c1 Edge.second ∧ ¬ pair.safe c1 Edge.first := by
  constructor
  · exact Or.inr ⟨by decide, by decide⟩
  · intro safe
    rcases safe with impossible | ⟨_, unseen⟩
    · cases impossible
    · change true = false at unseen; cases unseen

end PetaProof.SafetyCounter.Examples
