import PetaProof.ValueAssembly

/-!
正の閾値の間でleafの合否が同じなら、同じ戦略の終局利得の合否も同じ。
通常千日手0と連続王手±Mateは正の範囲内で合否が変わらないため、leafだけを調べればよい。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 全合法leafについて、二つの閾値での合否が一致する。 -/
def SameLeafCut (s t : Int) : Prop :=
  ∀ v score, G.legal v (.leaf score) → (s ≤ score ↔ t ≤ score)

/-- leafの合否が変わらない二つの正閾値では、実際の最初の終局の合否も一致する。 -/
theorem TerminalResult.same_cut [DecidableEq V] {s t : Int}
    (spos : 0 < s) (sbound : s ≤ G.mate) (tpos : 0 < t) (tbound : t ≤ G.mate)
    (same : G.SameLeafCut s t) {plan : G.MovePlan} {root : V} {payoff : Int}
    (result : G.TerminalResult plan root payoff) : (s ≤ payoff ↔ t ≤ payoff) := by
  classical
  apply TerminalResult.property G result (fun _ => True) (fun _ _ => True)
    (fun score => s ≤ score ↔ t ≤ score) trivial
  · intro _ v move _ legal _
    cases move with
    | node _ => exact ⟨trivial, trivial⟩
    | leaf score => exact same v score legal
  · intro _ _ edge back _
    unfold repetitionValue
    dsimp only
    split
    · constructor <;> omega
    · split <;> constructor <;> omega

/-- 勝利領域だけでなく、同じ自分の戦略が両方の閾値を保証する。 -/
theorem lower_same_cut [DecidableEq V] {s t : Int}
    (spos : 0 < s) (sbound : s ≤ G.mate) (tpos : 0 < t) (tbound : t ≤ G.mate)
    (same : G.SameLeafCut s t) (root : V) :
    G.LowerGuarantee root s ↔ G.LowerGuarantee root t := by
  constructor
  · rintro ⟨self, lower⟩
    refine ⟨self, ?_⟩
    intro opponent payoff result
    exact (TerminalResult.same_cut G spos sbound tpos tbound same result).mp (lower opponent payoff result)
  · rintro ⟨self, lower⟩
    refine ⟨self, ?_⟩
    intro opponent payoff result
    exact (TerminalResult.same_cut G spos sbound tpos tbound same result).mpr (lower opponent payoff result)

/-- [s,t)にleaf値がなければ、閾値をsからtへ上げても全leafの合否は変わらない。 -/
theorem same_leaf_cut_of_gap {s t : Int} (ordered : s ≤ t)
    (gap : ∀ v score, G.legal v (.leaf score) → ¬ (s ≤ score ∧ score < t)) : G.SameLeafCut s t := by
  intro v score legal
  have absent := gap v score legal
  constructor <;> omega

/-- score=levelのleafがない場合、levelとlevel+1の閾値の勝利領域は一致する。 -/
theorem lower_step_no_leaf [DecidableEq V] (level : Int) (positive : 0 < level)
    (below : level < G.mate) (absent : ∀ v, ¬ G.legal v (.leaf level)) (root : V) :
    G.LowerGuarantee root level ↔ G.LowerGuarantee root (level + 1) := by
  apply G.lower_same_cut positive (by omega) (by omega) (by omega)
  apply G.same_leaf_cut_of_gap (by omega)
  intro v score legal between
  have same : score = level := by omega
  subst score
  exact absent v legal

/-- C++が処理する閾値。Mateはleafがなくても必ず含める。 -/
def CriticalLevel (level : Int) : Prop :=
  0 < level ∧ level ≤ G.mate ∧ (level = G.mate ∨ ∃ v, G.legal v (.leaf level))

theorem mate_critical : G.CriticalLevel G.mate :=
  ⟨G.mate_positive, Int.le_refl _, Or.inl rfl⟩

/-- 最大の正の保証値はMateか、どこかの合法leafの値である。 -/
theorem PositiveMaximum.critical [DecidableEq V] (root : V) {value : Int}
    (maximum : G.PositiveMaximum root value) (positive : 0 < value) : G.CriticalLevel value := by
  classical
  refine ⟨positive, maximum.bounded, ?_⟩
  by_cases top : value = G.mate
  · exact Or.inl top
  · right
    apply Classical.byContradiction
    intro no_leaf
    have below : value < G.mate := by have := maximum.bounded; omega
    have same := G.lower_step_no_leaf value positive below (fun v legal => no_leaf ⟨v, legal⟩) root
    exact maximum.next positive below (same.mp (maximum.wins positive))

/-- 実現する正の整数最適値も、処理対象の閾値以外には現れない。 -/
theorem ExactValue.positive_critical [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) {value : Int} (exact : G.ExactValue root value)
    (positive : 0 < value) (bounded : value ≤ G.mate) : G.CriticalLevel value := by
  apply PositiveMaximum.critical G root
    (show G.PositiveMaximum root value from {
      nonnegative := by omega
      bounded := bounded
      zero := by intro impossible; omega
      wins := fun _ => exact.1
      next := fun _ _ => ExactValue.not_above G vertices covered root exact
    }) positive

/-- ある整数最適値が分かっているとき、任意の閾値の勝敗はその値との比較に一致する。 -/
theorem ExactValue.lower_iff [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) {value : Int} (exact : G.ExactValue root value) (level : Int) :
    G.LowerGuarantee root level ↔ level ≤ value := by
  constructor
  · rintro ⟨self, lower⟩
    obtain ⟨opponent, upper⟩ := exact.2
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    exact Int.le_trans (lower opponent payoff result) (upper self payoff result)
  · intro below
    obtain ⟨self, lower⟩ := exact.1
    exact ⟨self, fun opponent payoff result => Int.le_trans below (lower opponent payoff result)⟩

end PetaProof.ThresholdGame
