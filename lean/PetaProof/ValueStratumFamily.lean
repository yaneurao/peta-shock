import PetaProof.ValueStratumEnvelope

/-! 各値の閾値証拠から、一つの層別候補表と非空な保証手を構成する。 -/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- b≤0の下限に対応する、相手視点の正の閾値1-b。 -/
def counterThreshold (bound : Int) (better : -G.mate < bound) (nonpositive : bound ≤ 0) : ThresholdGame V :=
  G.opposite.retune (1 - bound) (by omega) (by change 1 - bound ≤ G.mate; omega)

/-- 同じ値の全頂点は同じ領域証拠を共有する。頂点ごとに独立の方策を混ぜる入力ではない。 -/
structure StratumFamily where
  value : V → Int
  bounded : ∀ vertex, -G.mate ≤ value vertex ∧ value vertex ≤ G.mate
  leaves : G.BoundedLeaves
  positive : ∀ bound (pos : 0 < bound) (cap : bound ≤ G.mate),
    (G.retune bound pos cap).RankedRegion (fun vertex => bound ≤ value vertex)
  nonpositive : ∀ bound (better : -G.mate < bound) (nonpos : bound ≤ 0),
    (G.counterThreshold bound better nonpos).RefutationRegion (fun vertex => bound ≤ value vertex)

namespace StratumFamily

variable {G} (family : G.StratumFamily)

noncomputable def table : G.ValueRankTable where
  value := family.value
  bounded := family.bounded
  rank := fun bound vertex =>
    if pos : 0 < bound ∧ bound ≤ G.mate then (family.positive bound pos.1 pos.2).rank vertex
    else if nonpos : -G.mate < bound ∧ bound ≤ 0 then
      (family.nonpositive bound nonpos.1 nonpos.2).rank vertex
    else 0

theorem positive_rank (bound : Int) (positive : 0 < bound) (cap : bound ≤ G.mate) (vertex : V) :
    family.table.rank bound vertex = (family.positive bound positive cap).rank vertex := by
  simp only [table, dif_pos (show 0 < bound ∧ bound ≤ G.mate from ⟨positive, cap⟩)]

theorem nonpositive_rank (bound : Int) (better : -G.mate < bound) (nonpositive : bound ≤ 0) (vertex : V) :
    family.table.rank bound vertex = (family.nonpositive bound better nonpositive).rank vertex := by
  have notPositive : ¬ (0 < bound ∧ bound ≤ G.mate) := by omega
  simp only [table, dif_neg notPositive, dif_pos (show -G.mate < bound ∧ bound ≤ 0 from ⟨better, nonpositive⟩)]

theorem positive_allowed (bound : Int) (positive : 0 < bound) (cap : bound ≤ G.mate)
    (vertex : V) (level : family.value vertex = bound) (move : Move V)
    (follows : (G.retune bound positive cap).Follows (family.positive bound positive cap).choice vertex move) :
    family.table.admissibleMove vertex move := by
  let region := family.positive bound positive cap
  have inside : bound ≤ family.value vertex := by omega
  refine ⟨follows.1, ?_⟩
  cases move with
  | leaf score =>
    have closed := region.closed vertex inside (.leaf score) follows
    change family.value vertex ≤ score
    change bound ≤ score at closed
    omega
  | node child =>
    have closed := region.closed vertex inside (.node child) follows
    change family.value vertex ≤ family.value child ∧ _
    refine ⟨by omega, fun same => ?_⟩
    change family.table.sameLevelCondition vertex child
    simp only [ValueRankTable.sameLevelCondition, show family.table.value vertex = bound from level,
      if_pos positive, family.positive_rank bound positive cap]
    exact ⟨region.decreasing vertex child inside follows, region.opponent_strict vertex child inside follows⟩

theorem nonpositive_allowed (bound : Int) (better : -G.mate < bound) (nonpositive : bound ≤ 0)
    (vertex : V) (level : family.value vertex = bound) (move : Move V)
    (reply : (G.counterThreshold bound better nonpositive).Replies
      (family.nonpositive bound better nonpositive).response vertex move.negate) :
    family.table.admissibleMove vertex move := by
  let region := family.nonpositive bound better nonpositive
  have inside : bound ≤ family.value vertex := by omega
  have legal : G.legal vertex move := by
    have law := reply.1
    change G.legal vertex move.negate.negate at law
    simpa only [Move.negate_negate] using law
  refine ⟨legal, ?_⟩
  cases move with
  | leaf score =>
    have closed := region.closed vertex inside (.leaf (-score)) reply
    change -score < 1 - bound at closed
    change family.value vertex ≤ score
    omega
  | node child =>
    have closed := region.closed vertex inside (.node child) reply
    change family.value vertex ≤ family.value child ∧ _
    refine ⟨by omega, fun same => ?_⟩
    change family.table.sameLevelCondition vertex child
    simp only [ValueRankTable.sameLevelCondition, show family.table.value vertex = bound from level,
      if_neg (show ¬ 0 < bound by omega), if_pos better,
      family.nonpositive_rank bound better nonpositive]
    intro checking
    apply region.strict_checking vertex child inside reply
    change G.owner vertex ≠ !G.player → G.check vertex child
    simpa only [ne_eq, Bool.eq_not, Classical.not_not] using checking

theorem bottom_allowed (vertex : V) (level : family.value vertex = -G.mate)
    (move : Move V) (legal : G.legal vertex move) : family.table.admissibleMove vertex move := by
  refine ⟨legal, ?_⟩
  cases move with
  | leaf score =>
    change family.value vertex ≤ score
    rw [level]
    exact (family.leaves vertex score legal).1
  | node child =>
    change family.value vertex ≤ family.value child ∧ _
    refine ⟨by rw [level]; exact (family.bounded child).1, fun _ => ?_⟩
    have positive := G.mate_positive
    simp [ValueRankTable.sameLevelCondition, table, level, show ¬ 0 < -G.mate by omega]

/-- 相手の全合法手も各閾値証拠から候補条件を満たす。 -/
theorem all_replies : family.table.AllReplies := by
  intro vertex move other legal
  by_cases positive : 0 < family.value vertex
  · exact (family.positive_allowed _ positive (family.bounded vertex).2 vertex rfl move
      ⟨legal, fun own => False.elim (other own)⟩).2
  · by_cases better : -G.mate < family.value vertex
    · have nonpositive : family.value vertex ≤ 0 := by omega
      apply (family.nonpositive_allowed _ better nonpositive vertex rfl move ?_).2
      refine ⟨?_, ?_⟩
      · change G.legal vertex move.negate.negate
        simpa only [Move.negate_negate] using legal
      · intro turn
        have own : G.owner vertex = G.player := by
          simpa only [counterThreshold, retune, opposite, ne_eq, Bool.eq_not, Classical.not_not] using turn
        exact False.elim (other own)
    · have bottom : family.value vertex = -G.mate := by have := (family.bounded vertex).1; omega
      exact (family.bottom_allowed vertex bottom move legal).2

/-- 各頂点の自分の保証手を、その頂点の値に対応する共通証拠から選ぶ。 -/
noncomputable def referenceMove (vertex : V) : Move V := by
  classical
  exact if pos : 0 < family.value vertex then
    (family.positive _ pos (family.bounded vertex).2).choice vertex
  else if better : -G.mate < family.value vertex then
    ((family.nonpositive _ better (by omega)).response vertex).negate
  else G.defaultPlan.choose [] vertex

theorem referenceMove_safe (vertex : V) (own : G.owner vertex = G.player) :
    family.table.admissibleMove vertex (family.referenceMove vertex) := by
  classical
  by_cases pos : 0 < family.value vertex
  · simp only [referenceMove, dif_pos pos]
    apply family.positive_allowed _ pos (family.bounded vertex).2 vertex rfl
    exact ⟨(family.positive _ pos (family.bounded vertex).2).chosen_legal vertex (Int.le_refl _) own, fun _ => rfl⟩
  · simp only [referenceMove, dif_neg pos]
    by_cases better : -G.mate < family.value vertex
    · simp only [dif_pos better]
      apply family.nonpositive_allowed _ better (by omega) vertex rfl
      rw [Move.negate_negate]
      refine ⟨?_, fun _ => rfl⟩
      apply (family.nonpositive _ better (by omega)).chosen_legal vertex (Int.le_refl _)
      change G.owner vertex ≠ !G.player
      simpa only [ne_eq, Bool.eq_not, Classical.not_not] using own
    · simp only [dif_neg better]
      apply family.bottom_allowed vertex (by have := (family.bounded vertex).1; omega)
      exact G.defaultPlan.legal [] vertex

noncomputable def reference : G.MovePlan := by
  classical
  exact {
    choose := fun _ vertex => if G.owner vertex = G.player then family.referenceMove vertex else G.defaultPlan.choose [] vertex
    legal := by
      intro history vertex
      by_cases own : G.owner vertex = G.player
      · simp only [if_pos own]; exact (family.referenceMove_safe vertex own).1
      · simp only [if_neg own]; exact G.defaultPlan.legal [] vertex
  }

theorem reference_admissible : family.table.AdmissiblePlan family.reference := by
  classical
  intro history vertex own
  simpa only [reference, if_pos own] using family.referenceMove_safe vertex own

theorem candidates_nonempty (vertex : V) (own : G.owner vertex = G.player) :
    ∃ move, family.table.admissibleMove vertex move :=
  ⟨family.referenceMove vertex, family.referenceMove_safe vertex own⟩

theorem reference_lower [DecidableEq V] (opponent : G.MovePlan) (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans family.reference opponent) root payoff) :
    family.value root ≤ payoff :=
  family.table.terminal_lower family.all_replies family.reference opponent family.reference_admissible root payoff result

/-- 両視点の閾値証拠族を統合すれば、正解値を別の仮定に置かず整数値を保証できる。 -/
theorem exact_values [DecidableEq V] (other : G.opposite.StratumFamily)
    (sameValue : ∀ vertex, other.value vertex = -family.value vertex) (root : V) :
    G.ExactValue root (family.value root) := by
  refine ⟨⟨family.reference, fun opponent payoff result => family.reference_lower opponent root payoff result⟩,
    other.reference.unopposite, ?_⟩
  intro self payoff result
  have reflected := TerminalResult.opposite G result
  rw [G.opposite_combine, MovePlan.opposite_unopposite] at reflected
  have upper := other.reference_lower self.opposite root (-payoff) reflected
  rw [sameValue root] at upper
  omega

theorem both_reference_exact [DecidableEq V] (other : G.opposite.StratumFamily)
    (sameValue : ∀ vertex, other.value vertex = -family.value vertex) (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans family.reference other.reference.unopposite) root payoff) :
    payoff = family.value root := by
  apply family.table.terminal_exact other.table sameValue family.all_replies other.all_replies
    family.reference other.reference.unopposite family.reference_admissible ?_ root payoff result
  rw [MovePlan.opposite_unopposite]
  exact other.reference_admissible

end StratumFamily
end PetaProof.ThresholdGame
