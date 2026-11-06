import PetaProof.RankedMoveEnvelope
import PetaProof.RefutationMoveEnvelope
import PetaProof.IntegerValue

/-! 値が増える辺では順位を比較せず、同じ値の層だけで共通順位を使う候補表。 -/
namespace PetaProof.Walk

universe u
variable {V : Type u} {R : V → V → Prop} {a b : V}

/-- 単調な値が始点以下へ戻る歩道では、全ての辺の両端値が始点に一致する。 -/
theorem every_same_level (value : V → Int)
    (mono : ∀ x y, R x y → value x ≤ value y) (walk : Walk R a b)
    (upper : value b ≤ value a) :
    walk.Every (fun x y => value x = value a ∧ value y = value a) := by
  induction walk with
  | nil => trivial
  | cons edge tail ih =>
    have forward := mono _ _ edge
    have rest := tail.monotone value mono
    have same : value _ = value _ := Int.le_antisymm forward (Int.le_trans rest upper)
    refine ⟨⟨rfl, same.symm⟩, ?_⟩
    have all := ih (by omega)
    exact tail.every_mono all (fun _ _ _ levels => ⟨levels.1.trans same.symm, levels.2.trans same.symm⟩)

end PetaProof.Walk

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 値は固定プレイヤー視点。順位は値の層ごとに別々に用意してよい。 -/
structure ValueRankTable where
  value : V → Int
  bounded : ∀ vertex, -G.mate ≤ value vertex ∧ value vertex ≤ G.mate
  rank : Int → V → Nat

namespace ValueRankTable

variable {G} (table : G.ValueRankTable)

/-- 値の厳密増加なら順位比較は不要。同値の辺だけ、値の符号に応じて循環を制限する。 -/
def sameLevelCondition (vertex child : V) : Prop :=
  if 0 < table.value vertex then
    table.rank (table.value vertex) child ≤ table.rank (table.value vertex) vertex ∧
      (G.owner vertex ≠ G.player → ¬ G.check vertex child →
        table.rank (table.value vertex) child < table.rank (table.value vertex) vertex)
  else if -G.mate < table.value vertex then
    (G.owner vertex = G.player → G.check vertex child) →
      table.rank (table.value vertex) child < table.rank (table.value vertex) vertex
  else True

def candidateCondition (vertex : V) : Move V → Prop
  | .leaf score => table.value vertex ≤ score
  | .node child => table.value vertex ≤ table.value child ∧
      (table.value child = table.value vertex → table.sameLevelCondition vertex child)

def admissibleMove (vertex : V) (move : Move V) : Prop :=
  G.legal vertex move ∧ table.candidateCondition vertex move

/-- 比較するのは同じ値の辺だけなので、各頂点自身の値の順位だけ保存すればよい。 -/
def diagonal : G.ValueRankTable where
  value := table.value
  bounded := table.bounded
  rank := fun _ vertex => table.rank (table.value vertex) vertex

theorem diagonal_same_level (vertex child : V) (same : table.value child = table.value vertex) :
    table.diagonal.sameLevelCondition vertex child ↔ table.sameLevelCondition vertex child := by
  simp only [diagonal, sameLevelCondition, same]

theorem diagonal_candidate (vertex : V) (move : Move V) :
    table.diagonal.candidateCondition vertex move ↔ table.candidateCondition vertex move := by
  cases move with
  | leaf score => exact Iff.rfl
  | node child =>
    change (table.value vertex ≤ table.value child ∧
      (table.value child = table.value vertex → table.diagonal.sameLevelCondition vertex child)) ↔
      (table.value vertex ≤ table.value child ∧
      (table.value child = table.value vertex → table.sameLevelCondition vertex child))
    by_cases same : table.value child = table.value vertex
    · simp only [same, true_implies, table.diagonal_same_level vertex child same]
    · simp only [same, false_implies, and_true]

theorem diagonal_admissible (vertex : V) (move : Move V) :
    table.diagonal.admissibleMove vertex move ↔ table.admissibleMove vertex move :=
  and_congr (Iff.refl _) (table.diagonal_candidate vertex move)

def Internal (vertex child : V) : Prop := table.admissibleMove vertex (.node child)

theorem monotone (vertex child : V) (edge : table.Internal vertex child) :
    table.value vertex ≤ table.value child := edge.2.1

def LevelInternal (level : Int) (vertex child : V) : Prop :=
  table.Internal vertex child ∧ table.value vertex = level ∧ table.value child = level

theorem level_rank {level : Int} (positive : 0 < level) {vertex child : V}
    (edge : table.LevelInternal level vertex child) : table.rank level child ≤ table.rank level vertex := by
  have condition := edge.1.2.2 (edge.2.2.trans edge.2.1.symm)
  simp only [sameLevelCondition, edge.2.1, if_pos positive] at condition
  exact condition.1

theorem level_strict {level : Int} (positive : 0 < level) {vertex child : V}
    (edge : table.LevelInternal level vertex child)
    (other : G.owner vertex ≠ G.player) (noncheck : ¬ G.check vertex child) :
    table.rank level child < table.rank level vertex := by
  have condition := edge.1.2.2 (edge.2.2.trans edge.2.1.symm)
  simp only [sameLevelCondition, edge.2.1, if_pos positive] at condition
  exact condition.2 other noncheck

theorem positive_level_loop_checks {level : Int} (positive : 0 < level) {a b : V}
    (edge : table.LevelInternal level a b) (back : Walk (table.LevelInternal level) b a) :
    (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  apply Walk.every_returning _ _ (Walk.cons edge back) (.nil a)
  intro vertex child step returning other
  apply Classical.byContradiction
  intro noncheck
  have strict := table.level_strict positive step other noncheck
  have lower := returning.nat_antitone (table.rank level) (fun _ _ found => table.level_rank positive found)
  omega

theorem positive_loop_checks {a b : V} (edge : table.Internal a b) (back : Walk table.Internal b a)
    (positive : 0 < table.value a) :
    (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  let loop := Walk.cons edge back
  have levels := loop.every_same_level table.value table.monotone (Int.le_refl _)
  let convert : ∀ v w, table.Internal v w ∧ (table.value v = table.value a ∧ table.value w = table.value a) →
      table.LevelInternal (table.value a) v w := fun _ _ found => found
  have all := table.positive_level_loop_checks positive (convert a b ⟨edge, levels.1⟩)
    ((back.withEvery _ levels.2).map convert)
  simpa only [Walk.Every, Walk.every_map, Walk.every_withEvery] using all

theorem nonpositive_level_strict {level : Int} (nonpositive : ¬ 0 < level) (better : -G.mate < level)
    {vertex child : V} (edge : table.LevelInternal level vertex child)
    (ownCheck : G.owner vertex = G.player → G.check vertex child) :
    table.rank level child < table.rank level vertex := by
  have condition := edge.1.2.2 (edge.2.2.trans edge.2.1.symm)
  simp only [sameLevelCondition, edge.2.1, if_neg nonpositive, if_pos better] at condition
  exact condition ownCheck

theorem no_own_loop {a b : V} (edge : table.Internal a b) (back : Walk table.Internal b a)
    (better : -G.mate < table.value a) :
    ¬ (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w) := by
  intro own
  by_cases positive : 0 < table.value a
  · have other := table.positive_loop_checks edge back positive
    have all := (Walk.cons edge back).every_mono ((Walk.cons edge back).every_and own other) (by
      intro vertex child _ checks
      by_cases turn : G.owner vertex = G.player
      · exact checks.1 turn
      · exact checks.2 turn)
    exact G.no_mutual_cycle a b ⟨edge.1, all.1⟩
      ((back.withEvery _ all.2).map (fun _ _ found => ⟨found.1.1, found.2⟩))
  · let loop := Walk.cons edge back
    have levels := loop.every_same_level table.value table.monotone (Int.le_refl _)
    have first : table.LevelInternal (table.value a) a b := ⟨edge, levels.1⟩
    have strict := table.nonpositive_level_strict positive better first own.1
    have both := back.every_and levels.2 own.2
    have lower := (back.withEvery _ both).nat_antitone (table.rank (table.value a)) (by
      intro vertex child found
      exact Nat.le_of_lt (table.nonpositive_level_strict positive better
        ⟨found.1, found.2.1⟩ found.2.2))
    omega

/-- 層別の局所条件から、値が異なる領域も含めた全候補表の循環検査条件を構成する。 -/
def certificate : Certificate V where
  edge := table.Internal
  owner := G.owner
  check := G.check
  player := G.player
  value := table.value
  mate := G.mate
  mate_pos := G.mate_positive
  bounded := table.bounded
  monotone := table.monotone
  no_own_cycle := by
    intro a b edge back
    let convert : ∀ v w, table.Internal v w ∧ -G.mate < table.value v ∧ -G.mate < table.value w ∧
        (G.owner v = G.player → G.check v w) → table.Internal v w := fun _ _ found => found.1
    have own : (Walk.cons (convert a b edge) (back.map convert)).Every
        (fun v w => G.owner v = G.player → G.check v w) := by
      refine ⟨edge.2.2.2, ?_⟩
      rw [Walk.every_map]
      exact back.every_mono back.every_true (fun _ _ found _ => found.2.2.2)
    exact table.no_own_loop edge.1 (back.map convert) edge.2.1 own
  opponent_cycle_checks := by
    intro a b edge positive _ back other
    exact (table.positive_loop_checks edge back positive).1 other

/-- 選別した候補の中でなら、局面と履歴に応じて手を選び替えてよい。 -/
def AdmissiblePlan (self : G.MovePlan) : Prop :=
  ∀ history vertex, G.owner vertex = G.player → table.admissibleMove vertex (self.choose history vertex)

/-- 相手の全合法手を保持する条件。相手の不都合な応手をfilterしない。 -/
def AllReplies : Prop :=
  ∀ vertex move, G.owner vertex ≠ G.player → G.legal vertex move → table.candidateCondition vertex move

theorem terminal_lower [DecidableEq V] (replies : table.AllReplies) (self opponent : G.MovePlan)
    (allowed : table.AdmissiblePlan self) (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply TerminalResult.property G result (fun vertex => table.value root ≤ table.value vertex)
    (fun vertex child => table.Internal vertex child ∧ table.value root ≤ table.value vertex)
    (fun score => table.value root ≤ score) (Int.le_refl _)
  · intro history vertex move lower legal selected
    have candidate : table.candidateCondition vertex move := by
      by_cases own : G.owner vertex = G.player
      · have same : self.choose history vertex = move := by simpa only [combinePlans, if_pos own] using selected
        rw [← same]
        exact (allowed history vertex own).2
      · exact replies vertex move own legal
    cases move with
    | leaf score => exact Int.le_trans lower candidate
    | node child => exact ⟨Int.le_trans lower candidate.1, ⟨legal, candidate⟩, lower⟩
  · intro a b edge back all
    let convert : ∀ v w, G.LegalNode v w ∧ (table.Internal v w ∧ table.value root ≤ table.value v) →
        table.Internal v w := fun _ _ found => found.2.1
    have bound := table.certificate.repetition_guarantee (convert a b ⟨edge, all.1⟩)
      ((back.withEvery _ all.2).map convert)
    have same := G.repetitionValue_eq_certificate table.certificate rfl rfl rfl rfl
      (convert a b ⟨edge, all.1⟩) ((back.withEvery _ all.2).map convert)
    rw [← same] at bound
    have mapped := (G.repetitionValue_map ⟨edge, all.1⟩ (back.withEvery _ all.2) convert).trans
      (G.repetitionValue_restrict edge back all.1 all.2)
    rw [mapped] at bound
    exact Int.le_trans all.1.2 bound

/-- 両視点の候補表を独立に守れば、同時に選んだ手順の利得は約束値に一致する。 -/
theorem terminal_exact [DecidableEq V] (opposite : G.opposite.ValueRankTable)
    (sameValue : ∀ vertex, opposite.value vertex = -table.value vertex)
    (replies : table.AllReplies) (oppositeReplies : opposite.AllReplies)
    (self opponent : G.MovePlan) (allowed : table.AdmissiblePlan self)
    (oppositeAllowed : opposite.AdmissiblePlan opponent.opposite)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : payoff = table.value root := by
  have lower := table.terminal_lower replies self opponent allowed root payoff result
  have reflected := TerminalResult.opposite G result
  rw [G.opposite_combine] at reflected
  have upper := opposite.terminal_lower oppositeReplies opponent.opposite self.opposite
    oppositeAllowed root (-payoff) reflected
  rw [sameValue root] at upper
  omega

end ValueRankTable
end PetaProof.ThresholdGame
