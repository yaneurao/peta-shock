import PetaProof.FiniteRefutation
import PetaProof.CompletenessExamples

/-! 通常千日手の0、相手連続王手負けのMate、leaf出口の反証を検査する。 -/
namespace PetaProof.FinitePayoffExamples

open PropagationExamples

def drawGame : ThresholdGame Bool where
  legal := fun v m => m = .node (!v)
  owner := fun v => v
  check := fun _ _ => False
  player := false
  threshold := 10
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by intro v w edge; cases v <;> cases w <;> simp_all
  nonempty_moves := fun v => ⟨.node (!v), rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def drawRegion : drawGame.RefutationRegion (fun _ => True) where
  response := fun v => .node (!v)
  chosen_legal := fun _ _ _ => rfl
  closed := by
    intro v _ m reply
    have selected : m = .node (!v) := reply.1
    subst m
    trivial
  rank := fun v => if v then 0 else 1
  strict_checking := by
    intro v w _ reply checking
    have selected : (.node w : Move Bool) = .node (!v) := reply.1
    have child : w = !v := Move.node.inj selected
    subst w
    cases v with
    | false => decide
    | true => exact False.elim (checking (by decide))

def drawEdge (v : Bool) : drawRegion.Internal v (!v) :=
  ⟨trivial, rfl, fun _ => rfl⟩

def drawBack : Walk drawRegion.Internal true false :=
  .cons (drawEdge true) (.cons (drawEdge false) (.cons (drawEdge true)
    (.cons (drawEdge false) (.cons (drawEdge true) (.nil false)))))

def drawTrace : Walk drawRegion.Internal false false := .cons (drawEdge false) drawBack

theorem drawTrace_four_occurrences : drawTrace.visits.count false = 4 := by decide

/-- 最後の訪問以前には、どの局面もまだ四回出現していない。 -/
theorem drawTrace_first_terminal : ∀ v, drawTrace.visits.dropLast.count v < 4 := by
  intro v
  cases v <;> decide

theorem draw_repetition_is_zero : drawGame.repetitionValue (drawEdge false) drawBack = 0 := by
  have no_own : ¬ drawTrace.Every (fun v w => drawGame.owner v = drawGame.player → drawGame.check v w) := by
    intro all
    exact all.1 rfl
  have no_other := drawRegion.no_opponent_check_loop (drawEdge false) drawBack
  change ¬ (Walk.cons (drawEdge false) drawBack).Every
    (fun v w => drawGame.owner v = drawGame.player → drawGame.check v w) at no_own
  simp only [ThresholdGame.repetitionValue, if_neg no_own, if_neg no_other]

/-- 最初から四回目までの6手区間を切り出しても、反証の上界が成り立つ。 -/
theorem draw_actual_fourfold_below :
    ∃ (stem : Walk drawRegion.Internal false false) (next : Bool)
      (edge : drawRegion.Internal false next) (back : Walk drawRegion.Internal next false)
      (suffix : Walk drawRegion.Internal false false),
      drawTrace = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count false = 1 ∧ (Walk.cons edge back).visits.count false = 4 ∧
      drawGame.repetitionValue edge back < drawGame.threshold :=
  drawRegion.fourfold_lt drawTrace false (by rw [drawTrace_four_occurrences]; exact Nat.le_refl _)

def winningEdge (v : Bool) : loopRegion.FiniteInternal v (!v) := by
  refine ⟨Or.inr trivial, rfl, ?_⟩
  intro own
  exact loopRegion.chosen_legal v (Or.inr trivial) own

def winningBack : Walk loopRegion.FiniteInternal true false :=
  .cons (winningEdge true) (.cons (winningEdge false) (.cons (winningEdge true)
    (.cons (winningEdge false) (.cons (winningEdge true) (.nil false)))))

theorem opponent_check_repetition_is_mate :
    loopGame.repetitionValue (winningEdge false) winningBack = 32000 := by
  have no_own := loopRegion.finite_loop_not_own_checks (winningEdge false) winningBack
  have opponent := loopRegion.finite_loop_opponent_checks (winningEdge false) winningBack
  simp only [ThresholdGame.repetitionValue, if_neg no_own, if_pos opponent]
  rfl

def ownCheckingGame : ThresholdGame Bool := {
  drawGame with
  check := fun v _ => v = false
  no_mutual_cycle := by
    intro a b edge back
    cases back with
    | nil => exact drawGame.alternating a a edge.1 rfl
    | cons next _ =>
      have first : a = false := edge.2
      have second : b = false := next.2
      exact drawGame.alternating a b edge.1 (second.trans first.symm)
}

def ownCheckingRegion : ownCheckingGame.RefutationRegion (fun _ => True) where
  response := drawRegion.response
  chosen_legal := drawRegion.chosen_legal
  closed := drawRegion.closed
  rank := drawRegion.rank
  strict_checking := by
    intro v w _ reply checking
    have selected : (.node w : Move Bool) = .node (!v) := reply.1
    have child : w = !v := Move.node.inj selected
    subst w
    cases v with
    | false => decide
    | true =>
      have impossible : (true : Bool) = false := checking (by decide)
      cases impossible

def ownCheckingEdge (v : Bool) : ownCheckingRegion.Internal v (!v) :=
  ⟨trivial, rfl, fun _ => rfl⟩

def ownCheckingBack : Walk ownCheckingRegion.Internal true false :=
  .cons (ownCheckingEdge true) (.cons (ownCheckingEdge false) (.cons (ownCheckingEdge true)
    (.cons (ownCheckingEdge false) (.cons (ownCheckingEdge true) (.nil false)))))

theorem own_check_repetition_is_minus_mate :
    ownCheckingGame.repetitionValue (ownCheckingEdge false) ownCheckingBack = -32000 := by
  let loop := Walk.cons (ownCheckingEdge false) ownCheckingBack
  have all : loop.Every
      (fun v w => ownCheckingGame.owner v = ownCheckingGame.player → ownCheckingGame.check v w) :=
    loop.every_mono loop.every_true (fun _ _ _ _ own => own)
  dsimp only [loop] at all
  simp only [ThresholdGame.repetitionValue, if_pos all]
  rfl

/-- 相手に悪いleafの出口がある例でも、停止条件だけから有限終局用の反証方策を作れる。 -/
theorem bad_leaf_exit_has_finite_refutation (root : Bool) :
    ∃ lost, Nonempty (escapeGame.RefutationRegion lost) ∧ lost root :=
  escapeGame.stopped_outside_refutation ThresholdGame.RankedRegion.empty
    CompletenessExamples.escape_ordinary_closed [false, true]
    (by intro v; cases v <;> simp) (fun _ => True) (fun _ _ => trivial)
    2 CompletenessExamples.escape_local_empty root (fun h => h)

theorem ordinary_positive_and_refutation_cannot_coexist :
    ¬ ∃ lost, Nonempty (ordinaryGame.RefutationRegion lost) ∧ lost () := by
  rintro ⟨lost, ⟨negative⟩, inside⟩
  exact ordinaryGame.finite_certificates_disjoint ordinaryRegion negative [()] (by simp)
    () (Or.inr trivial) inside

end PetaProof.FinitePayoffExamples
