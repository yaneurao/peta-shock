import PetaProof.FiniteAbsorption

/-! 実phaseの返却Bool表から吸収状態付き有限残余を作り、反証生成器へ渡す。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u
variable {n : Nat} {E : Type u} {G : ThresholdGame (Fin n)} (ctx : G.QueueContext E)

def absorbedKeep (_ctx : G.QueueContext E) (state : PropagationState (Fin n) E) (v : Fin (n + 2)) : Bool :=
  match absorbedDecode v with
  | .node original => !(state.counters original).admitted
  | .success => false
  | .failure => true

theorem absorbedKeep_correct (state : PropagationState (Fin n) E) (v : Fin (n + 2)) :
    ctx.absorbedKeep state v = true ↔ ¬ extendWon state.won (absorbedDecode v) := by
  cases shape : absorbedDecode v with
  | node original =>
    cases flag : (state.counters original).admitted <;>
      simp [absorbedKeep, shape, extendWon, PropagationState.won, flag]
  | success => simp [absorbedKeep, shape, extendWon]
  | failure => simp [absorbedKeep, shape, extendWon]

def stateResidualInput (state : PropagationState (Fin n) E)
    (solved : ∃ _policy : G.finiteAbsorbedArena.RankedPolicy
      (fun v => extendWon state.won (absorbedDecode v)),
      G.finiteAbsorbedArena.PolicyMaximal (fun v => extendWon state.won (absorbedDecode v))) :=
  ctx.absorbedInput.residualInput (ctx.absorbedKeep state)
    (HistoryArena.flagComplementTrap _ (ctx.absorbedKeep_correct state) (HistoryArena.solved_ordinary solved))

theorem stateResidual_success (state : PropagationState (Fin n) E)
    (solved : ∃ _policy : G.finiteAbsorbedArena.RankedPolicy
      (fun v => extendWon state.won (absorbedDecode v)),
      G.finiteAbsorbedArena.PolicyMaximal (fun v => extendWon state.won (absorbedDecode v))) :
    (ctx.stateResidualInput state solved).builtCounter.isSome = true :=
  ctx.absorbedInput.solved_residual_success (ctx.absorbedKeep state) (ctx.absorbedKeep_correct state) solved

variable [DecidableEq E]

theorem phase_absorbed_solved (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    let low := G.retune bound positive (Int.le_trans lower G.bounded)
    let final := ctx.phase bound positive (Int.le_trans lower G.bounded) state
    ∃ _policy : low.absorbedArena.RankedPolicy (extendWon final.won),
      low.absorbedArena.PolicyMaximal (extendWon final.won) := by
  obtain ⟨certificate⟩ := certified
  obtain ⟨regions⟩ := ctx.phase_regions state certificate boundary covers bound positive lower
  let low := G.retune bound positive (Int.le_trans lower G.bounded)
  have maximal := low.exact_region_lift_maximal ctx.vertices ctx.covered
    (fun v => regions.exact ctx.vertices ctx.covered v)
  exact ⟨low.liftRankedRegion regions.positive, maximal⟩

theorem phase_finite_solved (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    let low := G.retune bound positive (Int.le_trans lower G.bounded)
    let final := ctx.phase bound positive (Int.le_trans lower G.bounded) state
    ∃ _policy : low.finiteAbsorbedArena.RankedPolicy (fun v => extendWon final.won (absorbedDecode v)),
      low.finiteAbsorbedArena.PolicyMaximal (fun v => extendWon final.won (absorbedDecode v)) :=
  (G.retune bound positive _).absorbedEncoding.push_solved
    (ctx.phase_absorbed_solved state certified boundary covers bound positive lower)

def phaseResidualInput (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :=
  let low := ctx.atLevel bound positive (Int.le_trans lower G.bounded)
  let final := ctx.phase bound positive (Int.le_trans lower G.bounded) state
  low.stateResidualInput final (ctx.phase_finite_solved state certified boundary covers bound positive lower)

theorem phaseResidual_success (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    (ctx.phaseResidualInput state certified boundary covers bound positive lower).builtCounter.isSome = true :=
  (ctx.atLevel bound positive _).stateResidual_success
    (ctx.phase bound positive (Int.le_trans lower G.bounded) state)
    (ctx.phase_finite_solved state certified boundary covers bound positive lower)

/-- 閾値走査の一phaseから、有限ID版の補集合を覆う実計算の反証証拠まで接続する。 -/
def phaseComplementCounter (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :=
  let low := ctx.atLevel bound positive (Int.le_trans lower G.bounded)
  let final := ctx.phase bound positive (Int.le_trans lower G.bounded) state
  low.absorbedInput.solvedComplementCounter (low.absorbedKeep final) (low.absorbedKeep_correct final)
    (ctx.phase_finite_solved state certified boundary covers bound positive lower)

/-- ID変換を逆に辿り、元の吸収ゲームの補集合上の証拠へ戻す。 -/
def phaseOriginalCounter (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :=
  let low := G.retune bound positive (Int.le_trans lower G.bounded)
  let final := ctx.phase bound positive (Int.le_trans lower G.bounded) state
  let ordinary := HistoryArena.solved_ordinary
    (ctx.phase_absorbed_solved state certified boundary covers bound positive lower)
  let otherOrdinary := HistoryArena.solved_ordinary
    (ctx.phase_finite_solved state certified boundary covers bound positive lower)
  (low.absorbedEncoding.complement (won := extendWon final.won) ordinary otherOrdinary).pullCounter
    (ctx.phaseComplementCounter state certified boundary covers bound positive lower)

theorem phaseOriginal_refutes (state : PropagationState (Fin n) E)
    (certified : Nonempty (StateCertificate ctx.indexed state)) (boundary : ctx.Boundary state)
    (covers : ∀ v, CyclicVertex G.OpponentChecking v → ctx.core v = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold)
    (v : Fin n) (outside : ¬ (ctx.phase bound positive (Int.le_trans lower G.bounded) state).won v) :
    ¬ (G.retune bound positive (Int.le_trans lower G.bounded)).FourfoldWinning v := by
  let low := G.retune bound positive (Int.le_trans lower G.bounded)
  let ordinary := HistoryArena.solved_ordinary
    (ctx.phase_absorbed_solved state certified boundary covers bound positive lower)
  have anti := (low.absorbedArena.complementTrap ordinary).counter_refutes_original
    (ctx.phaseOriginalCounter state certified boundary covers bound positive lower) (.node v) outside
  intro winning
  exact anti ((low.fourfold_winning_iff_absorbed_history ctx.vertices ctx.covered v).mp winning)

end PetaProof.ThresholdGame.QueueContext
