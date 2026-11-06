import PetaProof.DeletionFifoIndex
import PetaProof.Determinacy

/-! 確定集合のBool表から有限残余を作る。元IDを保ち、除外IDは反証用の無害な埋草にする。 -/
namespace PetaProof.HistoryArena.DeletionInput

variable {n : Nat} {A : HistoryArena (Fin n)} (input : DeletionInput A)

/-- 元のIDを保つ。残す頂点の辺だけをfilterし、除外頂点には自己辺を置く。 -/
def residualNext (keep : Fin n → Bool) (v : Fin n) : List (Fin n) :=
  if keep v then (input.next v).filter keep else [v]

def residualArena (keep : Fin n → Bool) (trap : A.Trap (fun v => keep v = true)) : HistoryArena (Fin n) where
  edge := fun v w => w ∈ input.residualNext keep v
  owner := A.owner
  player := A.player
  bad := fun v w => (if keep v then input.bad v w else true) = true
  moves_exist := by
    intro v
    by_cases retained : keep v = true
    · obtain ⟨w, edge, inside⟩ : ∃ w, A.edge v w ∧ keep w = true := by
        by_cases own : A.owner v = A.player
        · obtain ⟨w, edge⟩ := A.moves_exist v
          exact ⟨w, edge, trap.own_closed v w retained own edge⟩
        · exact trap.other_move v retained own
      exact ⟨w, by simp [residualNext, retained, (input.edges v w).mpr edge, inside]⟩
    · have gone : keep v = false := Bool.eq_false_iff.mpr retained
      exact ⟨v, by simp [residualNext, gone]⟩

variable (keep : Fin n → Bool) (trap : A.Trap (fun v => keep v = true))

def residualInput : DeletionInput (input.residualArena keep trap) where
  next := input.residualNext keep
  edges := fun _ _ => Iff.rfl
  bad := fun v w => if keep v then input.bad v w else true
  bad_correct := fun _ _ => Iff.rfl

theorem residual_edge (v w : Fin n) (retained : keep v = true) :
    (input.residualArena keep trap).edge v w ↔ A.edge v w ∧ keep w = true := by
  simp [residualArena, residualNext, retained, input.edges v w]

theorem residual_bad (v w : Fin n) (retained : keep v = true) :
    (input.residualArena keep trap).bad v w ↔ A.bad v w := by
  simp [residualArena, retained, input.bad_correct v w]

/-- 除外IDを自己辺で全域化しても、偽の安全集合は作らない。 -/
theorem removed_cannot_stay (current : Fin n → Prop) (v : Fin n) (gone : keep v = false) :
    ¬ (input.residualArena keep trap).StayGood current v := by
  have self : (input.residualArena keep trap).edge v v := by simp [residualArena, residualNext, gone]
  have bad (w : Fin n) : (input.residualArena keep trap).bad v w := by simp [residualArena, gone]
  intro stays
  by_cases own : A.owner v = A.player
  · obtain ⟨w, _, nonbad, _⟩ := stays.1 own
    exact nonbad (bad w)
  · exact (stays.2 own v self).1 (bad v)

theorem residual_safe_restrict (current : Fin n → Prop)
    (safe : (input.residualArena keep trap).GoodSafeSet current)
    {won : Fin n → Prop} (same : ∀ v, keep v = true ↔ ¬ won v)
    (ordinary : A.OrdinaryClosed won) :
    (A.complementTrap ordinary).restricted.GoodSafeSet (fun v => current v.val) := by
  intro v inside
  have retained := (same v.val).mpr v.property
  have stays := safe v.val inside
  constructor
  · intro own
    obtain ⟨w, edge, nonbad, alive⟩ := stays.1 own
    obtain ⟨legal, kept⟩ := (input.residual_edge keep trap v.val w retained).mp edge
    exact ⟨⟨w, (same w).mp kept⟩, legal,
      fun bad => nonbad ((input.residual_bad keep trap v.val w retained).mpr bad), alive⟩
  · intro other w edge
    have childKept := (same w.val).mpr w.property
    have good := stays.2 other w.val ((input.residual_edge keep trap v.val w.val retained).mpr ⟨edge, childKept⟩)
    exact ⟨fun bad => good.1 ((input.residual_bad keep trap v.val w.val retained).mpr bad), good.2⟩

theorem residual_safe_empty {won : Fin n → Prop} (same : ∀ v, keep v = true ↔ ¬ won v)
    (policy : A.RankedPolicy won) (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won)
    (current : Fin n → Prop) (safe : (input.residualArena keep trap).GoodSafeSet current) :
    ∀ v, ¬ current v := by
  intro v alive
  by_cases retained : keep v = true
  · have restricted := input.residual_safe_restrict keep trap current safe same ordinary
    exact A.residual_safe_empty policy maximal ordinary restricted ⟨v, (same v).mp retained⟩ alive
  · exact input.removed_cannot_stay keep trap current v (Bool.eq_false_iff.mpr retained) (safe v alive)

theorem residual_empty_at_size {won : Fin n → Prop} (same : ∀ v, keep v = true ↔ ¬ won v)
    (policy : A.RankedPolicy won) (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won) :
    ∀ v, ¬ (input.residualArena keep trap).goodIter n v := by
  obtain ⟨k, bound, stable⟩ := (input.residualArena keep trap).goodIter_stable_exists (List.finRange n)
    (CoreEnumeration.finRange_covers n)
  have empty := input.residual_safe_empty keep trap same policy maximal ordinary _ stable
  have bounded : k ≤ n := by simpa using bound
  intro v alive
  exact empty v (goodIter_earlier n k bounded v alive)

theorem residual_built_success {won : Fin n → Prop} (same : ∀ v, keep v = true ↔ ¬ won v)
    (policy : A.RankedPolicy won) (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won) :
    (input.residualInput keep trap).builtCounter.isSome = true := by
  apply ((input.residualInput keep trap).builtCounter_iff).mpr
  exact fun v => (input.residualArena keep trap).empty_excludes_history n
    (input.residual_empty_at_size keep trap same policy maximal ordinary) v

end PetaProof.HistoryArena.DeletionInput

namespace PetaProof.HistoryArena

variable {n : Nat} {A : HistoryArena (Fin n)} {won : Fin n → Prop}

theorem solved_ordinary {V : Type u} {B : HistoryArena V} {region : V → Prop}
    (solved : ∃ _policy : B.RankedPolicy region, B.PolicyMaximal region) :
    B.OrdinaryClosed region := by
  obtain ⟨policy, maximal⟩ := solved
  exact B.maximal_policy_ordinary policy maximal

def flagComplementTrap (keep : Fin n → Bool) (same : ∀ v, keep v = true ↔ ¬ won v)
    (ordinary : A.OrdinaryClosed won) : A.Trap (fun v => keep v = true) where
  own_closed := fun v w outside own edge => (same w).mpr
    ((A.complementTrap ordinary).own_closed v w ((same v).mp outside) own edge)
  other_move := by
    intro v outside other
    obtain ⟨w, edge, inside⟩ := (A.complementTrap ordinary).other_move v ((same v).mp outside) other
    exact ⟨w, edge, (same w).mpr inside⟩

namespace DeletionInput

variable (input : DeletionInput A) (keep : Fin n → Bool)
variable (same : ∀ v, keep v = true ↔ ¬ won v) (ordinary : A.OrdinaryClosed won)
variable (trap : A.Trap (fun v => keep v = true))

/-- 自分番のresponse欄は使わないので自分自身で埋め、相手番だけ実計算の応手を戻す。 -/
def residualResponse (counter : (input.residualArena keep trap).Counterstrategy)
    (v : {v // ¬ won v}) : {v // ¬ won v} :=
  if own : A.owner v.val = A.player then v else
    ⟨counter.response v.val, (same _).mp
      ((input.residual_edge keep trap _ _ ((same v.val).mpr v.property)).mp (counter.legal v.val own)).2⟩

def liftResidualCounter (counter : (input.residualArena keep trap).Counterstrategy) :
    (A.complementTrap ordinary).restricted.Counterstrategy where
  response := input.residualResponse keep same trap counter
  legal := by
    intro v other
    change A.owner v.val ≠ A.player at other
    change A.edge v.val ((input.residualResponse keep same trap counter v).val)
    simp only [residualResponse, dif_neg other]
    exact ((input.residual_edge keep trap _ _ ((same v.val).mpr v.property)).mp (counter.legal v.val other)).1
  ranking := {
    rank := fun v => counter.ranking.rank v.val
    strict_good := by
      intro v w follows nonbad
      have retained := (same v.val).mpr v.property
      have childKept := (same w.val).mpr w.property
      have edge := (input.residual_edge keep trap v.val w.val retained).mpr ⟨follows.1, childKept⟩
      have selected : A.owner v.val ≠ A.player → w.val = counter.response v.val := by
        intro other
        have selected := congrArg Subtype.val (follows.2 other)
        simpa only [residualResponse, dif_neg other] using selected
      exact counter.ranking.strict_good v.val w.val ⟨edge, selected⟩
        (fun bad => nonbad ((input.residual_bad keep trap v.val w.val retained).mp bad))
  }

variable (solved : ∃ _policy : A.RankedPolicy won, A.PolicyMaximal won)

theorem solved_residual_success :
    (input.residualInput keep (flagComplementTrap keep same (solved_ordinary solved))).builtCounter.isSome = true := by
  obtain ⟨policy, maximal⟩ := solved
  exact input.residual_built_success keep _ same policy maximal (solved_ordinary ⟨policy, maximal⟩)

/-- 最大性の証明はPropとしてのみ使い、具体的な順位や応手は有限FIFOの返却値から取得する。 -/
def solvedResidualCounter :
    (input.residualArena keep (flagComplementTrap keep same (solved_ordinary solved))).Counterstrategy :=
  ((input.residualInput keep (flagComplementTrap keep same (solved_ordinary solved))).builtCounter).get
    (input.solved_residual_success keep same solved)

def solvedComplementCounter : (A.complementTrap (solved_ordinary solved)).restricted.Counterstrategy :=
  input.liftResidualCounter keep same (solved_ordinary solved) _ (input.solvedResidualCounter keep same solved)

include input keep same solved in
theorem solvedComplement_refutes (v : Fin n) (outside : ¬ won v) : ¬ A.HistoryWinning v :=
  (A.complementTrap (solved_ordinary solved)).counter_refutes_original
    (input.solvedComplementCounter keep same solved) v outside

end PetaProof.HistoryArena.DeletionInput
