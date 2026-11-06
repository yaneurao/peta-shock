import PetaProof.IncrementalBoundary
import PetaProof.ThresholdChange

/-! 影響領域外の同一性は、局所方程式ではなく四回出現ゲームの保証で示す。 -/
namespace PetaProof.IncrementalBoundary

universe u
variable {V : Type u} {G H : ThresholdGame V} {outside : V → Prop}

structure Agreement (G H : ThresholdGame V) (outside : V → Prop) : Prop where
  legal : ∀ vertex, outside vertex → ∀ move, G.legal vertex move ↔ H.legal vertex move
  owner : ∀ vertex, outside vertex → G.owner vertex = H.owner vertex
  check : ∀ vertex, outside vertex → ∀ child, G.check vertex child ↔ H.check vertex child
  player : G.player = H.player
  threshold : G.threshold = H.threshold
  closed : ∀ vertex child, outside vertex → G.legal vertex (.node child) → outside child

namespace Agreement

variable (agreement : Agreement G H outside)
include agreement

def symm : Agreement H G outside where
  legal := fun v inside m => (agreement.legal v inside m).symm
  owner := fun v inside => (agreement.owner v inside).symm
  check := fun v inside w => (agreement.check v inside w).symm
  player := agreement.player.symm
  threshold := agreement.threshold.symm
  closed := fun v w inside edge => agreement.closed v w inside ((agreement.legal v inside _).mpr edge)

/-- 閾値と視点を変えても、更新されない部分の対応は再利用できる。 -/
def retune (level : Int) (positive : 0 < level) (left : level ≤ G.mate) (right : level ≤ H.mate) :
    Agreement (G.retune level positive left) (H.retune level positive right) outside where
  legal := agreement.legal
  owner := agreement.owner
  check := agreement.check
  player := agreement.player
  threshold := rfl
  closed := agreement.closed

def opposite : Agreement G.opposite H.opposite outside where
  legal := fun vertex inside move => agreement.legal vertex inside move.negate
  owner := agreement.owner
  check := agreement.check
  player := congrArg Bool.not agreement.player
  threshold := agreement.threshold
  closed := agreement.closed

theorem follows_old (choice : V → Move V) (vertex : V) (inside : outside vertex) (move : Move V)
    (follows : H.Follows choice vertex move) : G.Follows choice vertex move := by
  refine ⟨(agreement.legal vertex inside move).mpr follows.1, ?_⟩
  intro own
  apply follows.2
  rw [← agreement.owner vertex inside, ← agreement.player]
  exact own

/-- 順位も選択手も変更せず、前向きに閉じた外側へ保証領域を制限する。 -/
def transport {won : V → Prop} (region : G.RankedRegion won) :
    H.RankedRegion (fun vertex => won vertex ∧ outside vertex) where
  choice := region.choice
  rank := region.rank
  stage := region.stage
  rank_bound := fun v inside => region.rank_bound v inside.1
  chosen_legal := by
    intro vertex inside own
    apply (agreement.legal vertex inside.2 _).mp
    apply region.chosen_legal vertex inside.1
    rw [agreement.owner vertex inside.2, agreement.player]
    exact own
  closed := by
    intro vertex inside move follows
    have original := agreement.follows_old region.choice vertex inside.2 move follows
    have result := region.closed vertex inside.1 move original
    cases move with
    | leaf score => simpa only [agreement.threshold] using result
    | node child => exact ⟨result, agreement.closed vertex child inside.2 original.1⟩
  decreasing := fun vertex child inside follows =>
    region.decreasing vertex child inside.1 (agreement.follows_old region.choice vertex inside.2 _ follows)
  opponent_strict := by
    intro vertex child inside follows other quiet
    apply region.opponent_strict vertex child inside.1
      (agreement.follows_old region.choice vertex inside.2 _ follows)
    · intro own
      apply other
      rw [← agreement.owner vertex inside.2, ← agreement.player]
      exact own
    · intro check
      exact quiet ((agreement.check vertex inside.2 child).mp check)

theorem fourfold_forward [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (inside : outside root) (winning : G.FourfoldWinning root) : H.FourfoldWinning root := by
  rcases G.finite_certificate_dichotomy vertices covered root with positive | negative
  · obtain ⟨won, ⟨region⟩, member⟩ := positive
    exact (agreement.transport region).fourfold_winning root ⟨member, inside⟩
  · obtain ⟨lost, ⟨region⟩, member⟩ := negative
    exact False.elim (region.not_fourfold_winning vertices covered root member winning)

/-- 領域外のrootでは、履歴依存の全戦略を許す四回出現の勝敗が同じ。 -/
theorem fourfold_iff [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (inside : outside root) : G.FourfoldWinning root ↔ H.FourfoldWinning root :=
  ⟨agreement.fourfold_forward vertices covered root inside,
    agreement.symm.fourfold_forward vertices covered root inside⟩

end Agreement
end PetaProof.IncrementalBoundary
