import PetaProof.Determinacy

/-! 有限IDへの全単射で、順位付き保証領域とその最大性を移す。履歴を列挙しない。 -/
namespace PetaProof.HistoryArena

universe u v
variable {V : Type u} {W : Type v} {A : HistoryArena V} {B : HistoryArena W}

structure Encoding (A : HistoryArena V) (B : HistoryArena W) where
  encode : V → W
  decode : W → V
  left : ∀ x, decode (encode x) = x
  right : ∀ x, encode (decode x) = x
  edges : ∀ x y, B.edge (encode x) (encode y) ↔ A.edge x y
  owners : ∀ x, B.owner (encode x) = B.player ↔ A.owner x = A.player
  bad : ∀ x y, B.bad (encode x) (encode y) ↔ A.bad x y

namespace Encoding

variable (code : Encoding A B)

def symm : Encoding B A where
  encode := code.decode
  decode := code.encode
  left := code.right
  right := code.left
  edges := by intro x y; rw [← code.edges, code.right, code.right]
  owners := by intro x; rw [← code.owners, code.right]
  bad := by intro x y; rw [← code.bad, code.right, code.right]

def pullPolicy {won : W → Prop} (policy : B.RankedPolicy won) :
    A.RankedPolicy (fun x => won (code.encode x)) := by
  let choice := fun x => code.decode (policy.choice (code.encode x))
  have follows (x y : V) (old : A.FollowsChoice choice x y) :
      B.FollowsChoice policy.choice (code.encode x) (code.encode y) := by
    refine ⟨(code.edges x y).mpr old.1, ?_⟩
    intro own
    have selected := congrArg code.encode (old.2 ((code.owners x).mp own))
    simpa only [choice, code.right] using selected
  exact {
    choice := choice
    legal := by
      intro x own
      apply (code.edges x (choice x)).mp
      change B.edge (code.encode x) (code.encode (code.decode (policy.choice (code.encode x))))
      rw [code.right]
      exact policy.legal _ ((code.owners x).mpr own)
    rank := fun x => policy.rank (code.encode x)
    ceiling := policy.ceiling
    bounded := fun x inside => policy.bounded _ inside
    closed := fun x y inside old => policy.closed _ _ inside (follows x y old)
    decreasing := fun x y inside old => policy.decreasing _ _ inside (follows x y old)
    strict_bad := fun x y inside old bad => policy.strict_bad _ _ inside (follows x y old) ((code.bad x y).mpr bad)
  }

theorem push_maximal {won : V → Prop} (maximal : A.PolicyMaximal won) :
    B.PolicyMaximal (fun x => won (code.decode x)) := by
  intro other policy x inside
  have bound := maximal (fun v => other (code.encode v)) (code.pullPolicy policy) (code.decode x)
  apply bound
  simpa only [code.right] using inside

theorem push_solved {won : V → Prop} (solved : ∃ _policy : A.RankedPolicy won, A.PolicyMaximal won) :
    ∃ _policy : B.RankedPolicy (fun x => won (code.decode x)),
      B.PolicyMaximal (fun x => won (code.decode x)) := by
  obtain ⟨policy, maximal⟩ := solved
  exact ⟨code.symm.pullPolicy policy, code.push_maximal maximal⟩

def pullCounter (counter : B.Counterstrategy) : A.Counterstrategy := by
  let response := fun x => code.decode (counter.response (code.encode x))
  have follows (x y : V) (old : A.FollowsResponse response x y) :
      B.FollowsResponse counter.response (code.encode x) (code.encode y) := by
    refine ⟨(code.edges x y).mpr old.1, ?_⟩
    intro other
    have originalOther : A.owner x ≠ A.player := fun own => other ((code.owners x).mpr own)
    have selected := congrArg code.encode (old.2 originalOther)
    simpa only [response, code.right] using selected
  exact {
    response := response
    legal := by
      intro x other
      apply (code.edges x (response x)).mp
      change B.edge (code.encode x) (code.encode (code.decode (counter.response (code.encode x))))
      rw [code.right]
      exact counter.legal _ (fun own => other ((code.owners x).mp own))
    ranking := {
      rank := fun x => counter.ranking.rank (code.encode x)
      strict_good := fun x y old good => counter.ranking.strict_good _ _ (follows x y old)
        (fun bad => good ((code.bad x y).mp bad))
    } }

def complement {won : V → Prop} (ordinary : A.OrdinaryClosed won)
    (otherOrdinary : B.OrdinaryClosed (fun x => won (code.decode x))) :
    Encoding (A.complementTrap ordinary).restricted (B.complementTrap otherOrdinary).restricted where
  encode := fun x => ⟨code.encode x.val, by simpa only [code.left] using x.property⟩
  decode := fun x => ⟨code.decode x.val, x.property⟩
  left := fun x => Subtype.ext (code.left x.val)
  right := fun x => Subtype.ext (code.right x.val)
  edges := fun x y => code.edges x.val y.val
  owners := fun x => code.owners x.val
  bad := fun x y => code.bad x.val y.val

end Encoding
end PetaProof.HistoryArena
