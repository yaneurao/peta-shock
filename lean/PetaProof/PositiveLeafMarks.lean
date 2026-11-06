import PetaProof.MainRunAccounting

/-! 入力辺を一回走査して、正のleaf評価値の存在を有限Bool配列へ記録する。 -/
namespace PetaProof.PositiveLeafMarks

universe u
variable {E : Type u}

def oneHit (scoreOf : E → Option Int) (edge : E) (index : Nat) : Prop :=
  ∃ score, scoreOf edge = some score ∧ 0 < score ∧ score.toNat = index

def Hit (scoreOf : E → Option Int) : List E → Nat → Prop
  | [], _ => False
  | edge :: rest, index => oneHit scoreOf edge index ∨ Hit scoreOf rest index

def markOne (scoreOf : E → Option Int) (flags : Array Bool) (edge : E) : Array Bool :=
  match scoreOf edge with
  | none => flags
  | some score => if 0 < score then flags.setIfInBounds score.toNat true else flags

theorem markOne_size (scoreOf : E → Option Int) (flags : Array Bool) (edge : E) :
    (markOne scoreOf flags edge).size = flags.size := by
  cases found : scoreOf edge with
  | none => simp [markOne, found]
  | some score => by_cases positive : 0 < score <;> simp [markOne, found, positive]

theorem markOne_get (scoreOf : E → Option Int) (flags : Array Bool) (edge : E)
    (index : Nat) (valid : index < flags.size) :
    (markOne scoreOf flags edge)[index]? = some true ↔ flags[index]? = some true ∨ oneHit scoreOf edge index := by
  cases found : scoreOf edge with
  | none => simp [markOne, found, oneHit]
  | some score =>
    by_cases positive : 0 < score
    · by_cases same : score.toNat = index
      · simp [markOne, found, positive, Array.getElem?_setIfInBounds, same, valid, oneHit]
      · simp [markOne, found, positive, Array.getElem?_setIfInBounds, same, oneHit]
    · simp [markOne, found, positive, oneHit]

def markAll (scoreOf : E → Option Int) : List E → Array Bool → Array Bool
  | [], flags => flags
  | edge :: rest, flags => markAll scoreOf rest (markOne scoreOf flags edge)

theorem markAll_size (scoreOf : E → Option Int) (edges : List E) (flags : Array Bool) :
    (markAll scoreOf edges flags).size = flags.size := by
  induction edges generalizing flags with
  | nil => rfl
  | cons edge rest ih => simp only [markAll, ih, markOne_size]

theorem markAll_get (scoreOf : E → Option Int) (edges : List E) (flags : Array Bool)
    (index : Nat) (valid : index < flags.size) :
    (markAll scoreOf edges flags)[index]? = some true ↔ flags[index]? = some true ∨ Hit scoreOf edges index := by
  induction edges generalizing flags with
  | nil => simp [markAll, Hit]
  | cons edge rest ih =>
    rw [markAll, ih (markOne scoreOf flags edge) (by simpa only [markOne_size] using valid),
      markOne_get scoreOf flags edge index valid]
    exact or_assoc

theorem hit_mem (scoreOf : E → Option Int) (edges : List E) (index : Nat) :
    Hit scoreOf edges index ↔ ∃ edge ∈ edges, oneHit scoreOf edge index := by
  induction edges with
  | nil => simp [Hit]
  | cons edge rest ih =>
    rw [Hit, ih]
    constructor
    · rintro (first | ⟨other, member, found⟩)
      · exact ⟨edge, by simp, first⟩
      · exact ⟨other, by simp [member], found⟩
    · rintro ⟨other, member, found⟩
      rcases List.mem_cons.mp member with same | later
      · subst other; exact Or.inl found
      · exact Or.inr ⟨other, later, found⟩

def flags (scoreOf : E → Option Int) (cap : Nat) (edges : List E) : Array Bool :=
  markAll scoreOf edges (Array.replicate (cap + 1) false)

theorem flags_size (scoreOf : E → Option Int) (cap : Nat) (edges : List E) :
    (flags scoreOf cap edges).size = cap + 1 := by simp [flags, markAll_size]

theorem flags_get (scoreOf : E → Option Int) (cap : Nat) (edges : List E)
    (index : Nat) (valid : index ≤ cap) :
    (flags scoreOf cap edges)[index]? = some true ↔ ∃ edge ∈ edges, oneHit scoreOf edge index := by
  rw [flags, markAll_get scoreOf edges _ index (by simpa using (show index < cap + 1 by omega))]
  have initial : (Array.replicate (cap + 1) false)[index]? = some false := by simp [Array.getElem?_eq_getElem, valid, show index < cap + 1 by omega]
  rw [initial]
  simpa only [Bool.false_eq_true, Option.some.injEq, false_or] using hit_mem scoreOf edges index

/-- 型分岐・正値判定・範囲検査・一要素書込みのイベント数。 -/
def oneWork (scoreOf : E → Option Int) (flags : Array Bool) (edge : E) : Nat :=
  match scoreOf edge with
  | none => 1
  | some score => 2 + if 0 < score then 1 + if score.toNat < flags.size then 1 else 0 else 0

def scanWork (scoreOf : E → Option Int) : List E → Array Bool → Nat
  | [], _ => 0
  | edge :: rest, flags => oneWork scoreOf flags edge + scanWork scoreOf rest (markOne scoreOf flags edge)

theorem oneWork_bound (scoreOf : E → Option Int) (flags : Array Bool) (edge : E) : oneWork scoreOf flags edge ≤ 4 := by
  cases found : scoreOf edge with
  | none => simp [oneWork, found]
  | some score => simp only [oneWork, found]; split <;> (try split) <;> omega

theorem scanWork_bound (scoreOf : E → Option Int) (edges : List E) (flags : Array Bool) :
    scanWork scoreOf edges flags ≤ 4 * edges.length := by
  induction edges generalizing flags with
  | nil => simp [scanWork]
  | cons edge rest ih =>
    have first := oneWork_bound scoreOf flags edge
    have remaining := ih (markOne scoreOf flags edge)
    simp only [scanWork, List.length_cons]
    omega

end PetaProof.PositiveLeafMarks
