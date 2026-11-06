import PetaProof.ArenaEncoding
import PetaProof.QueueThresholdWitness
import PetaProof.FiniteResidual

/-! 元局面に成功・失敗の二IDを足し、有限出辺と王手Boolから吸収ゲームを作る。 -/
namespace PetaProof.ThresholdGame

variable {n : Nat} {G : ThresholdGame (Fin n)}

def absorbedEncode : AbsorbedState (Fin n) → Fin (n + 2)
  | .node v => ⟨v.val, by have := v.isLt; omega⟩
  | .success => ⟨n, by omega⟩
  | .failure => ⟨n + 1, by omega⟩

def absorbedDecode (v : Fin (n + 2)) : AbsorbedState (Fin n) :=
  if original : v.val < n then .node ⟨v.val, original⟩
  else if v.val = n then .success else .failure

theorem absorbed_left (v : AbsorbedState (Fin n)) : absorbedDecode (absorbedEncode v) = v := by
  cases v with
  | node v => simp [absorbedDecode, absorbedEncode, v.isLt]
  | success => simp [absorbedDecode, absorbedEncode]
  | failure => simp [absorbedDecode, absorbedEncode]

theorem absorbed_right (v : Fin (n + 2)) : absorbedEncode (absorbedDecode v) = v := by
  unfold absorbedDecode
  split
  · exact Fin.ext rfl
  · split
    · apply Fin.ext
      change n = v.val
      omega
    · apply Fin.ext
      have := v.isLt
      simp only [absorbedEncode]
      omega

def finiteAbsorbedArena (G : ThresholdGame (Fin n)) : HistoryArena (Fin (n + 2)) where
  edge := fun v w => G.absorbedArena.edge (absorbedDecode v) (absorbedDecode w)
  owner := fun v => G.absorbedArena.owner (absorbedDecode v)
  player := G.player
  bad := fun v w => G.absorbedArena.bad (absorbedDecode v) (absorbedDecode w)
  moves_exist := by
    intro v
    obtain ⟨w, edge⟩ := G.absorbedArena.moves_exist (absorbedDecode v)
    exact ⟨absorbedEncode w, by simpa only [absorbed_left] using edge⟩

def absorbedEncoding (G : ThresholdGame (Fin n)) : HistoryArena.Encoding G.absorbedArena G.finiteAbsorbedArena where
  encode := absorbedEncode
  decode := absorbedDecode
  left := absorbed_left
  right := absorbed_right
  edges := by intro v w; simp [finiteAbsorbedArena, absorbed_left]
  owners := by intro v; simp [finiteAbsorbedArena, absorbed_left, absorbedArena]
  bad := by intro v w; simp [finiteAbsorbedArena, absorbed_left]

namespace QueueContext

universe u
variable {E : Type u} (ctx : G.QueueContext E)

def absorbedNext (v : Fin (n + 2)) : List (Fin (n + 2)) :=
  match absorbedDecode v with
  | .node original => (ctx.indexed.outgoing original).map (fun e => absorbedEncode (G.encodeMove (ctx.indexed.move e)))
  | _ => [v]

theorem absorbedNext_correct (v w : Fin (n + 2)) :
    w ∈ ctx.absorbedNext v ↔ G.finiteAbsorbedArena.edge v w := by
  change w ∈ ctx.absorbedNext v ↔ G.absorbedArena.edge (absorbedDecode v) (absorbedDecode w)
  unfold absorbedNext
  cases source : absorbedDecode v with
  | node original =>
    change w ∈ (ctx.indexed.outgoing original).map
      (fun e => absorbedEncode (G.encodeMove (ctx.indexed.move e))) ↔
        G.absorbedArena.edge (.node original) (absorbedDecode w)
    rw [G.absorbed_edge_iff]
    constructor
    · intro member
      obtain ⟨e, listed, same⟩ := List.mem_map.mp member
      have decoded := congrArg absorbedDecode same
      rw [absorbed_left] at decoded
      exact ⟨ctx.indexed.move e, ctx.indexed.legal original e listed, decoded⟩
    · rintro ⟨move, legal, same⟩
      obtain ⟨e, listed, selected⟩ := ctx.indexed.covers original move legal
      apply List.mem_map.mpr
      exact ⟨e, listed, by rw [selected, same, absorbed_right]⟩
  | success =>
    change w ∈ [v] ↔ G.absorbedArena.edge .success (absorbedDecode w)
    change w ∈ [v] ↔ absorbedDecode w = .success
    constructor
    · intro member
      have same : w = v := by simpa using member
      simpa only [same] using source
    · intro same
      have equal := congrArg absorbedEncode (same.trans source.symm)
      simpa only [absorbed_right, List.mem_singleton] using equal
  | failure =>
    change w ∈ [v] ↔ absorbedDecode w = .failure
    constructor
    · intro member
      have same : w = v := by simpa using member
      simpa only [same] using source
    · intro same
      have equal := congrArg absorbedEncode (same.trans source.symm)
      simpa only [absorbed_right, List.mem_singleton] using equal

def absorbedBad (v w : Fin (n + 2)) : Bool :=
  match absorbedDecode v, absorbedDecode w with
  | .node a, .node b => decide (G.owner a ≠ G.player) && !ctx.checked a b
  | .failure, .failure => true
  | _, _ => false

theorem absorbedBad_correct (v w : Fin (n + 2)) :
    ctx.absorbedBad v w = true ↔ G.finiteAbsorbedArena.bad v w := by
  have check (a b : Fin n) : ctx.checked a b = false ↔ ¬ G.check a b := by
    have correct := ctx.check_correct a b
    cases flag : ctx.checked a b <;> simp_all
  cases a : absorbedDecode v <;> cases b : absorbedDecode w <;>
    simp [absorbedBad, finiteAbsorbedArena, absorbedArena, a, b, check]

def absorbedInput : HistoryArena.DeletionInput G.finiteAbsorbedArena where
  next := ctx.absorbedNext
  edges := ctx.absorbedNext_correct
  bad := ctx.absorbedBad
  bad_correct := ctx.absorbedBad_correct

end QueueContext
end PetaProof.ThresholdGame
