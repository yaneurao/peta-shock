import PetaProof.SharedRankFamily
import PetaProof.DenseWitnessIndex

/-! 代表閾値の配列は両視点について先に構築し、頂点の分配中は参照だけを行う。 -/
namespace PetaProof.ThresholdGame.SharedRankFamily

universe u
variable {n : Nat} {E : Type u} {G : ThresholdGame (Fin n)}
variable {ctx : G.QueueContext E} {otherCore : Fin n → Bool}

structure WitnessIndices (ctx : G.QueueContext E) (otherCore : Fin n → Bool) where
  own : Array Nat
  opponent : Array Nat
  own_correct : ∀ query, 0 < query → query ≤ G.mate →
    own[query.toNat]? = some (ctx.witnessLevel query).toNat
  opponent_correct : ∀ query, 0 < query → query ≤ G.mate →
    opponent[query.toNat]? = some ((ctx.opposite otherCore).witnessLevel query).toNat

def buildWitnessIndices : WitnessIndices ctx otherCore where
  own := ctx.witnessIndex
  opponent := (ctx.opposite otherCore).witnessIndex
  own_correct := ctx.witnessIndex_eq
  opponent_correct := (ctx.opposite otherCore).witnessIndex_eq

variable (shared : SharedRankFamily ctx otherCore)

/-- 参照表を明示的な引数にすることで、頂点ごとの再構築を避ける。 -/
def indexedTarget (indices : WitnessIndices ctx otherCore) (vertex : Fin n) : Option Key :=
  if 0 < shared.value vertex then
    some (false, ((indices.own[(shared.value vertex).toNat]?).getD 0 : Int))
  else if -G.mate < shared.value vertex then
    some (true, ((indices.opponent[(1 - shared.value vertex).toNat]?).getD 0 : Int))
  else none

theorem indexedTarget_eq (indices : WitnessIndices ctx otherCore) (vertex : Fin n) :
    shared.indexedTarget indices vertex = shared.target vertex := by
  classical
  by_cases positive : 0 < shared.value vertex
  · have cap := (shared.bounded vertex).2
    have level := (ctx.witnessLevel_spec (shared.value vertex) positive cap).2.1.1
    simp [indexedTarget, target, positive, indices.own_correct _ positive cap,
      Int.toNat_of_nonneg (Int.le_of_lt level)]
  · by_cases better : -G.mate < shared.value vertex
    · have queryPositive : 0 < 1 - shared.value vertex := by omega
      have cap : 1 - shared.value vertex ≤ G.mate := by omega
      have level := ((ctx.opposite otherCore).witnessLevel_spec (1 - shared.value vertex)
        queryPositive cap).2.1.1
      simp [indexedTarget, target, positive, better,
        indices.opponent_correct _ queryPositive cap,
        Int.toNat_of_nonneg (Int.le_of_lt level)]
    · simp [indexedTarget, target, positive, better]

theorem buildWitnessIndices_sizes :
    (buildWitnessIndices (ctx := ctx) (otherCore := otherCore)).own.size = G.mate.toNat + 1 ∧
    (buildWitnessIndices (ctx := ctx) (otherCore := otherCore)).opponent.size = G.mate.toNat + 1 := by
  exact ⟨ctx.witnessIndex_size, (ctx.opposite otherCore).witnessIndex_size⟩

end PetaProof.ThresholdGame.SharedRankFamily
