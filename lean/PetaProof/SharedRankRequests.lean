import PetaProof.IndexedRankTargets
import PetaProof.RankRequestBuckets

/-! 両視点・代表閾値の取得先を配列番号へ写し、要求表を一回の頂点走査で構築する。 -/
namespace PetaProof.ThresholdGame.SharedRankFamily

universe u
variable {n : Nat} {E : Type u} {G : ThresholdGame (Fin n)}
variable {ctx : G.QueueContext E} {otherCore : Fin n → Bool}

def keyIndex (key : Key) : Nat := 2 * key.2.toNat + if key.1 then 1 else 0

def bucketCount (G : ThresholdGame (Fin n)) : Nat := 2 * (G.mate.toNat + 1)

theorem keyIndex_bound (key : Key) (valid : ValidKey (G := G) key) : keyIndex key < bucketCount G := by
  have cast : (G.mate.toNat : Int) = G.mate := Int.toNat_of_nonneg (Int.le_of_lt G.mate_positive)
  have upper := valid.2
  have bound : key.2.toNat ≤ G.mate.toNat := by omega
  cases side : key.1 <;> simp [keyIndex, bucketCount, side] <;> omega

theorem keyIndex_injective (first second : Key) (left : 0 ≤ first.2) (right : 0 ≤ second.2)
    (same : keyIndex first = keyIndex second) : first = second := by
  obtain ⟨firstSide, firstLevel⟩ := first
  obtain ⟨secondSide, secondLevel⟩ := second
  have firstCast : (firstLevel.toNat : Int) = firstLevel := Int.toNat_of_nonneg left
  have secondCast : (secondLevel.toNat : Int) = secondLevel := Int.toNat_of_nonneg right
  cases firstSide <;> cases secondSide <;> simp [keyIndex] at same ⊢ <;> omega

variable (shared : SharedRankFamily ctx otherCore)

noncomputable def route (vertex : Fin n) : Option (Fin (bucketCount G)) :=
  match shared.target vertex with
  | none => none
  | some key => if valid : ValidKey (G := G) key then some ⟨keyIndex key, keyIndex_bound key valid⟩ else none

theorem route_some (vertex : Fin n) (key : Key) (found : shared.target vertex = some key) :
    shared.route vertex = some ⟨keyIndex key, keyIndex_bound key (shared.target_valid vertex key found)⟩ := by
  classical
  simp [route, found, shared.target_valid vertex key found]

theorem route_iff (vertex : Fin n) (key : Key) (valid : ValidKey (G := G) key) :
    shared.route vertex = some ⟨keyIndex key, keyIndex_bound key valid⟩ ↔ shared.target vertex = some key := by
  classical
  cases found : shared.target vertex with
  | none => simp [route, found]
  | some actual =>
    have actualValid := shared.target_valid vertex actual found
    rw [shared.route_some vertex actual found]
    constructor
    · intro same
      have indices := congrArg Fin.val (Option.some.inj same)
      have equal := keyIndex_injective actual key (Int.le_of_lt actualValid.1) (Int.le_of_lt valid.1) indices
      exact congrArg some equal
    · intro same
      have equal := Option.some.inj same
      subst actual
      rfl

structure Requests where
  buckets : Array (List (Fin n))
  size : buckets.size = bucketCount G
  correct : ∀ key (valid : ValidKey (G := G) key) vertex,
    vertex ∈ RankRequestBuckets.row buckets (⟨keyIndex key, keyIndex_bound key valid⟩ : Fin (bucketCount G)) ↔
      shared.target vertex = some key
  unique : ∀ key (valid : ValidKey (G := G) key),
    (RankRequestBuckets.row buckets (⟨keyIndex key, keyIndex_bound key valid⟩ : Fin (bucketCount G))).Nodup

/-- 配列から得た取得先を要求表の添字へ変換する。 -/
def indexedRoute (indices : WitnessIndices ctx otherCore) (vertex : Fin n) : Option (Fin (bucketCount G)) :=
  match shared.indexedTarget indices vertex with
  | none => none
  | some key => if valid : ValidKey (G := G) key then some ⟨keyIndex key, keyIndex_bound key valid⟩ else none

theorem indexedRoute_eq (indices : WitnessIndices ctx otherCore) (vertex : Fin n) :
    shared.indexedRoute indices vertex = shared.route vertex := by
  simp only [indexedRoute, route, shared.indexedTarget_eq indices vertex]

/-- 先頭登録だけで分配する。両視点の索引は分配前に一回ずつ構築する。 -/
noncomputable def buildRequests : Requests shared :=
  let indices := buildWitnessIndices (ctx := ctx) (otherCore := otherCore)
  { buckets := RankRequestBuckets.build (shared.indexedRoute indices) (List.finRange n)
    size := RankRequestBuckets.build_size _ _
    correct := by
      intro key valid vertex
      rw [RankRequestBuckets.build_member]
      simp only [CoreEnumeration.finRange_covers n vertex, true_and]
      rw [shared.indexedRoute_eq]
      exact shared.route_iff vertex key valid
    unique := fun key valid => RankRequestBuckets.row_unique _ _ (CoreEnumeration.finRange_unique n) _ }

/-- 分配の実装を索引参照へ置き換えても、行順を含む要求配列全体が変わらない。 -/
theorem buildRequests_buckets_eq :
    shared.buildRequests.buckets = RankRequestBuckets.build shared.route (List.finRange n) := by
  have same : shared.indexedRoute (buildWitnessIndices (ctx := ctx) (otherCore := otherCore)) =
      shared.route := funext (shared.indexedRoute_eq _)
  change RankRequestBuckets.build _ _ = _
  rw [same]

namespace Requests

variable {shared} (requests : Requests shared)

noncomputable def get (key : Key) : List (Fin n) := by
  classical
  exact if valid : ValidKey (G := G) key then RankRequestBuckets.row requests.buckets ⟨keyIndex key, keyIndex_bound key valid⟩ else []

theorem get_iff (key : Key) (vertex : Fin n) : vertex ∈ requests.get key ↔ shared.target vertex = some key := by
  classical
  by_cases valid : ValidKey (G := G) key
  · simp only [get, dif_pos valid]
    exact requests.correct key valid vertex
  · simp only [get, dif_neg valid, List.not_mem_nil, false_iff]
    exact fun found => valid (shared.target_valid vertex key found)

theorem get_unique (key : Key) : (requests.get key).Nodup := by
  classical
  by_cases valid : ValidKey (G := G) key
  · simp only [get, dif_pos valid]
    exact requests.unique key valid
  · simp [get, valid]

end Requests
end PetaProof.ThresholdGame.SharedRankFamily
