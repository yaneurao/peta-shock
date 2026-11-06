import PetaProof.StoppedComplement
import PetaProof.ValueStratumFamily
import PetaProof.GeneratedThresholds

/-! 同じキュー返却状態から正側の順位と全補集合の反証順位を取り出す。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

namespace RefutationRegion

def reindex {old next : V → Prop} (region : G.RefutationRegion old)
    (same : ∀ vertex, old vertex ↔ next vertex) : G.RefutationRegion next where
  response := region.response
  chosen_legal := fun vertex inside => region.chosen_legal vertex ((same vertex).mpr inside)
  closed := by
    intro vertex inside move reply
    have closed := region.closed vertex ((same vertex).mpr inside) move reply
    cases move with
    | leaf score => exact closed
    | node child => exact (same child).mp closed
  rank := region.rank
  strict_checking := fun vertex child inside => region.strict_checking vertex child ((same vertex).mpr inside)

end RefutationRegion

/-- 返却集合の正側順位と、その全補集合を同時に覆う反証順位。 -/
structure ResolvedRegions (G : ThresholdGame V) (won : V → Prop) (cap : Nat) where
  positive : G.RankedRegion won
  negative : G.ComplementWitness won cap

namespace ResolvedRegions

variable {old next : V → Prop} {cap : Nat}

def reindex (regions : G.ResolvedRegions old cap) (same : ∀ vertex, old vertex ↔ next vertex) :
    G.ResolvedRegions next cap where
  positive := regions.positive.reindex same
  negative := {
    region := regions.negative.region.reindex (fun vertex => not_congr (same vertex))
    rank_bound := fun vertex outside => regions.negative.rank_bound vertex ((not_congr (same vertex)).mpr outside)
  }

theorem exact [DecidableEq V] (regions : G.ResolvedRegions old cap)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (root : V) :
    old root ↔ G.FourfoldWinning root := by
  constructor
  · exact regions.positive.fourfold_winning root
  · intro winning
    apply Classical.byContradiction
    intro outside
    exact regions.negative.region.not_fourfold_winning vertices covered root outside winning

end ResolvedRegions

/-- 整数最適値が既に証明されていれば、任意の下限の可否は値との比較に一致する。 -/
theorem lower_iff_exact_value [DecidableEq V] (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (root : V) (value bound : Int) (exactValue : G.ExactValue root value) :
    G.LowerGuarantee root bound ↔ bound ≤ value := by
  constructor
  · rintro ⟨self, lower⟩
    obtain ⟨opponent, upper⟩ := exactValue.2
    obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered (G.combinePlans self opponent) root
    exact Int.le_trans (lower opponent payoff result) (upper self payoff result)
  · intro lower
    obtain ⟨self, guaranteed⟩ := exactValue.1
    exact ⟨self, fun opponent payoff result => Int.le_trans lower (guaranteed opponent payoff result)⟩

namespace QueueContext

variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

/-- 正側は同じ通常状態の証明書を使い、負側も同じ確定集合の補集合を覆う。 -/
theorem settleQueue_regions (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) :
    Nonempty (G.ResolvedRegions (ctx.settleQueue ctx.vertices.length state).won (ctx.vertices.length + 2)) := by
  obtain ⟨final⟩ := ctx.settleQueue_certified ctx.vertices.length state certificate
  obtain ⟨negative⟩ := G.exact_complement_witness final.region ctx.vertices ctx.covered
    (ctx.settleQueue_exact state certificate boundary covers)
  exact ⟨⟨final.region, negative⟩⟩

/-- 初期状態を作り直さず、新leaf帯を通知した実際のphaseの返却集合から抽出する。 -/
theorem phase_regions (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    Nonempty ((G.retune bound positive (Int.le_trans lower G.bounded)).ResolvedRegions
      (ctx.phase bound positive (Int.le_trans lower G.bounded) state).won (ctx.vertices.length + 2)) := by
  exact (ctx.atLevel bound positive _).settleQueue_regions
    (ctx.prepare bound positive _ state) (ctx.prepare_certificate state certificate bound positive lower)
    (ctx.prepare_boundary state boundary bound positive lower) covers

/-- 値配列と閾値返却集合の一致を使い、選択手・順位を変えず層別証拠へ移す。 -/
theorem phase_value_regions (value : V → Int) (values : ∀ vertex, G.ExactValue vertex (value vertex))
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    Nonempty ((G.retune bound positive (Int.le_trans lower G.bounded)).ResolvedRegions
      (fun vertex => bound ≤ value vertex) (ctx.vertices.length + 2)) := by
  obtain ⟨regions⟩ := ctx.phase_regions state certificate boundary covers bound positive lower
  exact ⟨regions.reindex (fun vertex => (ctx.phase_exact state certificate boundary covers bound positive lower vertex).trans
    (G.lower_iff_exact_value ctx.vertices ctx.covered vertex (value vertex) bound (values vertex)))⟩

/-- 値の正当性は有限入力からの主計算の既証定理を使い、外部の正解値を入力しない。 -/
theorem phase_generated_regions (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) (bound : Int) (positive : 0 < bound) (lower : bound ≤ G.threshold) :
    Nonempty ((G.retune bound positive (Int.le_trans lower G.bounded)).ResolvedRegions
      (fun vertex => bound ≤ ctx.generatedValue otherCore vertex) (ctx.vertices.length + 2)) :=
  ctx.phase_value_regions (ctx.generatedValue otherCore)
    (ctx.generatedValue_exact otherCore leaves covers otherCovers) state certificate boundary covers bound positive lower

end QueueContext
end PetaProof.ThresholdGame
