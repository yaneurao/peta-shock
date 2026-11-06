import PetaProof.SparseWitnessCut
import PetaProof.ValueStratumFilter

/-! 疎な実走査の証拠を全整数閾値へ移し、外部の順位族なしに安全候補を構成する。
証拠の取り出しには古典的選択を用いる。生成費用まで検証した実行コードではない。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E] (ctx : G.QueueContext E)

/-- 未処理の整数閾値も、同じleaf合否を持つ記録から選択手・順位をそのまま得る。 -/
theorem generated_cut_regions (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) :
    Nonempty ((G.retune query positive cap).ResolvedRegions
      (fun vertex => query ≤ ctx.generatedValue otherCore vertex) (ctx.vertices.length + 2)) := by
  obtain ⟨row, member, sameLevel⟩ := ctx.witnessLevel_recorded query positive cap
  obtain ⟨pos, bounded, ⟨regions⟩⟩ := generated_phase_regions ctx atTop otherCore leaves covers otherCovers row member
  have cut : G.SameLeafCut row.1 query := by
    intro vertex score legal
    rw [sameLevel]
    exact (ctx.witnessLevel_cut query positive cap vertex score legal).symm
  let transferred : (G.retune query positive cap).ResolvedRegions
      (fun vertex => row.1 ≤ ctx.generatedValue otherCore vertex) (ctx.vertices.length + 2) := {
    positive := regions.positive.recut query positive cap cut
    negative := {
      region := regions.negative.region.recut query positive cap cut
      rank_bound := regions.negative.rank_bound
    }
  }
  refine ⟨transferred.reindex ?_⟩
  intro vertex
  have exactValue := ctx.generatedValue_exact otherCore leaves covers otherCovers vertex
  exact (ExactValue.lower_iff G ctx.vertices ctx.covered vertex exactValue row.1).symm.trans
    ((G.lower_same_cut pos bounded positive cap cut vertex).trans
      (ExactValue.lower_iff G ctx.vertices ctx.covered vertex exactValue query))

theorem generatedValue_bounded (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) : -G.mate ≤ ctx.generatedValue otherCore vertex ∧ ctx.generatedValue otherCore vertex ≤ G.mate := by
  have exactValue := ctx.generatedValue_exact otherCore leaves covers otherCovers vertex
  obtain ⟨self, opponent, ⟨result⟩⟩ := ExactValue.realized G ctx.vertices ctx.covered vertex exactValue
  exact TerminalResult.payoff_bounded G leaves result

/-- 全閾値の証拠族を有限入力から構成する。正解値や順位族を追加の入力にしない。 -/
noncomputable def generatedFamily (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    G.StratumFamily where
  value := ctx.generatedValue otherCore
  bounded := ctx.generatedValue_bounded otherCore leaves covers otherCovers
  leaves := leaves
  positive := fun bound positive cap =>
    (Classical.choice (ctx.generated_cut_regions atTop otherCore leaves covers otherCovers bound positive cap)).positive
  nonpositive := by
    intro bound better nonpositive
    let other := ctx.opposite otherCore
    have positive : 0 < 1 - bound := by omega
    have cap : 1 - bound ≤ G.opposite.mate := by change 1 - bound ≤ G.mate; omega
    let regions := Classical.choice (other.generated_cut_regions atTop ctx.core
      (G.opposite_bounded_leaves leaves) otherCovers (ctx.opposite_opposite_core covers) (1 - bound) positive cap)
    apply regions.negative.region.reindex
    intro vertex
    have sign := ctx.generated_opposite_sign otherCore leaves covers otherCovers vertex
    change (ctx.opposite otherCore).generatedValue ctx.core vertex = -ctx.generatedValue otherCore vertex at sign
    change ¬ (1 - bound ≤ (ctx.opposite otherCore).generatedValue ctx.core vertex) ↔ _
    rw [sign]
    omega

/-- 各頂点自身の値の順位一個だけを使う候補表。 -/
noncomputable def generatedTable (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    G.ValueRankTable := (ctx.generatedFamily atTop otherCore leaves covers otherCovers).table.diagonal

theorem generatedTable_replies (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    (ctx.generatedTable atTop otherCore leaves covers otherCovers).AllReplies := by
  let family := ctx.generatedFamily atTop otherCore leaves covers otherCovers
  intro vertex move other legal
  exact (family.table.diagonal_candidate vertex move).mpr (family.all_replies vertex move other legal)

theorem generatedTable_nonempty (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) (own : G.owner vertex = G.player) :
    ∃ move, (ctx.generatedTable atTop otherCore leaves covers otherCovers).admissibleMove vertex move := by
  let family := ctx.generatedFamily atTop otherCore leaves covers otherCovers
  obtain ⟨move, safe⟩ := family.candidates_nonempty vertex own
  exact ⟨move, (family.table.diagonal_admissible vertex move).mpr safe⟩

/-- 同じ入力から生成した候補内の任意の履歴依存選択が、計算値の下限を保つ。 -/
theorem generatedTable_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (self opponent : G.MovePlan)
    (allowed : (ctx.generatedTable atTop otherCore leaves covers otherCovers).AdmissiblePlan self)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff :=
  (ctx.generatedTable atTop otherCore leaves covers otherCovers).terminal_lower
    (ctx.generatedTable_replies atTop otherCore leaves covers otherCovers) self opponent allowed root payoff result

/-- 生成表を元辺の安定filterへ渡す。元の指し手IDを失わない。 -/
noncomputable def generatedInput (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    ValueStratumFilter.Input (ctx.generatedTable atTop otherCore leaves covers otherCovers) E where
  indexed := ctx.indexed
  checked := ctx.checked
  checked_correct := ctx.check_correct

theorem generated_kept_nonempty (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (vertex : V) (own : G.owner vertex = G.player) :
    ∃ edge, edge ∈ (ctx.generatedInput atTop otherCore leaves covers otherCovers).kept vertex := by
  obtain ⟨move, safe⟩ := ctx.generatedTable_nonempty atTop otherCore leaves covers otherCovers vertex own
  obtain ⟨edge, member, _⟩ :=
    (ctx.generatedInput atTop otherCore leaves covers otherCovers).nonempty_of_safe vertex move safe
  exact ⟨edge, member⟩

theorem generated_kept_lower (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ (ctx.generatedInput atTop otherCore leaves covers otherCovers).kept vertex,
        self.choose history vertex = ctx.indexed.move edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff :=
  (ctx.generatedInput atTop otherCore leaves covers otherCovers).filtered_plan_lower
    (ctx.generatedTable_replies atTop otherCore leaves covers otherCovers) self opponent selected root payoff result

/-- 表の各頂点に値と順位一個だけを格納する。中間証拠の生成空間とは別の上界。 -/
noncomputable def generatedStoredRows (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    List (V × Int × Nat) :=
  ctx.vertices.map (fun vertex => (vertex, ctx.generatedValue otherCore vertex,
    (ctx.generatedTable atTop otherCore leaves covers otherCovers).rank 0 vertex))

theorem generatedStoredRows_length (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    (ctx.generatedStoredRows atTop otherCore leaves covers otherCovers).length = ctx.vertices.length := by
  simp [generatedStoredRows]

theorem generatedTable_rank_independent (atTop : G.threshold = G.mate)
    (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (level : Int) (vertex : V) :
    (ctx.generatedTable atTop otherCore leaves covers otherCovers).rank level vertex =
      (ctx.generatedTable atTop otherCore leaves covers otherCovers).rank 0 vertex := rfl

end PetaProof.ThresholdGame.QueueContext
