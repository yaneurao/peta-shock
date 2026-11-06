import PetaProof.SharedPhaseWitness
import PetaProof.CapturedCandidateTable

/-! 両視点の共有証拠から候補表と取得先を同時に定義する。
同じ代表閾値では同じ証拠を参照するため、保存する順位と表の順位が一致する。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V} [DecidableEq V]

structure SharedRankFamily (ctx : G.QueueContext E) (otherCore : V → Bool) where
  value : V → Int
  bounded : ∀ vertex, -G.mate ≤ value vertex ∧ value vertex ≤ G.mate
  leaves : G.BoundedLeaves
  own : SharedPhaseWitness ctx value
  opponent : SharedPhaseWitness (ctx.opposite otherCore) (fun vertex => -value vertex)

namespace SharedRankFamily

variable {ctx : G.QueueContext E} {otherCore : V → Bool}

/-- 共通証拠は新しい外部仮定ではなく、両側の実走査の返却証拠から構成できる。 -/
noncomputable def fromGenerated [DecidableEq E] (atTop : G.threshold = G.mate)
    (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    SharedRankFamily ctx otherCore where
  value := ctx.generatedValue otherCore
  bounded := ctx.generatedValue_bounded otherCore leaves covers otherCovers
  leaves := leaves
  own := SharedPhaseWitness.fromRecords atTop
    (ctx.generatedValue_exact otherCore leaves covers otherCovers) covers
  opponent := SharedPhaseWitness.fromRecords atTop (fun vertex => by
    have exact := ctx.other_generated_exact otherCore leaves covers otherCovers vertex
    rw [ctx.generated_opposite_sign otherCore leaves covers otherCovers vertex] at exact
    exact exact) otherCovers

variable (shared : SharedRankFamily ctx otherCore)

noncomputable def family : G.StratumFamily where
  value := shared.value
  bounded := shared.bounded
  leaves := shared.leaves
  positive := fun bound pos cap => (shared.own.atQuery bound pos cap).positive
  nonpositive := by
    intro bound better nonpositive
    have pos : 0 < 1 - bound := by omega
    have cap : 1 - bound ≤ G.opposite.mate := by change 1 - bound ≤ G.mate; omega
    exact (shared.opponent.atQuery (1 - bound) pos cap).negative.region.reindex (by
      intro vertex
      change ¬ (1 - bound ≤ -shared.value vertex) ↔ bound ≤ shared.value vertex
      omega)

noncomputable def table : G.ValueRankTable := shared.family.table.diagonal

/-- falseは自分側走査の正順位、trueは相手側走査の反証順位を表す。 -/
abbrev Key := Bool × Int

noncomputable def target (vertex : V) : Option Key := by
  classical
  exact if 0 < shared.value vertex then some (false, ctx.witnessLevel (shared.value vertex))
    else if -G.mate < shared.value vertex then some (true, (ctx.opposite otherCore).witnessLevel (1 - shared.value vertex))
    else none

noncomputable def payload (key : Key) (vertex : V) : Nat :=
  if key.1 then shared.opponent.negativePayload key.2 vertex else shared.own.positivePayload key.2 vertex

/-- 生成器に最終表との一致を仮定せず、共有証拠から取得先のpayloadとの一致を導く。 -/
theorem target_payload (vertex : V) (key : Key) (found : shared.target vertex = some key) :
    shared.payload key vertex = shared.table.rank (shared.table.value vertex) vertex := by
  classical
  by_cases positive : 0 < shared.value vertex
  · simp only [target, if_pos positive, Option.some.injEq] at found
    rw [← found]
    change shared.own.positivePayload (ctx.witnessLevel (shared.value vertex)) vertex =
      shared.family.table.rank (shared.value vertex) vertex
    rw [shared.family.positive_rank (shared.value vertex) positive (shared.bounded vertex).2]
    exact (shared.own.atQuery_positive_rank _ positive (shared.bounded vertex).2 vertex).symm
  · by_cases better : -G.mate < shared.value vertex
    · simp only [target, if_neg positive, if_pos better, Option.some.injEq] at found
      rw [← found]
      have nonpositive : shared.value vertex ≤ 0 := by omega
      change shared.opponent.negativePayload ((ctx.opposite otherCore).witnessLevel (1 - shared.value vertex)) vertex =
        shared.family.table.rank (shared.value vertex) vertex
      rw [shared.family.nonpositive_rank (shared.value vertex) better nonpositive]
      exact (shared.opponent.atQuery_negative_rank _ (by omega) (by change 1 - shared.value vertex ≤ G.mate; omega) vertex).symm
    · simp [target, positive, better] at found

theorem omitted_rank_zero (vertex : V) (omitted : shared.target vertex = none) :
    shared.table.rank (shared.table.value vertex) vertex = 0 := by
  classical
  have nonpositive : ¬ 0 < shared.value vertex := by
    intro pos
    simp [target, pos] at omitted
  have notBetter : ¬ -G.mate < shared.value vertex := by
    intro better
    simp [target, nonpositive, better] at omitted
  have bottom : shared.value vertex = -G.mate := by have := (shared.bounded vertex).1; omega
  exact shared.family.bottom_diagonal_rank vertex bottom

theorem replies : shared.table.AllReplies := by
  intro vertex move other legal
  exact (shared.family.table.diagonal_candidate vertex move).mpr (shared.family.all_replies vertex move other legal)

theorem nonempty (vertex : V) (own : G.owner vertex = G.player) :
    ∃ move, shared.table.admissibleMove vertex move := by
  obtain ⟨move, safe⟩ := shared.family.candidates_nonempty vertex own
  exact ⟨move, (shared.family.table.diagonal_admissible vertex move).mpr safe⟩

def keys (_shared : SharedRankFamily ctx otherCore) : List Key :=
  ctx.generatedLevels.map (fun level => (false, level)) ++
    (ctx.opposite otherCore).generatedLevels.map (fun level => (true, level))

theorem keys_unique : shared.keys.Nodup := by
  unfold keys
  change List.Pairwise (fun a b => a ≠ b) (_ ++ _)
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    apply ctx.generatedLevels_ordered.imp
    intro first second less same
    have equal := congrArg Prod.snd same
    omega
  · rw [List.pairwise_map]
    apply (ctx.opposite otherCore).generatedLevels_ordered.imp
    intro first second less same
    have equal := congrArg Prod.snd same
    omega
  · intro first present second later same
    obtain ⟨left, _, rfl⟩ := List.mem_map.mp present
    obtain ⟨right, _, rfl⟩ := List.mem_map.mp later
    exact Bool.noConfusion (congrArg Prod.fst same)

theorem target_registered (vertex : V) (key : Key) (found : shared.target vertex = some key) : key ∈ shared.keys := by
  classical
  by_cases positive : 0 < shared.value vertex
  · simp only [target, if_pos positive, Option.some.injEq] at found
    rw [← found]
    apply List.mem_append.mpr
    apply Or.inl
    exact List.mem_map.mpr ⟨_, (ctx.generatedLevels_critical_iff _).mpr
      (ctx.witnessLevel_spec _ positive (shared.bounded vertex).2).2.1, rfl⟩
  · by_cases better : -G.mate < shared.value vertex
    · simp only [target, if_neg positive, if_pos better, Option.some.injEq] at found
      rw [← found]
      apply List.mem_append.mpr
      apply Or.inr
      have pos : 0 < 1 - shared.value vertex := by omega
      have cap : 1 - shared.value vertex ≤ G.opposite.mate := by change 1 - shared.value vertex ≤ G.mate; omega
      exact List.mem_map.mpr ⟨_, ((ctx.opposite otherCore).generatedLevels_critical_iff _).mpr
        ((ctx.opposite otherCore).witnessLevel_spec _ pos cap).2.1, rfl⟩
    · simp [target, positive, better] at found

def ValidKey (key : Key) : Prop := 0 < key.2 ∧ key.2 ≤ G.mate

instance (key : Key) : Decidable (ValidKey (G := G) key) :=
  inferInstanceAs (Decidable (0 < key.2 ∧ key.2 ≤ G.mate))

theorem registered_valid (key : Key) (member : key ∈ shared.keys) : ValidKey (G := G) key := by
  rcases List.mem_append.mp member with own | other
  · obtain ⟨level, present, rfl⟩ := List.mem_map.mp own
    exact ctx.generatedLevels_valid level present
  · obtain ⟨level, present, rfl⟩ := List.mem_map.mp other
    exact (ctx.opposite otherCore).generatedLevels_valid level present

theorem target_valid (vertex : V) (key : Key) (found : shared.target vertex = some key) : ValidKey (G := G) key :=
  shared.registered_valid key (shared.target_registered vertex key found)

end SharedRankFamily
end PetaProof.ThresholdGame
