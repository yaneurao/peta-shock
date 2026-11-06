import PetaProof.QueueScanWitness
import PetaProof.QueueCounterWitness

/-! 疎な走査にない整数閾値を、leafの合否が等しい実処理閾値へ丸める。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

/-- 合法手・選択手・順位を変えず、成功leafの集合だけが等しい閾値へ移す。 -/
def RankedRegion.recut {won : V → Prop} (region : G.RankedRegion won)
    (level : Int) (positive : 0 < level) (cap : level ≤ G.mate)
    (same : G.SameLeafCut G.threshold level) : (G.retune level positive cap).RankedRegion won where
  choice := region.choice
  rank := region.rank
  stage := region.stage
  rank_bound := region.rank_bound
  chosen_legal := region.chosen_legal
  closed := by
    intro vertex inside move follows
    have closed := region.closed vertex inside move follows
    cases move with
    | node child => exact closed
    | leaf score => exact (same vertex score follows.1).mp closed
  decreasing := region.decreasing
  opponent_strict := region.opponent_strict

def RefutationRegion.recut {lost : V → Prop} (region : G.RefutationRegion lost)
    (level : Int) (positive : 0 < level) (cap : level ≤ G.mate)
    (same : G.SameLeafCut G.threshold level) : (G.retune level positive cap).RefutationRegion lost where
  response := region.response
  rank := region.rank
  chosen_legal := region.chosen_legal
  closed := by
    intro vertex inside move replies
    have closed := region.closed vertex inside move replies
    cases move with
    | node child => exact closed
    | leaf score =>
      have cut := same vertex score replies.1
      change score < level
      change score < G.threshold at closed
      omega
  strict_checking := region.strict_checking

/-- 始値も候補として残す、query以上の最小整数の一回走査。 -/
def ceilingFold (query : Int) : Int → List Int → Int
  | current, [] => current
  | current, level :: rest =>
    ceilingFold query (if query ≤ level ∧ level < current then level else current) rest

theorem ceilingFold_spec (query current : Int) (levels : List Int) (initial : query ≤ current) :
    query ≤ ceilingFold query current levels ∧
    (ceilingFold query current levels = current ∨ ceilingFold query current levels ∈ levels) ∧
    ceilingFold query current levels ≤ current ∧
    ∀ level ∈ levels, query ≤ level → ceilingFold query current levels ≤ level := by
  induction levels generalizing current with
  | nil => simp [ceilingFold, initial]
  | cons level rest ih =>
    let next := if query ≤ level ∧ level < current then level else current
    have nextBound : query ≤ next := by dsimp [next]; split <;> omega
    obtain ⟨lower, member, upper, smallest⟩ := ih next nextBound
    have nextUpper : next ≤ current := by dsimp [next]; split <;> omega
    have nextLevel : query ≤ level → next ≤ level := by dsimp [next]; split <;> omega
    change query ≤ ceilingFold query next rest ∧
      (ceilingFold query next rest = current ∨ ceilingFold query next rest ∈ level :: rest) ∧
      ceilingFold query next rest ≤ current ∧
      ∀ other ∈ level :: rest, query ≤ other → ceilingFold query next rest ≤ other
    refine ⟨lower, ?_, by omega, ?_⟩
    · rcases member with same | tail
      · rw [same]
        dsimp [next]
        split <;> simp
      · exact Or.inr (List.mem_cons_of_mem _ tail)
    · intro other present above
      rcases List.mem_cons.mp present with same | tail
      · subst other; have := nextLevel above; omega
      · exact smallest other tail above

namespace QueueContext

variable (ctx : G.QueueContext E)

def witnessLevel (query : Int) : Int := ceilingFold query G.mate ctx.generatedLevels

theorem witnessLevel_spec (query : Int) (_positive : 0 < query) (cap : query ≤ G.mate) :
    query ≤ ctx.witnessLevel query ∧ G.CriticalLevel (ctx.witnessLevel query) ∧
      ∀ level, G.CriticalLevel level → query ≤ level → ctx.witnessLevel query ≤ level := by
  obtain ⟨lower, member, upper, smallest⟩ := ceilingFold_spec query G.mate ctx.generatedLevels cap
  refine ⟨lower, ?_, ?_⟩
  · rcases member with same | member
    · rw [show ctx.witnessLevel query = G.mate from same]
      exact G.mate_critical
    · exact (ctx.generatedLevels_critical_iff _).mp member
  · intro level critical above
    exact smallest level ((ctx.generatedLevels_critical_iff level).mpr critical) above

/-- queryから代表閾値の直前までにleaf値は存在せず、合否集合が厳密に同じ。 -/
theorem witnessLevel_cut (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) :
    G.SameLeafCut query (ctx.witnessLevel query) := by
  obtain ⟨lower, critical, smallest⟩ := ctx.witnessLevel_spec query positive cap
  have upper := critical.2.1
  apply G.same_leaf_cut_of_gap lower
  intro vertex score legal between
  have candidate : G.CriticalLevel score :=
    ⟨by omega, by omega, Or.inr ⟨vertex, legal⟩⟩
  have bound := smallest score candidate between.1
  omega

variable [DecidableEq V] [DecidableEq E]

/-- 代表閾値は実際のphase記録に現れる。追加のphaseを実行する必要はない。 -/
theorem witnessLevel_recorded (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) :
    ∃ row ∈ phaseStates G ctx ctx.generatedLevels ctx.generatedLevels_valid ctx.seeded,
      row.1 = ctx.witnessLevel query := by
  have member := (ctx.generatedLevels_critical_iff _).mpr (ctx.witnessLevel_spec query positive cap).2.1
  rw [← phaseStates_levels G ctx ctx.generatedLevels ctx.generatedLevels_valid ctx.seeded] at member
  exact List.mem_map.mp member

end QueueContext
end PetaProof.ThresholdGame
