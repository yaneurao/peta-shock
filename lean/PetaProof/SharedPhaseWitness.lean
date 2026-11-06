import PetaProof.GeneratedStratumFamily

/-! 要求閾値ごとに別の順位を選ばず、一つの処理閾値につき一つの証拠を共有する。
証拠の選択は非計算的であり、生成時間・生成中メモリの上界は含めない。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V]

structure SharedPhaseWitness (ctx : G.QueueContext E) (value : V → Int) where
  exactValue : ∀ vertex, G.ExactValue vertex (value vertex)
  regions : ∀ level (positive : 0 < level) (cap : level ≤ G.mate), level ∈ ctx.generatedLevels →
    (G.retune level positive cap).ResolvedRegions (fun vertex => level ≤ value vertex) (ctx.vertices.length + 2)

namespace SharedPhaseWitness

variable {ctx : G.QueueContext E} {value : V → Int}

section Records
variable [DecidableEq E]

theorem recorded_regions (atTop : G.threshold = G.mate)
    (values : ∀ vertex, G.ExactValue vertex (value vertex))
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (level : Int) (positive : 0 < level) (cap : level ≤ G.mate) (member : level ∈ ctx.generatedLevels) :
    Nonempty ((G.retune level positive cap).ResolvedRegions
      (fun vertex => level ≤ value vertex) (ctx.vertices.length + 2)) := by
  have stored : ∃ row ∈ phaseStates G ctx ctx.generatedLevels ctx.generatedLevels_valid ctx.seeded,
      row.1 = level := by
    rw [← phaseStates_levels G ctx ctx.generatedLevels ctx.generatedLevels_valid ctx.seeded] at member
    exact List.mem_map.mp member
  obtain ⟨⟨actual, state⟩, present, same⟩ := stored
  change actual = level at same
  subst actual
  have below : ∀ level ∈ ctx.generatedLevels, level ≤ G.threshold := by
    intro t inside
    rw [atTop]
    exact (ctx.generatedLevels_valid t inside).2
  obtain ⟨pos, bounded, certificate⟩ := phaseStates_value_regions G ctx ctx.generatedLevels
    ctx.generatedLevels_valid ctx.generatedLevels_ordered below covers ctx.seeded ctx.seeded_certificate
    ctx.seeded_boundary value values (level, state) present
  exact certificate

/-- 選択は代表閾値ごとに一回定義し、その証拠を全要求から参照する。 -/
noncomputable def fromRecords (atTop : G.threshold = G.mate)
    (values : ∀ vertex, G.ExactValue vertex (value vertex))
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true) :
    SharedPhaseWitness ctx value where
  exactValue := values
  regions := fun level positive cap member => Classical.choice (recorded_regions atTop values covers level positive cap member)

/-- 今回のphaseから同じ型の存在証拠を得れば、固定した選択規則による証拠も一致する。
この一致は存在証拠の証明無関係性を使い、効率的な抽出アルゴリズムを意味しない。 -/
theorem fromRecords_local (atTop : G.threshold = G.mate)
    (values : ∀ vertex, G.ExactValue vertex (value vertex))
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (level : Int) (positive : 0 < level) (cap : level ≤ G.mate) (member : level ∈ ctx.generatedLevels)
    (localEvidence : Nonempty ((G.retune level positive cap).ResolvedRegions
      (fun vertex => level ≤ value vertex) (ctx.vertices.length + 2))) :
    (fromRecords atTop values covers).regions level positive cap member = Classical.choice localEvidence := rfl

end Records

variable (source : SharedPhaseWitness ctx value)

noncomputable def positivePayload (level : Int) (vertex : V) : Nat := by
  classical
  exact if valid : G.CriticalLevel level then
    (source.regions level valid.1 valid.2.1 ((ctx.generatedLevels_critical_iff level).mpr valid)).positive.rank vertex
    else 0

noncomputable def negativePayload (level : Int) (vertex : V) : Nat := by
  classical
  exact if valid : G.CriticalLevel level then
    (source.regions level valid.1 valid.2.1 ((ctx.generatedLevels_critical_iff level).mpr valid)).negative.region.rank vertex
    else 0

/-- 一つの代表証拠を閾値間で移し、選択手と順位を変えずに再利用する。 -/
noncomputable def atQuery (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) :
    (G.retune query positive cap).ResolvedRegions (fun vertex => query ≤ value vertex) (ctx.vertices.length + 2) := by
  let level := ctx.witnessLevel query
  have valid := (ctx.witnessLevel_spec query positive cap).2.1
  let original := source.regions level valid.1 valid.2.1 ((ctx.generatedLevels_critical_iff level).mpr valid)
  have cut : G.SameLeafCut level query := fun vertex score legal =>
    (ctx.witnessLevel_cut query positive cap vertex score legal).symm
  let transferred : (G.retune query positive cap).ResolvedRegions
      (fun vertex => level ≤ value vertex) (ctx.vertices.length + 2) := {
    positive := original.positive.recut query positive cap cut
    negative := { region := original.negative.region.recut query positive cap cut, rank_bound := original.negative.rank_bound }
  }
  apply transferred.reindex
  intro vertex
  exact (ExactValue.lower_iff G ctx.vertices ctx.covered vertex (source.exactValue vertex) level).symm.trans
    ((G.lower_same_cut valid.1 valid.2.1 positive cap cut vertex).trans
      (ExactValue.lower_iff G ctx.vertices ctx.covered vertex (source.exactValue vertex) query))

theorem atQuery_positive_rank (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) (vertex : V) :
    (source.atQuery query positive cap).positive.rank vertex = source.positivePayload (ctx.witnessLevel query) vertex := by
  have valid := (ctx.witnessLevel_spec query positive cap).2.1
  simp only [positivePayload, dif_pos valid]
  rfl

theorem atQuery_negative_rank (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) (vertex : V) :
    (source.atQuery query positive cap).negative.region.rank vertex = source.negativePayload (ctx.witnessLevel query) vertex := by
  have valid := (ctx.witnessLevel_spec query positive cap).2.1
  simp only [negativePayload, dif_pos valid]
  rfl

theorem same_positive_rank (first second : Int) (firstPos : 0 < first) (secondPos : 0 < second)
    (firstCap : first ≤ G.mate) (secondCap : second ≤ G.mate)
    (same : ctx.witnessLevel first = ctx.witnessLevel second) (vertex : V) :
    (source.atQuery first firstPos firstCap).positive.rank vertex =
      (source.atQuery second secondPos secondCap).positive.rank vertex := by
  rw [source.atQuery_positive_rank, source.atQuery_positive_rank, same]

theorem same_negative_rank (first second : Int) (firstPos : 0 < first) (secondPos : 0 < second)
    (firstCap : first ≤ G.mate) (secondCap : second ≤ G.mate)
    (same : ctx.witnessLevel first = ctx.witnessLevel second) (vertex : V) :
    (source.atQuery first firstPos firstCap).negative.region.rank vertex =
      (source.atQuery second secondPos secondCap).negative.region.rank vertex := by
  rw [source.atQuery_negative_rank, source.atQuery_negative_rank, same]

end SharedPhaseWitness
end PetaProof.ThresholdGame
