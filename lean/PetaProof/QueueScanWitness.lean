import PetaProof.QueueThresholdWitness

/-! 全閾値の実走査に対応する、証明用のphase返却状態列。
これは順位表の圧縮実装ではない。状態列を本番で保持することも要求しない。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def phaseStates : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) →
    PropagationState V E → List (Int × PropagationState V E)
  | _, _, [], _, _ => []
  | G, ctx, t :: rest, valid, state =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let next := ctx.phase t positive bounded state
    (t, next) :: phaseStates (G.retune t positive bounded) (ctx.atLevel t positive bounded)
      rest (fun s member => valid s (by simp [member])) next

theorem phaseStates_levels (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) :
    (phaseStates G ctx levels valid state).map Prod.fst = levels := by
  induction levels generalizing G state with
  | nil => rfl
  | cons t rest ih =>
    simp only [phaseStates, List.map_cons, Prod.fst]
    congr 1
    exact ih _ _ _ _

def lastPhase (initial : PropagationState V E) (rows : List (Int × PropagationState V E)) :
    PropagationState V E := rows.foldl (fun _ row => row.2) initial

/-- 最後の記録は、値配列を更新する元の全走査と同じ返却状態である。 -/
theorem phaseStates_final (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) (values : V → Int) :
    lastPhase state (phaseStates G ctx levels valid state) =
      (scanQueues G ctx levels valid state values).1 := by
  induction levels generalizing G state values with
  | nil => rfl
  | cons t rest ih =>
    let pos := (valid t (by simp)).1
    let cap := (valid t (by simp)).2
    let low := ctx.atLevel t pos cap
    let next := ctx.phase t pos cap state
    let tailValid := fun level (mem : level ∈ rest) => valid level (List.mem_cons_of_mem t mem)
    change lastPhase next (phaseStates (G.retune t pos cap) low rest tailValid next) =
      (scanQueues (G.retune t pos cap) low rest tailValid next
        (latchValues values t (fun vertex => (next.counters vertex).admitted))).1
    exact ih _ low tailValid next _

/-- 各行は、直前までの同じカウンターを引き継いだ実phaseの両側の順位証拠を持つ。 -/
theorem phaseStates_regions (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a))
    (below : ∀ t ∈ levels, t ≤ G.threshold)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) :
    ∀ row ∈ phaseStates G ctx levels valid state,
      ∃ positive : 0 < row.1, ∃ bounded : row.1 ≤ G.mate,
        Nonempty ((G.retune row.1 positive bounded).ResolvedRegions row.2.won (ctx.vertices.length + 2)) := by
  induction levels generalizing G state with
  | nil => simp [phaseStates]
  | cons t rest ih =>
    intro row member
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    have lower := below t (by simp)
    let next := ctx.phase t positive bounded state
    change row ∈ (t, next) :: _ at member
    rcases List.mem_cons.mp member with same | tail
    · subst row
      exact ⟨positive, bounded, ctx.phase_regions state certificate boundary covers t positive lower⟩
    · obtain ⟨cert⟩ := ctx.phase_certified state certificate t positive lower
      have boundNext := ctx.phase_boundary state boundary t positive lower
      have tailBelow : ∀ s ∈ rest, s ≤ (G.retune t positive bounded).threshold :=
        fun s mem => Int.le_of_lt (List.rel_of_pairwise_cons descending mem)
      exact ih (G.retune t positive bounded) (ctx.atLevel t positive bounded)
        (fun s mem => valid s (by simp [mem])) descending.of_cons tailBelow covers next cert boundNext row tail

/-- 全走査の各返却順位を、後から得た正確な値表の同じ閾値領域へ移す。 -/
theorem phaseStates_value_regions (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a))
    (below : ∀ t ∈ levels, t ≤ G.threshold)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (state : PropagationState V E) (certificate : StateCertificate ctx.indexed state)
    (boundary : ctx.Boundary state) (value : V → Int)
    (values : ∀ vertex, G.ExactValue vertex (value vertex))
    (row : Int × PropagationState V E) (member : row ∈ phaseStates G ctx levels valid state) :
    ∃ positive : 0 < row.1, ∃ bounded : row.1 ≤ G.mate,
      Nonempty ((G.retune row.1 positive bounded).ResolvedRegions
        (fun vertex => row.1 ≤ value vertex) (ctx.vertices.length + 2)) := by
  obtain ⟨pos, cap, ⟨regions⟩⟩ := phaseStates_regions G ctx levels valid descending below covers
    state certificate boundary row member
  refine ⟨pos, cap, ⟨regions.reindex ?_⟩⟩
  intro vertex
  exact (regions.exact ctx.vertices ctx.covered vertex).trans
    ((G.retune_winning_iff row.1 pos cap vertex).trans
      (G.lower_iff_exact_value ctx.vertices ctx.covered vertex (value vertex) row.1 (values vertex)))

/-- 閾値列も値の正解も外から渡さず、有限入力から得た同じ走査へ接続する。 -/
theorem generated_phase_regions {G : ThresholdGame V} (ctx : G.QueueContext E)
    (atTop : G.threshold = G.mate) (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (row : Int × PropagationState V E)
    (member : row ∈ phaseStates G ctx ctx.generatedLevels ctx.generatedLevels_valid ctx.seeded) :
    ∃ positive : 0 < row.1, ∃ bounded : row.1 ≤ G.mate,
      Nonempty ((G.retune row.1 positive bounded).ResolvedRegions
        (fun vertex => row.1 ≤ ctx.generatedValue otherCore vertex) (ctx.vertices.length + 2)) := by
  apply phaseStates_value_regions G ctx ctx.generatedLevels ctx.generatedLevels_valid
    ctx.generatedLevels_ordered _ covers ctx.seeded ctx.seeded_certificate ctx.seeded_boundary
    (ctx.generatedValue otherCore) (ctx.generatedValue_exact otherCore leaves covers otherCovers) row member
  intro level present
  rw [atTop]
  exact (ctx.generatedLevels_valid level present).2

end PetaProof.ThresholdGame
