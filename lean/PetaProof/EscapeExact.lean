import PetaProof.EscapeBounds
import PetaProof.EscapeTableCheck

/-! 実FIFO出力の上下界を合わせ、一般入力で最短保証距離と完全一致させる。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E) {arena : HistoryArena V} {target : V → Prop}

omit [DecidableEq V] [DecidableEq E] in
theorem stopped_received (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (edge : E) (notified : state.notified edge = true) (cost : Nat)
    (known : (state.counters (input.child edge)).result = some cost) : state.received edge = cost := by
  have logged := inv.notified_logged edge notified
  have receivedKnown := (coherent (input.child edge) (state.received edge)).mpr (List.mem_append_left _ logged)
  exact Option.some.inj (receivedKnown.symm.trans known)

omit [DecidableEq V] [DecidableEq E] in
theorem stopped_own_bound (goals : List V) (state : State V E) (inv : Invariant input state)
    (coherent : Coherent state) (complete : Complete input state) (empty : state.frame.queue.pending = [])
    (bounds : Bounds input goals state) (vertex : V) (own : input.own vertex = true)
    (edge : E) (member : edge ∈ input.outgoing vertex) (distance cost : Nat)
    (parentKnown : (state.counters vertex).result = some distance)
    (childKnown : (state.counters (input.child edge)).result = some cost) : distance ≤ cost + 1 := by
  have source := (input.outgoing_correct vertex edge).mp member
  have notified := (complete edge).mpr ((stopped_finite_iff state coherent empty _).mp ⟨cost, childKnown⟩)
  have ownSource : input.own (input.source edge) = true := by simpa only [source] using own
  obtain ⟨other, known, bound⟩ := bounds.own edge notified ownSource
  rw [source] at known
  have same : other = distance := Option.some.inj (known.symm.trans parentKnown)
  have received := stopped_received input state inv coherent edge notified cost childKnown
  omega

theorem runLabels_own_bound (goals vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (own : input.own vertex = true) (edge : E) (member : edge ∈ input.outgoing vertex)
    (distance cost : Nat) (parentKnown : runLabels input goals vertices vertex = some distance)
    (childKnown : runLabels input goals vertices (input.child edge) = some cost) : distance ≤ cost + 1 := by
  cases started : start input goals with
  | none => simp [runLabels, started] at parentKnown
  | some state =>
    obtain ⟨inv, coherent, complete⟩ := started_run_good input goals state started vertices.length
    have initial := start_good input goals state started
    have bounds := run_bounds input goals vertices.length state initial.1 initial.2.1 (start_bounds input goals state started)
    apply stopped_own_bound input goals _ inv coherent complete (started_run_drained input goals state started vertices covered)
      bounds vertex own edge member distance cost
    · simpa only [runLabels, started] using parentKnown
    · simpa only [runLabels, started] using childKnown

theorem runLabels_other_witness (goals vertices : List V) (vertex : V) (notGoal : vertex ∉ goals)
    (own : input.own vertex = false) (distance : Nat) (known : runLabels input goals vertices vertex = some distance) :
    ∃ edge ∈ input.outgoing vertex, ∃ cost, runLabels input goals vertices (input.child edge) = some cost ∧ distance ≤ cost + 1 := by
  cases started : start input goals with
  | none => simp [runLabels, started] at known
  | some state =>
    have initial := start_good input goals state started
    have bounds := run_bounds input goals vertices.length state initial.1 initial.2.1 (start_bounds input goals state started)
    have current : ((run input vertices.length state).counters vertex).result = some distance := by
      simpa only [runLabels, started] using known
    simpa only [runLabels, started] using bounds.other vertex distance notGoal own current

/-- 到達層nの頂点には実出力でn以下のラベルが付く。ここで過大距離を排除する。 -/
theorem runLabels_layer_bound (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (bound : Nat) (vertex : V) (inside : arena.escapeLayer target bound vertex) :
    ∃ distance, runLabels input goals vertices vertex = some distance ∧ distance ≤ bound := by
  induction bound generalizing vertex with
  | zero => exact ⟨0, runLabels_goal_zero input goals vertices vertex ((goals_correct vertex).mp inside), Nat.le_refl _⟩
  | succ bound ih =>
    have finite := (runLabels_finite_iff input matching goals vertices goals_correct covered vertex).mpr
      (arena.escapeLayer_complete target vertices covered (bound + 1) vertex inside)
    obtain ⟨distance, known⟩ := finite
    rcases inside with goal | step
    · have zero := runLabels_goal_zero input goals vertices vertex ((goals_correct vertex).mp goal)
      have same : distance = 0 := Option.some.inj (known.symm.trans zero)
      exact ⟨distance, known, by omega⟩
    · by_cases goal : target vertex
      · have zero := runLabels_goal_zero input goals vertices vertex ((goals_correct vertex).mp goal)
        have same : distance = 0 := Option.some.inj (known.symm.trans zero)
        exact ⟨distance, known, by omega⟩
      · by_cases own : arena.owner vertex = arena.player
        · rw [if_pos own] at step
          obtain ⟨child, legal, childInside⟩ := step
          obtain ⟨cost, childKnown, smaller⟩ := ih child childInside
          obtain ⟨edge, member, same⟩ := (matching.edges vertex child).mp legal
          have childLabel : runLabels input goals vertices (input.child edge) = some cost := by simpa only [same] using childKnown
          have upper := runLabels_own_bound input goals vertices covered vertex ((matching.owner vertex).mpr own)
            edge member distance cost known childLabel
          exact ⟨distance, known, by omega⟩
        · rw [if_neg own] at step
          have notGoal : vertex ∉ goals := fun member => goal ((goals_correct vertex).mpr member)
          have other : input.own vertex = false := by
            cases flag : input.own vertex with
            | false => rfl
            | true => exact False.elim (own ((matching.owner vertex).mp flag))
          obtain ⟨edge, member, cost, childKnown, witness⟩ := runLabels_other_witness input goals vertices vertex notGoal other distance known
          have legal := (matching.edges vertex (input.child edge)).mpr ⟨edge, member, rfl⟩
          obtain ⟨otherCost, otherLabel, smaller⟩ := ih (input.child edge) (step (input.child edge) legal)
          have same : cost = otherCost := Option.some.inj (childKnown.symm.trans otherLabel)
          exact ⟨distance, known, by omega⟩

/-- 一般目標の初期化からN回実行した実FIFOの全出力が、厳密な最短保証距離に一致する。 -/
theorem runLabels_exact (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) : runLabels input goals vertices vertex = arena.escapeDistance target vertices.length vertex := by
  classical
  cases known : runLabels input goals vertices vertex with
  | none =>
    have outside := (runLabels_none_iff input matching goals vertices goals_correct covered vertex).mp known
    simp [HistoryArena.escapeDistance, outside]
  | some distance =>
    have inside := (runLabels_finite_iff input matching goals vertices goals_correct covered vertex).mp ⟨distance, known⟩
    have lower := (runLabels_guarantees input matching goals vertices goals_correct covered vertex distance known).1
    have rank := (arena.escapeRank_spec target vertices.length vertex inside).2.1
    obtain ⟨cost, label, upper⟩ := runLabels_layer_bound input matching goals vertices goals_correct covered _ vertex rank
    have same : distance = cost := Option.some.inj (known.symm.trans label)
    have equal : distance = arena.escapeRank target vertices.length vertex := by omega
    simp [HistoryArena.escapeDistance, inside, equal]

theorem runLabels_reference (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (reference : HistoryArena.EscapeInput arena target) (vertex : V) :
    runLabels input goals vertices vertex = reference.computedDistance vertices.length vertex := by
  rw [reference.computedDistance_eq]
  exact runLabels_exact input matching goals vertices goals_correct covered vertex

/-- チェッカー受理を仮定せず、実行の保存証明から受理することを導く。 -/
theorem runLabels_checked (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (reference : HistoryArena.EscapeInput arena target) :
    reference.tableCheck (runLabels input goals vertices) vertices = true := by
  apply (reference.tableCheck_iff_exact _ vertices covered).mpr
  funext vertex
  exact runLabels_reference input matching goals vertices goals_correct covered reference vertex

end PetaProof.EscapePropagation.State
