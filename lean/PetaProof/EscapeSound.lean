import PetaProof.EscapeNone

/-! 有限の確定ラベルdには、実際にd手以内で目標へ到達できる証拠がある。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E) {arena : HistoryArena V} {target : V → Prop}

def Sound (arena : HistoryArena V) (target : V → Prop) (state : State V E) : Prop :=
  ∀ vertex distance, (state.counters vertex).result = some distance → arena.escapeLayer target distance vertex

omit [DecidableEq V] [DecidableEq E] in
theorem popped_sound (state : State V E) (coherent : Coherent state) (sound : Sound arena target state)
    (vertex : V) (distance : Nat) (logged : (vertex, distance) ∈ state.frame.queue.popped) :
    arena.escapeLayer target distance vertex :=
  sound vertex distance ((coherent vertex distance).mpr (List.mem_append_left _ logged))

/-- 記録済み子の距離と実pop履歴から、新規確定する親の到達証拠を作る。 -/
theorem notifyKnown_sound (matching : ArenaMatch input arena) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state) (edge : E)
    (fresh : state.notified edge = false) (currentChild : input.child edge = state.frame.child)
    (currentCost : state.received edge = state.frame.distance) : Sound arena target (notifyKnown input state edge) := by
  let parent := input.source edge
  have member : edge ∈ input.outgoing parent := (input.outgoing_correct parent edge).mpr rfl
  have currentLayer : arena.escapeLayer target state.frame.distance (input.child edge) := by
    rw [currentChild]
    exact popped_sound state coherent sound _ _ inv.frame.active_logged
  have oldLayer (other : E) (inRow : other ∈ input.outgoing parent)
      (seen : (state.counters parent).seen other = true) :
      arena.escapeLayer target state.frame.distance (input.child other) := by
    have logged := inv.notified_logged other (inv.seen_notified parent other inRow seen)
    exact arena.escapeLayer_mono target (inv.frame.past_bound _ logged) _
      (popped_sound state coherent sound _ _ logged)
  intro vertex distance known
  by_cases same : vertex = parent
  · subst vertex
    cases prior : (state.counters parent).result with
    | some oldDistance =>
      have stable := notifyKnown_result_stable input state edge parent oldDistance prior
      have equal : oldDistance = distance := Option.some.inj (stable.symm.trans known)
      simpa only [equal] using sound parent oldDistance prior
    | none =>
      let next := EscapeCounter.hit (input.own parent) (state.counters parent) edge state.frame.distance
      have ready : next.result = some distance := by
        have priorSource : (state.counters (input.source edge)).result = none := prior
        simpa only [notifyKnown, EscapeFifo.Frame.notifyParent, priorSource, Option.isSome_none,
          Bool.false_eq_true, ite_false, parent, if_pos rfl] using known
      have localFresh : (state.counters parent).seen edge = false := by
        rw [inv.pending_history parent prior edge member, fresh]
      have peak : (state.counters parent).peak ≤ state.frame.distance := by
        rw [(inv.counters parent).exact_peak, EscapeCounter.seenMaximum_bound]
        intro other inRow seen
        exact inv.frame.past_bound _ (inv.notified_logged other (inv.seen_notified parent other inRow seen))
      have form := EscapeCounter.hit_current_distance (input.own parent) (state.counters parent)
        edge state.frame.distance prior peak
      have equal : distance = state.frame.distance + 1 := by
        change (EscapeCounter.hit _ _ _ _).result = some distance at ready
        rw [form] at ready
        split at ready
        · exact (Option.some.inj ready).symm
        · cases ready
      rw [equal]
      apply Or.inr
      cases own : input.own parent with
      | true =>
        rw [if_pos ((matching.owner parent).mp own)]
        exact ⟨input.child edge, (matching.edges parent _).mpr ⟨edge, member, rfl⟩, currentLayer⟩
      | false =>
        have other : arena.owner parent ≠ arena.player := by
          intro ownArena
          have impossible := (matching.owner parent).mpr ownArena
          rw [own] at impossible
          cases impossible
        rw [if_neg other]
        have finished : (EscapeCounter.hit false (state.counters parent) edge (state.received edge)).result.isSome = true := by
          rw [currentCost, ← own]
          change next.result.isSome = true
          rw [ready]
          rfl
        have allSeen := (EscapeCounter.and_hit_complete (state.counters parent) edge (input.outgoing parent)
          state.received (inv.counters parent) (input.outgoing_unique parent) member localFresh prior).mp finished
        intro child legal
        obtain ⟨move, inRow, childEqual⟩ := (matching.edges parent child).mp legal
        rcases (markSeen_true_iff (state.counters parent).seen edge move).mp (allSeen move inRow) with sameEdge | earlier
        · subst move
          simpa only [childEqual] using currentLayer
        · simpa only [childEqual] using oldLayer move inRow earlier
  · have knownOld : (state.counters vertex).result = some distance := by
      have different : vertex ≠ input.source edge := same
      simpa only [notifyKnown, if_neg different] using known
    exact sound vertex distance knownOld

theorem notify_sound (matching : ArenaMatch input arena) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state) (edge : E)
    (fresh : state.notified edge = false) (currentChild : input.child edge = state.frame.child) :
    Sound arena target (notify input state edge) := by
  apply notifyKnown_sound input matching (state.record edge) (record_preserves input state inv edge fresh)
    coherent sound edge fresh currentChild
  simp [record]

theorem notifyMany_sound (matching : ArenaMatch input arena) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state)
    (edges : List E) (unique : edges.Nodup) (fresh : ∀ edge ∈ edges, state.notified edge = false)
    (current : ∀ edge ∈ edges, input.child edge = state.frame.child) :
    Sound arena target (notifyMany input state edges) := by
  induction edges generalizing state with
  | nil => exact sound
  | cons edge rest ih =>
    have parts := List.nodup_cons.mp unique
    have newInv := notify_preserves input state inv edge (fresh edge (by simp)) (current edge (by simp))
    have newSound := notify_sound input matching state inv coherent sound edge (fresh edge (by simp)) (current edge (by simp))
    apply ih (notify input state edge) newInv (notify_coherent input state inv.frame.queue coherent edge) newSound parts.2
    · intro other member
      rw [notify_notified]
      have different : other ≠ edge := by intro equal; exact parts.1 (equal ▸ member)
      simp only [markSeen, if_neg different]
      exact fresh other (by simp [member])
    · intro other member
      exact (current other (by simp [member])).trans (notify_position input state edge).1.symm

theorem notifyIncoming_sound (matching : ArenaMatch input arena) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state)
    (fresh : ∀ edge ∈ input.incoming state.frame.child, state.notified edge = false) :
    Sound arena target (notifyIncoming input state) :=
  notifyMany_sound input matching state inv coherent sound _ (input.incoming_unique _) fresh
    (fun edge member => (input.incoming_correct _ edge).mp member)

theorem advance_sound (matching : ArenaMatch input arena) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state) :
    Sound arena target (advance input state) := by
  cases pending : state.frame.queue.pending with
  | nil => simpa only [advance, pending] using sound
  | cons head rest =>
    simp only [advance, pending]
    exact notifyIncoming_sound input matching (state.openNext head) (openNext_preserves input state inv head rest pending)
      (openNext_coherent state coherent head) sound (openNext_fresh input state inv head rest pending)

theorem run_sound (matching : ArenaMatch input arena) (fuel : Nat) (state : State V E)
    (inv : Invariant input state) (coherent : Coherent state) (sound : Sound arena target state) :
    Sound arena target (run input fuel state) := by
  induction fuel generalizing state with
  | zero => exact sound
  | succ fuel ih =>
    exact ih _ (advance_preserves input state inv) (advance_coherent input state inv coherent)
      (advance_sound input matching state inv coherent sound)

omit [DecidableEq E] in
theorem initialGoals_sound (goals : List V) (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals)
    (frame : EscapeFifo.Frame V) :
    Sound arena target (initialGoals input (fun vertex => decide (vertex ∈ goals)) frame) := by
  intro vertex distance known
  by_cases goal : vertex ∈ goals
  · have zero : distance = 0 := by
      simpa [initialGoals, goal, EscapeCounter.initial, eq_comm] using known
    rw [zero]
    exact (goals_correct vertex).mpr goal
  · simp [initialGoals, goal, EscapeCounter.initial] at known

theorem start_sound (matching : ArenaMatch input arena) (goals : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals)
    (state : State V E) (started : start input goals = some state) : Sound arena target state := by
  cases pending : (EscapeFifo.seeded goals).pending with
  | nil => simp [start, pending] at started
  | cons head rest =>
    let frame : EscapeFifo.Frame V := ⟨head.1, head.2, EscapeFifo.pop (EscapeFifo.seeded goals)⟩
    let initialState := initialGoals input (fun vertex => decide (vertex ∈ goals)) frame
    have equal : notifyIncoming input initialState = state := by
      simpa only [start, pending, Option.some.injEq] using started
    rw [← equal]
    have valid : frame.Invariant := EscapeFifo.Frame.begin_preserves (EscapeFifo.seeded goals)
      (EscapeFifo.seeded_invariant goals) head rest pending
    exact notifyIncoming_sound input matching initialState (initialGoals_invariant input _ frame valid)
      (initialGoals_coherent input goals head) (initialGoals_sound input goals goals_correct frame)
      (by intro edge _; rfl)

/-- 最終表を仮定せず、目標初期化と実通知制御から有限ラベルの到達証拠を得る。 -/
theorem runLabels_sound (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (vertex : V) (distance : Nat)
    (known : runLabels input goals vertices vertex = some distance) :
    arena.escapeLayer target distance vertex := by
  cases started : start input goals with
  | none => simp [runLabels, started] at known
  | some state =>
    obtain ⟨inv, coherent, _⟩ := start_good input goals state started
    have sound := run_sound input matching vertices.length state inv coherent (start_sound input matching goals goals_correct state started)
    apply sound vertex distance
    simpa only [runLabels, started] using known

/-- 到達可能な頂点の分類は、有限距離の数値最適性とは独立に完全一致する。 -/
theorem runLabels_finite_iff (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) : (∃ distance, runLabels input goals vertices vertex = some distance) ↔
      arena.escapeLayer target vertices.length vertex := by
  constructor
  · rintro ⟨distance, known⟩
    exact arena.escapeLayer_complete target vertices covered distance vertex
      (runLabels_sound input matching goals vertices goals_correct vertex distance known)
  · intro inside
    have notNone := (runLabels_none_certificate input matching goals vertices goals_correct covered).layer_not_none
      vertices.length vertex inside
    cases label : runLabels input goals vertices vertex with
    | none => exact False.elim (notNone label)
    | some distance => exact ⟨distance, rfl⟩

theorem runLabels_none_iff (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) : runLabels input goals vertices vertex = none ↔
      ¬ arena.escapeLayer target vertices.length vertex := by
  constructor
  · intro unresolved
    exact (runLabels_none_certificate input matching goals vertices goals_correct covered).none_outside
      vertex unresolved vertices.length
  · intro outside
    cases label : runLabels input goals vertices vertex with
    | none => rfl
    | some distance =>
      exact False.elim (outside ((runLabels_finite_iff input matching goals vertices goals_correct covered vertex).mp ⟨distance, label⟩))

/-- 報告距離は実現可能な上界であり、真の最短距離を過小評価しない。等号はまだ主張しない。 -/
theorem runLabels_guarantees (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (distance : Nat) (known : runLabels input goals vertices vertex = some distance) :
    arena.escapeRank target vertices.length vertex ≤ distance ∧
      ∃ strategy : arena.Strategy, arena.escapeWithin target strategy [] distance vertex := by
  have inside := (runLabels_finite_iff input matching goals vertices goals_correct covered vertex).mp ⟨distance, known⟩
  have bound := (arena.escapeRank_le_iff target vertices.length vertex inside distance).mpr
    (runLabels_sound input matching goals vertices goals_correct vertex distance known)
  exact ⟨bound, (arena.escape_minimax target vertices covered vertex inside distance).mpr bound⟩

theorem runLabels_finite_iff_guarantee (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) : (∃ distance, runLabels input goals vertices vertex = some distance) ↔
      ∃ strategy : arena.Strategy, ∃ bound, arena.escapeWithin target strategy [] bound vertex := by
  constructor
  · rintro ⟨distance, known⟩
    obtain ⟨strategy, guaranteed⟩ := (runLabels_guarantees input matching goals vertices goals_correct covered vertex distance known).2
    exact ⟨strategy, distance, guaranteed⟩
  · rintro ⟨strategy, bound, guaranteed⟩
    apply (runLabels_finite_iff input matching goals vertices goals_correct covered vertex).mpr
    exact arena.escapeLayer_complete target vertices covered bound vertex
      (arena.escapeWithin_layer target strategy [] bound vertex guaranteed)

end PetaProof.EscapePropagation.State
