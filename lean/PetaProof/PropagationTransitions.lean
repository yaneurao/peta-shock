import PetaProof.PropagationState

/-! 影の実行状態の確定領域の単調性と、局所集合の一括追加。 -/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

/-- 確定集合が広がっても、既に良い出口だった手は良い出口のままである。 -/
theorem goodExit_mono {old next : V → Prop} (inclusion : ∀ vertex, old vertex → next vertex)
    (move : Move V) (good : G.GoodExit old move) : G.GoodExit next move := by
  cases move with
  | node vertex => exact inclusion vertex good
  | leaf _ => exact good

namespace RankedRegion

/-- 集合の外延が同じなら、選択手・順位を変えずに証拠の添字だけを移す。 -/
def reindex {old next : V → Prop} (region : G.RankedRegion old)
    (same : ∀ vertex, old vertex ↔ next vertex) : G.RankedRegion next where
  choice := region.choice
  rank := region.rank
  stage := region.stage
  rank_bound := fun vertex inside => region.rank_bound vertex ((same vertex).mpr inside)
  chosen_legal := fun vertex inside => region.chosen_legal vertex ((same vertex).mpr inside)
  closed := by
    intro vertex inside move follows
    have good := region.closed vertex ((same vertex).mpr inside) move follows
    cases move with
    | node child => exact (same child).mp good
    | leaf _ => exact good
  decreasing := fun vertex child inside => region.decreasing vertex child ((same vertex).mpr inside)
  opponent_strict := fun vertex child inside => region.opponent_strict vertex child ((same vertex).mpr inside)

end RankedRegion

namespace PropagationState

variable [DecidableEq V] [DecidableEq E]

theorem won_notify_mono (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (edge : E) (vertex : V) (inside : state.won vertex) : (state.notify indexed edge).won vertex := by
  by_cases same : vertex = indexed.source edge
  · subst vertex
    change (state.counters (indexed.source edge)).admitted = true at inside
    simp [won, notify, HitCounter.hit, inside]
  · simpa only [won, notify, if_neg same] using inside

/-- 通知によって増える可能性があるのは、その辺の親だけである。 -/
theorem won_notify_iff (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (edge : E) (vertex : V) :
    (state.notify indexed edge).won vertex ↔ state.won vertex ∨
      (vertex = indexed.source edge ∧ (state.notify indexed edge).won (indexed.source edge)) := by
  by_cases same : vertex = indexed.source edge
  · subst vertex
    constructor
    · intro inside; exact Or.inr ⟨rfl, inside⟩
    · rintro (old | ⟨_, next⟩)
      · exact won_notify_mono indexed state edge _ old
      · exact next
  · simp [won, notify, same]

omit [DecidableEq E] in
theorem won_add_iff (state : PropagationState V E) (vertex other : V) :
    (state.add vertex).won other ↔ state.won other ∨ other = vertex := by
  by_cases same : other = vertex <;> simp [won, add, same]

omit [DecidableEq E] in
def addMany (state : PropagationState V E) : List V → PropagationState V E
  | [] => state
  | vertex :: rest => addMany (state.add vertex) rest

omit [DecidableEq E] in
theorem won_addMany_iff (state : PropagationState V E) (vertices : List V) (other : V) :
    (state.addMany vertices).won other ↔ state.won other ∨ other ∈ vertices := by
  induction vertices generalizing state with
  | nil => simp [addMany]
  | cons vertex rest ih =>
    rw [addMany, ih, won_add_iff, List.mem_cons]
    exact or_assoc

omit [DecidableEq E] in
theorem addMany_notified (state : PropagationState V E) (vertices : List V) :
    (state.addMany vertices).notified = state.notified := by
  induction vertices generalizing state with
  | nil => rfl
  | cons vertex rest ih => exact ih (state.add vertex)

omit [DecidableEq E] in
theorem addMany_preserves (indexed : G.IndexedMoves E) (state : PropagationState V E)
    (inv : Invariant indexed state) (vertices : List V) : Invariant indexed (state.addMany vertices) := by
  induction vertices generalizing state with
  | nil => exact inv
  | cons vertex rest ih => exact ih _ (add_preserves indexed state inv vertex)

end PropagationState
end PetaProof.ThresholdGame
