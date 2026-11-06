import PetaProof.QueueScanAccounting

/-!
全閾値走査と同じ分岐から局所解析の返却集合を記録する証明用ログ。
空の返却も一回と数える。解析の内部処理を定数時間とは仮定しない。
-/
namespace PetaProof

universe u
variable {V : Type u}

/-- 記録した頂点は重複せず、開始時には未確定、終了時には確定している。 -/
structure FreshAdmissions (before after : V → Prop) (items : List V) : Prop where
  mono : ∀ vertex, before vertex → after vertex
  unique : items.Nodup
  fresh : ∀ vertex ∈ items, ¬ before vertex
  admitted : ∀ vertex ∈ items, after vertex

namespace FreshAdmissions

theorem empty {before after : V → Prop} (mono : ∀ vertex, before vertex → after vertex) :
    FreshAdmissions before after [] := ⟨mono, List.nodup_nil, by simp, by simp⟩

theorem trans {before middle after : V → Prop} {first second : List V}
    (left : FreshAdmissions before middle first) (right : FreshAdmissions middle after second) :
    FreshAdmissions before after (first ++ second) := by
  refine ⟨fun v h => right.mono v (left.mono v h), ?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨left.unique, right.unique, ?_⟩
    intro a ha b hb same
    exact right.fresh b hb (same ▸ left.admitted a ha)
  · intro v member old
    rcases List.mem_append.mp member with h | h
    · exact left.fresh v h old
    · exact right.fresh v h (left.mono v old)
  · intro v member
    rcases List.mem_append.mp member with h | h
    · exact right.mono v (left.admitted v h)
    · exact right.admitted v h

end FreshAdmissions

namespace LocalCalls

variable [DecidableEq V]

/-- 各非空返却を少なくとも一頂点に課金する。空返却は別に残す。 -/
theorem calls_le (calls : List (List V)) :
    calls.length ≤ calls.flatten.length + calls.count [] := by
  induction calls with
  | nil => simp
  | cons batch rest ih =>
    cases batch with
    | nil => simpa only [List.length_cons, List.flatten_cons, List.nil_append,
        List.count_cons_self] using Nat.add_le_add_right ih 1
    | cons vertex tail =>
      simp only [List.length_cons, List.flatten_cons, List.length_append, List.count_cons,
        List.cons_ne_nil, if_false]
      omega

end LocalCalls
end PetaProof

namespace PetaProof.ThresholdGame.PropagationState

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]

theorem notifyMany_won_mono (indexed : G.IndexedMoves E) (state : PropagationState V E) (edges : List E) :
    ∀ vertex, state.won vertex → (state.notifyMany indexed edges).won vertex := by
  induction edges generalizing state with
  | nil => exact fun _ h => h
  | cons edge rest ih => exact fun v h => ih _ v (won_notify_mono indexed state edge v h)

theorem drainQueue_won_mono (indexed : G.IndexedMoves E) (parents : ParentLists indexed)
    (fuel : Nat) (state : PropagationState V E) :
    ∀ vertex, state.won vertex → (drainQueue indexed parents fuel state).won vertex := by
  induction fuel generalizing state with
  | zero => exact fun _ h => h
  | succ fuel ih =>
    intro v h
    apply ih _ v
    cases pending : state.queue.pending with
    | nil => simpa [queueVisit, pending] using h
    | cons target rest =>
      simpa only [queueVisit, pending] using
        notifyFreshMany_mono indexed state.pop (parents.incoming target) v h

end PetaProof.ThresholdGame.PropagationState

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable [DecidableEq V] [DecidableEq E]
variable (ctx : QueueContext G E)

/-- 燃料ゼロでは解析を呼ばず、通常FIFOを排出するだけである。 -/
def localCalls : Nat → PropagationState V E → List (List V)
  | 0, _ => []
  | fuel + 1, state =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    if members = [] then [[]] else members :: localCalls fuel (closed.addMany members)

theorem localMembers_core (state : PropagationState V E) (vertex : V)
    (inside : vertex ∈ ctx.localMembers state) : ctx.core vertex = true :=
  (G.iterate_subset ctx.vertices.length vertex ((ctx.localMembers_iff state vertex).mp inside)).1

theorem localCalls_fresh (fuel : Nat) (state : PropagationState V E) :
    FreshAdmissions state.won (ctx.settleQueue fuel state).won (ctx.localCalls fuel state).flatten := by
  induction fuel generalizing state with
  | zero => exact FreshAdmissions.empty (PropagationState.drainQueue_won_mono _ _ _ _)
  | succ fuel ih =>
    let closed := ctx.drain state
    let members := ctx.localMembers closed
    have drained : FreshAdmissions state.won closed.won [] :=
      FreshAdmissions.empty (PropagationState.drainQueue_won_mono _ _ _ _)
    by_cases empty : members = []
    · change ctx.localMembers (ctx.drain state) = [] at empty
      simpa only [localCalls, settleQueue, if_pos empty, List.flatten_cons, List.flatten_nil,
        List.nil_append] using drained
    · have added : FreshAdmissions closed.won (closed.addMany members).won members := by
        refine ⟨fun v h => (PropagationState.won_addMany_iff closed members v).mpr (Or.inl h),
          ctx.unique.filter _, (ctx.localBatch closed).fresh, ?_⟩
        intro v member
        exact (PropagationState.won_addMany_iff closed members v).mpr (Or.inr member)
      have result := drained.trans (added.trans (ih (closed.addMany members)))
      change ¬ ctx.localMembers (ctx.drain state) = [] at empty
      simpa only [localCalls, settleQueue, if_neg empty, List.flatten_cons, List.nil_append] using result

theorem localCalls_core (fuel : Nat) (state : PropagationState V E) (vertex : V)
    (member : vertex ∈ (ctx.localCalls fuel state).flatten) : ctx.core vertex = true := by
  induction fuel generalizing state with
  | zero => cases member
  | succ fuel ih =>
    by_cases empty : ctx.localMembers (ctx.drain state) = []
    · simp [localCalls, empty] at member
    · simp only [localCalls, if_neg empty, List.flatten_cons, List.mem_append] at member
      exact member.elim (fun h => ctx.localMembers_core _ vertex h) (fun h => ih _ h)

theorem localCalls_empty_bound (fuel : Nat) (state : PropagationState V E) :
    (ctx.localCalls fuel state).count [] ≤ 1 := by
  induction fuel generalizing state with
  | zero => simp [localCalls]
  | succ fuel ih =>
    by_cases empty : ctx.localMembers (ctx.drain state) = []
    · simp [localCalls, empty]
    · simpa [localCalls, empty, List.count_cons] using ih ((ctx.drain state).addMany _)

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanLocalCalls : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) →
    PropagationState V E → List (List V)
  | _, _, [], _, _ => []
  | G, ctx, t :: rest, valid, state =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    low.localCalls ctx.vertices.length (ctx.prepare t positive bounded state) ++
      scanLocalCalls (G.retune t positive bounded) low rest
        (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)

theorem scanLocalCalls_fresh (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) (values : V → Int) :
    FreshAdmissions state.won (scanQueues G ctx levels valid state values).1.won
      (scanLocalCalls G ctx levels valid state).flatten := by
  induction levels generalizing G state values with
  | nil => exact FreshAdmissions.empty (fun _ h => h)
  | cons t rest ih =>
    let positive := (valid t (by simp)).1
    let bounded := (valid t (by simp)).2
    let low := ctx.atLevel t positive bounded
    let prepared := ctx.prepare t positive bounded state
    have prepareMono : FreshAdmissions state.won prepared.won [] :=
      FreshAdmissions.empty (PropagationState.notifyMany_won_mono _ _ _)
    have first := low.localCalls_fresh ctx.vertices.length prepared
    have tailResult := ih (G.retune t positive bounded) low
      (fun s member => valid s (by simp [member])) (ctx.phase t positive bounded state)
      (latchValues values t (fun vertex => ((ctx.phase t positive bounded state).counters vertex).admitted))
    simpa only [scanLocalCalls, List.flatten_append, List.nil_append, scanQueues] using
      prepareMono.trans (first.trans tailResult)

theorem scanLocalCalls_core (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (state : PropagationState V E) (vertex : V)
    (member : vertex ∈ (scanLocalCalls G ctx levels valid state).flatten) : ctx.core vertex = true := by
  induction levels generalizing G state with
  | nil => cases member
  | cons t rest ih =>
    simp only [scanLocalCalls, List.flatten_append, List.mem_append] at member
    rcases member with first | later
    · exact (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2).localCalls_core _ _ vertex first
    · exact ih (G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
        (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2)
        (fun s present => valid s (by simp [present])) _ later

theorem scanLocalCalls_empty_bound (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    (scanLocalCalls G ctx levels valid state).count [] ≤ levels.length := by
  induction levels generalizing G state with
  | nil => simp [scanLocalCalls]
  | cons t rest ih =>
    have first := (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2).localCalls_empty_bound
      ctx.vertices.length (ctx.prepare t (valid t (by simp)).1 (valid t (by simp)).2 state)
    have tailResult := ih (G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
      (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2)
      (fun s member => valid s (by simp [member]))
      (ctx.phase t (valid t (by simp)).1 (valid t (by simp)).2 state)
    simp only [scanLocalCalls, List.count_append, List.length_cons]
    omega

namespace QueueContext

variable {G : ThresholdGame V} (ctx : QueueContext G E)

/-- 局所解析の対象となる王手循環候補数。過大近似されたcoreでも成立する。 -/
def coreSize : Nat := (ctx.vertices.filter ctx.core).length

theorem scanLocalCalls_vertices_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    (scanLocalCalls G ctx levels valid state).flatten.length ≤ ctx.coreSize := by
  apply DistinctWork.length_le _ _ (scanLocalCalls_fresh G ctx levels valid state (fun _ => 0)).unique
  intro vertex member
  exact List.mem_filter.mpr ⟨ctx.covered vertex, scanLocalCalls_core G ctx levels valid state vertex member⟩

/-- 非空返却数はcore数以下。初期状態・閾値数に依存して増えない。 -/
theorem scanLocalCalls_nonempty_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    (scanLocalCalls G ctx levels valid state).length -
      (scanLocalCalls G ctx levels valid state).count [] ≤ ctx.coreSize := by
  have charged := LocalCalls.calls_le (scanLocalCalls G ctx levels valid state)
  have vertices := ctx.scanLocalCalls_vertices_bound levels valid state
  omega

/-- 全閾値を通した局所解析の呼び出し回数はK+D以下。各呼び出しの時間は別途必要。 -/
theorem scanLocalCalls_bound (levels : List Int)
    (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) (state : PropagationState V E) :
    (scanLocalCalls G ctx levels valid state).length ≤ ctx.coreSize + levels.length := by
  have charged := LocalCalls.calls_le (scanLocalCalls G ctx levels valid state)
  have vertices := ctx.scanLocalCalls_vertices_bound levels valid state
  have emptyCalls := scanLocalCalls_empty_bound G ctx levels valid state
  omega

end QueueContext
end PetaProof.ThresholdGame
