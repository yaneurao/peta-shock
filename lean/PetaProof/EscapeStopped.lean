import PetaProof.EscapeStart
import PetaProof.EscapeDistanceTable

/-! 空キューで確定結果とpop済み集合が一致し、未確定側のmin/max条件を得る。 -/
namespace PetaProof.EscapePropagation.State

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable (input : Input V E)

omit [DecidableEq V] [DecidableEq E] in
theorem stopped_finite_iff (state : State V E) (coherent : Coherent state)
    (empty : state.frame.queue.pending = []) (vertex : V) :
    (∃ distance, (state.counters vertex).result = some distance) ↔ vertex ∈ state.frame.queue.popped.map Prod.fst := by
  constructor
  · rintro ⟨distance, known⟩
    have member := (coherent vertex distance).mp known
    simp only [EscapeFifo.State.total, empty, List.append_nil] at member
    exact List.mem_map.mpr ⟨(vertex, distance), member, rfl⟩
  · intro inside
    obtain ⟨item, member, same⟩ := List.mem_map.mp inside
    refine ⟨item.2, (coherent vertex item.2).mpr ?_⟩
    simp only [EscapeFifo.State.total, empty, List.append_nil]
    simpa only [← same, Prod.eta] using member

omit [DecidableEq V] [DecidableEq E] in
theorem outside_is_none (state : State V E) (coherent : Coherent state)
    (empty : state.frame.queue.pending = []) (vertex : V)
    (outside : vertex ∉ state.frame.queue.popped.map Prod.fst) : (state.counters vertex).result = none := by
  cases known : (state.counters vertex).result with
  | none => rfl
  | some distance => exact False.elim (outside ((stopped_finite_iff state coherent empty vertex).mp ⟨distance, known⟩))

omit [DecidableEq V] [DecidableEq E] in
/-- 既に「未pop」ではなく、実際の未確定結果noneについて全子の条件を述べられる。 -/
theorem stopped_own_infinite (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (complete : Complete input state) (empty : state.frame.queue.pending = [])
    (vertex : V) (own : input.own vertex = true) (pending : (state.counters vertex).result = none)
    (edge : E) (member : edge ∈ input.outgoing vertex) : (state.counters (input.child edge)).result = none :=
  outside_is_none state coherent empty (input.child edge)
    (pending_own_outside input state inv complete vertex own pending edge member)

omit [DecidableEq V] [DecidableEq E] in
theorem stopped_other_infinite (state : State V E) (inv : Invariant input state) (coherent : Coherent state)
    (complete : Complete input state) (empty : state.frame.queue.pending = [])
    (vertex : V) (pending : (state.counters vertex).result = none) :
    ∃ edge ∈ input.outgoing vertex, (state.counters (input.child edge)).result = none := by
  obtain ⟨edge, member, outside⟩ := pending_child_outside input state inv complete vertex pending
  exact ⟨edge, member, outside_is_none state coherent empty _ outside⟩

/-- 実際の初期化とN回の実行から、未確定自分番の最終表条件へつなぐ。 -/
theorem started_run_own_infinite (goals : List V) (state : State V E) (started : start input goals = some state)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V)
    (own : input.own vertex = true) (pending : ((run input vertices.length state).counters vertex).result = none)
    (edge : E) (member : edge ∈ input.outgoing vertex) :
    ((run input vertices.length state).counters (input.child edge)).result = none := by
  obtain ⟨inv, coherent, complete⟩ := started_run_good input goals state started vertices.length
  exact stopped_own_infinite input _ inv coherent complete (started_run_drained input goals state started vertices covered)
    vertex own pending edge member

theorem started_run_other_infinite (goals : List V) (state : State V E) (started : start input goals = some state)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V)
    (pending : ((run input vertices.length state).counters vertex).result = none) :
    ∃ edge ∈ input.outgoing vertex, ((run input vertices.length state).counters (input.child edge)).result = none := by
  obtain ⟨inv, coherent, complete⟩ := started_run_good input goals state started vertices.length
  exact stopped_other_infinite input _ inv coherent complete (started_run_drained input goals state started vertices covered)
    vertex pending

/-- 空目標では全頂点none、それ以外は目標初期化からN回実行した確定結果を返す。 -/
def runLabels (goals vertices : List V) (vertex : V) : Option Nat :=
  match start input goals with
  | none => none
  | some state => ((run input vertices.length state).counters vertex).result

theorem runLabels_goal_zero (goals vertices : List V) (vertex : V) (goal : vertex ∈ goals) :
    runLabels input goals vertices vertex = some 0 := by
  cases started : start input goals with
  | none =>
    have empty := (start_none_iff input goals).mp started
    rw [empty] at goal
    cases goal
  | some state =>
    simpa only [runLabels, started] using started_run_goal_zero input goals state started vertices.length vertex goal

theorem runLabels_own_infinite (goals vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (own : input.own vertex = true) (pending : runLabels input goals vertices vertex = none)
    (edge : E) (member : edge ∈ input.outgoing vertex) : runLabels input goals vertices (input.child edge) = none := by
  cases started : start input goals with
  | none => simp [runLabels, started]
  | some state =>
    have unresolved : ((run input vertices.length state).counters vertex).result = none := by
      simpa only [runLabels, started] using pending
    simpa only [runLabels, started] using
      started_run_own_infinite input goals state started vertices covered vertex own unresolved edge member

theorem runLabels_other_infinite (goals vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (pending : runLabels input goals vertices vertex = none) :
    ∃ edge ∈ input.outgoing vertex, runLabels input goals vertices (input.child edge) = none := by
  cases started : start input goals with
  | none =>
    have nonempty := input.outgoing_nonempty vertex
    cases outgoing : input.outgoing vertex with
    | nil => simp [outgoing] at nonempty
    | cons edge rest => exact ⟨edge, by simp [outgoing], by simp [runLabels, started]⟩
  | some state =>
    have unresolved : ((run input vertices.length state).counters vertex).result = none := by
      simpa only [runLabels, started] using pending
    simpa only [runLabels, started] using
      started_run_other_infinite input goals state started vertices covered vertex unresolved

end PetaProof.EscapePropagation.State

namespace PetaProof.HistoryArena

universe u
variable {V : Type u} {A : HistoryArena V} {target : V → Prop}

/-- 目標が空なら全頂点noneが正しい。処理枠やダミーの開始頂点は不要。 -/
theorem empty_target_table (noGoals : ∀ vertex, ¬ target vertex) :
    EscapeTable A target (fun _ => none) := by
  constructor
  · intro vertex goal
    exact False.elim (noGoals vertex goal)
  · intro vertex distance _ _ impossible
    cases impossible
  · intro vertex distance _ _ impossible
    cases impossible
  · intro vertex _ _ _ child _
    rfl
  · intro vertex _ _ _
    obtain ⟨child, edge⟩ := A.moves_exist vertex
    exact ⟨child, edge, rfl⟩

theorem empty_target_exact (input : EscapeInput A target) (noGoals : ∀ vertex, ¬ target vertex)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (vertex : V) :
    input.computedDistance vertices.length vertex = none :=
  ((empty_target_table noGoals).agrees_with_reference input vertices covered vertex).symm

end PetaProof.HistoryArena
