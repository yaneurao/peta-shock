import PetaProof.KosarajuStep

/-!
逆終了順の外側ループ。未割当頂点が残りの根に含まれることからHighestを導き、
各番号がちょうど一つのSCCを表す不変条件を実際のpassに沿って保つ。
-/
namespace PetaProof.KosarajuStep

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

/-- 一意な終了列では、列の順序とidxOfの大小が一致する。 -/
theorem finish_ranks_increase (finished : List V) (unique : finished.Nodup) :
    finished.Pairwise (fun a b => finished.idxOf a < finished.idxOf b) := by
  induction finished with
  | nil => simp
  | cons root rest ih =>
    obtain ⟨absent, nodup⟩ := List.nodup_cons.mp unique
    apply List.Pairwise.cons
    · intro vertex member
      have different : vertex ≠ root := by intro same; exact absent (same ▸ member)
      simp only [List.idxOf_cons, cond_eq_if, beq_iff_eq, if_neg (Ne.symm different), if_true]
      omega
    · apply (ih nodup).imp_of_mem
      intro a b ma mb earlier
      have na : a ≠ root := by intro same; exact absent (same ▸ ma)
      have nb : b ≠ root := by intro same; exact absent (same ▸ mb)
      simp only [List.idxOf_cons, cond_eq_if, beq_iff_eq, if_neg (Ne.symm na), if_neg (Ne.symm nb)]
      omega

theorem reverse_ranks_decrease (finished : List V) (unique : finished.Nodup) :
    finished.reverse.Pairwise (fun a b => finished.idxOf b < finished.idxOf a) := by
  rw [List.pairwise_reverse]
  exact finish_ranks_increase finished unique

/-- まだ割り当てられていない頂点は、今後走査する根の列に必ず残っている。 -/
def Pending (todo : List V) (previous : V → Option Nat) : Prop :=
  ∀ vertex, previous vertex = none → vertex ∈ todo

theorem head_highest (finished : List V) (root : V) (rest : List V)
    (decreasing : (root :: rest).Pairwise (fun a b => finished.idxOf b < finished.idxOf a))
    (previous : V → Option Nat) (pending : Pending (root :: rest) previous) :
    Highest finished previous root := by
  intro vertex fresh
  rcases List.mem_cons.mp (pending vertex fresh) with same | later
  · subst vertex; exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.mp decreasing).1 vertex later)

theorem step_pending (fuel : Nat) (parents : V → List V) (state : ComponentNumbering.State V)
    (root : V) (rest : List V) (pending : Pending (root :: rest) state.result) :
    Pending rest (ComponentNumbering.step fuel parents state root).result := by
  intro vertex fresh
  have old : state.result vertex = none := by
    cases assigned : state.result vertex with
    | none => rfl
    | some id =>
      have stable := ComponentNumbering.step_label_stable fuel parents state root vertex id assigned
      rw [fresh] at stable
      cases stable
  rcases List.mem_cons.mp (pending vertex old) with same | member
  · subst vertex
    obtain ⟨id, assigned⟩ := ComponentNumbering.step_root_assigned fuel parents state root
    rw [fresh] at assigned
    cases assigned
  · exact member

omit [DecidableEq V] in
def Accurate (outgoing : V → List (Option V)) (previous : V → Option Nat) : Prop :=
  ∀ a b id, previous a = some id → (previous b = some id ↔ Mutual outgoing a b)

omit [DecidableEq V] in
theorem initial_accurate (outgoing : V → List (Option V)) :
    Accurate outgoing (ComponentNumbering.initial : ComponentNumbering.State V).result := by
  intro a b id assigned
  cases assigned

theorem step_accurate (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last)
    (empty : last.stack = []) (listed : ∀ v, v ∈ last.finished)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state)
    (whole : Saturated outgoing state.result) (accurate : Accurate outgoing state.result)
    (root : V) (highest : Highest last.finished state.result root) :
    Accurate outgoing (ComponentNumbering.step vertices.length parents state root).result := by
  by_cases fresh : state.result root = none
  · have exact_component := descend_one_component vertices unique covered outgoing parents correct
      last run empty listed state valid whole root fresh highest
    have history := ComponentNumbering.descend_run vertices.length parents state root
    simp only [ComponentNumbering.step, if_pos fresh]
    intro a b id assigned
    rcases history.label_cases a with old | current
    · have old_a := old.symm.trans assigned
      have bound := valid.bounded a id old_a
      have old_b_iff : (ComponentNumbering.descend vertices.length parents state root).result b = some id ↔
          state.result b = some id := by
        constructor
        · intro found
          rcases history.label_cases b with kept | new
          · exact kept.symm.trans found
          · have equal := Option.some.inj (found.symm.trans new)
            omega
        · exact history.label_stable b id
      exact old_b_iff.trans (accurate a b id old_a)
    · have equal := Option.some.inj (assigned.symm.trans current)
      subst id
      have root_a := (exact_component a).mp current
      constructor
      · intro found
        have root_b := (exact_component b).mp found
        exact ⟨reach_trans root_a.2 root_b.1, reach_trans root_b.2 root_a.1⟩
      · intro same
        exact (exact_component b).mpr
          ⟨reach_trans root_a.1 same.1, reach_trans same.2 root_a.2⟩
  · simpa only [ComponentNumbering.step, if_neg fresh] using accurate

/-- 外側の走査位置も含めた不変条件。既存番号の意味を未割当マスクとは別に保持する。 -/
structure PassInvariant (outgoing : V → List (Option V)) (todo : List V)
    (state : ComponentNumbering.State V) : Prop where
  valid : ComponentNumbering.Invariant state
  whole : Saturated outgoing state.result
  accurate : Accurate outgoing state.result
  pending : Pending todo state.result

theorem pass_invariant (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last)
    (empty : last.stack = []) (listed : ∀ v, v ∈ last.finished)
    (todo : List V) (decreasing : todo.Pairwise (fun a b => last.finished.idxOf b < last.finished.idxOf a))
    (state : ComponentNumbering.State V) (inv : PassInvariant outgoing todo state) :
    PassInvariant outgoing [] (ComponentNumbering.pass vertices.length parents todo state) := by
  induction todo generalizing state with
  | nil => exact inv
  | cons root rest ih =>
    have highest := head_highest last.finished root rest decreasing state.result inv.pending
    apply ih (List.pairwise_cons.mp decreasing).2
    exact ⟨ComponentNumbering.step_preserves _ _ _ inv.valid root,
      step_preserves_saturated vertices unique covered outgoing parents correct last run empty listed
        state inv.valid inv.whole root (fun _ => highest),
      step_accurate vertices unique covered outgoing parents correct last run empty listed
        state inv.valid inv.whole inv.accurate root highest,
      step_pending _ _ _ root rest inv.pending⟩

/-- 実際の第一DFSと第二DFSをつないだ最終状態。SCC分割を入力として要求しない。 -/
theorem finish_accurate (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source) :
    Accurate outgoing (ComponentNumbering.finish vertices (ForwardDfs.order vertices roots outgoing) parents).result := by
  let last := ForwardDfs.finish vertices roots outgoing
  have listed := ForwardDfs.finish_covers vertices unique covered roots roots_cover outgoing
  have distinct := ForwardDfs.finish_unique vertices roots outgoing
  have inv : PassInvariant outgoing last.finished.reverse ComponentNumbering.initial :=
    ⟨ComponentNumbering.initial_invariant, by intro a b same; rfl,
      initial_accurate outgoing, by intro v fresh; exact List.mem_reverse.mpr (listed v)⟩
  exact (pass_invariant vertices unique covered outgoing parents correct last
    (ForwardDfs.finish_timeline vertices unique covered outgoing roots)
    (ForwardDfs.forest_drains vertices unique covered outgoing roots ForwardDfs.initial rfl)
    listed last.finished.reverse (reverse_ranks_decrease last.finished distinct)
    ComponentNumbering.initial inv).accurate

theorem component_eq_iff_mutual (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (a b : V) :
    ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents a =
      ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents b ↔ Mutual outgoing a b := by
  have covered_order := ForwardDfs.order_covers vertices unique covered roots roots_cover outgoing
  have assigned_a := ComponentNumbering.finish_result vertices _ parents covered_order a
  have assigned_b := ComponentNumbering.finish_result vertices _ parents covered_order b
  have exact_class := finish_accurate vertices unique covered roots roots_cover outgoing parents correct a b _ assigned_a
  rw [assigned_b, Option.some.injEq] at exact_class
  exact (eq_comm.trans exact_class)

end PetaProof.KosarajuStep
