import PetaProof.KosarajuPass

/-!
割当済み領域の逆辺閉性と番号のトポロジカル順を外側ループに沿って保つ。
これにより、実際の二つのDFSから既存のSccPartition証拠と循環core仕様へ接続する。
-/
namespace PetaProof.KosarajuStep

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

omit [DecidableEq V] in
structure EdgeInvariant (outgoing : V → List (Option V)) (previous : V → Option Nat) : Prop where
  closed : ∀ a b, Edge outgoing a b → previous b ≠ none → previous a ≠ none
  ordered : ∀ a b ia ib, Edge outgoing a b → previous a = some ia → previous b = some ib → ia ≤ ib

omit [DecidableEq V] in
theorem initial_edges (outgoing : V → List (Option V)) :
    EdgeInvariant outgoing (ComponentNumbering.initial : ComponentNumbering.State V).result := by
  constructor
  · intro a b edge assigned
    exact False.elim (assigned rfl)
  · intro a b ia ib edge assigned
    cases assigned

theorem step_edges (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last)
    (empty : last.stack = []) (listed : ∀ v, v ∈ last.finished)
    (state : ComponentNumbering.State V) (valid : ComponentNumbering.Invariant state)
    (whole : Saturated outgoing state.result) (edges : EdgeInvariant outgoing state.result)
    (root : V) (highest : Highest last.finished state.result root) :
    EdgeInvariant outgoing (ComponentNumbering.step vertices.length parents state root).result := by
  by_cases fresh : state.result root = none
  · have exact_component := descend_one_component vertices unique covered outgoing parents correct
      last run empty listed state valid whole root fresh highest
    have history := ComponentNumbering.descend_run vertices.length parents state root
    have lower (v : V) (assigned : state.result v ≠ none) :
        (ComponentNumbering.descend vertices.length parents state root).result v ≠ none := by
      cases old : state.result v with
      | none => exact False.elim (assigned old)
      | some id =>
        have stable := history.label_stable v id old
        rw [stable]
        exact Option.noConfusion
    have bound := (ComponentNumbering.step_preserves vertices.length parents state valid root).bounded
    simp only [ComponentNumbering.step, if_pos fresh] at bound ⊢
    constructor
    · intro a b edge assigned
      by_cases old_b : state.result b = none
      · have new_b : (ComponentNumbering.descend vertices.length parents state root).result b =
            some state.roots.length := by
          rcases history.label_cases b with kept | new
          · exact False.elim (assigned (kept.trans old_b))
          · exact new
        by_cases old_a : state.result a = none
        · have same_b := (exact_component b).mp new_b
          have back : Reach outgoing a root := reach_trans ⟨.cons edge (.nil b)⟩ same_b.2
          have same_a := fresh_predecessor_mutual outgoing last run empty listed state.result whole root highest a old_a back
          rw [(exact_component a).mpr same_a]
          exact Option.noConfusion
        · exact lower a old_a
      · exact lower a (edges.closed a b edge old_b)
    · intro a b ia ib edge assigned_a assigned_b
      rcases history.label_cases b with old | new
      · have old_b := old.symm.trans assigned_b
        change state.result b = some ib at old_b
        have not_none_b : state.result b ≠ none := by rw [old_b]; exact Option.noConfusion
        have not_none_a := edges.closed a b edge not_none_b
        cases found : state.result a with
        | none => exact False.elim (not_none_a found)
        | some id =>
          have stable := history.label_stable a id found
          have equal := Option.some.inj (assigned_a.symm.trans stable)
          subst ia
          exact edges.ordered a b id ib edge found old_b
      · have equal := Option.some.inj (assigned_b.symm.trans new)
        have upper := bound a ia assigned_a
        simp only [List.length_append, List.length_singleton] at upper
        omega
  · simpa only [ComponentNumbering.step, if_neg fresh] using edges

/-- 各反復でのHighestは、残りの逆終了順と未割当頂点の包含から導く。 -/
theorem pass_edges (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last)
    (empty : last.stack = []) (listed : ∀ v, v ∈ last.finished)
    (todo : List V) (decreasing : todo.Pairwise (fun a b => last.finished.idxOf b < last.finished.idxOf a))
    (state : ComponentNumbering.State V) (inv : PassInvariant outgoing todo state)
    (edges : EdgeInvariant outgoing state.result) :
    EdgeInvariant outgoing (ComponentNumbering.pass vertices.length parents todo state).result := by
  induction todo generalizing state with
  | nil => exact edges
  | cons root rest ih =>
    have highest := head_highest last.finished root rest decreasing state.result inv.pending
    have next_inv : PassInvariant outgoing rest (ComponentNumbering.step vertices.length parents state root) :=
      ⟨ComponentNumbering.step_preserves _ _ _ inv.valid root,
       step_preserves_saturated vertices unique covered outgoing parents correct last run empty listed
         state inv.valid inv.whole root (fun _ => highest),
       step_accurate vertices unique covered outgoing parents correct last run empty listed
         state inv.valid inv.whole inv.accurate root highest,
       step_pending _ _ _ root rest inv.pending⟩
    exact ih (List.pairwise_cons.mp decreasing).2 _ next_inv
      (step_edges vertices unique covered outgoing parents correct last run empty listed
        state inv.valid inv.whole edges root highest)

theorem finish_edges (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source) :
    EdgeInvariant outgoing (ComponentNumbering.finish vertices (ForwardDfs.order vertices roots outgoing) parents).result := by
  let last := ForwardDfs.finish vertices roots outgoing
  have listed := ForwardDfs.finish_covers vertices unique covered roots roots_cover outgoing
  have inv : PassInvariant outgoing last.finished.reverse ComponentNumbering.initial :=
    ⟨ComponentNumbering.initial_invariant, by intro a b same; rfl,
      initial_accurate outgoing, by intro v fresh; exact List.mem_reverse.mpr (listed v)⟩
  exact pass_edges vertices unique covered outgoing parents correct last
    (ForwardDfs.finish_timeline vertices unique covered outgoing roots)
    (ForwardDfs.forest_drains vertices unique covered outgoing roots ForwardDfs.initial rfl)
    listed last.finished.reverse
    (reverse_ranks_decrease last.finished (ForwardDfs.finish_unique vertices roots outgoing))
    ComponentNumbering.initial inv (initial_edges outgoing)

theorem component_ordered (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (a b : V) (edge : Edge outgoing a b) :
    ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents a ≤
      ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents b := by
  have order_cover := ForwardDfs.order_covers vertices unique covered roots roots_cover outgoing
  exact (finish_edges vertices unique covered roots roots_cover outgoing parents correct).ordered a b _ _ edge
    (ComponentNumbering.finish_result vertices _ parents order_cover a)
    (ComponentNumbering.finish_result vertices _ parents order_cover b)

/-- SCC分割の正しさを仮定せず、両DFSの計算結果そのものから証拠を構成する。 -/
def computedPartition (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source) :
    SccPartition (Edge outgoing) where
  component := ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents
  ordered := component_ordered vertices unique covered roots roots_cover outgoing parents correct
  connected := fun a b same =>
    ((component_eq_iff_mutual vertices unique covered roots roots_cover outgoing parents correct a b).mp same).1

theorem computed_core_correct (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (roots : List V) (roots_cover : ∀ v, v ∈ roots) (outgoing : V → List (Option V))
    (parents : V → List V) (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (selfLoop : V → Bool) (self_correct : ∀ v, selfLoop v = true ↔ Edge outgoing v v) (vertex : V) :
    vertex ∈ CoreEnumeration.core
      (ComponentCycleFlags.keep vertices
        (ComponentNumbering.component vertices (ForwardDfs.order vertices roots outgoing) parents) selfLoop) vertices ↔
      CyclicVertex (Edge outgoing) vertex := by
  exact ComponentNumbering.extracted_core_correct vertices unique covered _
    (ForwardDfs.order_covers vertices unique covered roots roots_cover outgoing) parents
    (component_ordered vertices unique covered roots roots_cover outgoing parents correct)
    (computedPartition vertices unique covered roots roots_cover outgoing parents correct).connected
    selfLoop self_correct vertex

end PetaProof.KosarajuStep
