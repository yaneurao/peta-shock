import PetaProof.ReverseDfsReach
import PetaProof.ForwardDfsSccOrder

/-!
最大終了順位の未割当根からの第二DFSは、一つのSCCだけを過不足なく取り出す。
既割当がSCC単位であることと根の順位条件は、外側の走査から渡す前提として明示する。
-/
namespace PetaProof.KosarajuStep

universe u
variable {V : Type u} [DecidableEq V]
open ForwardDfs

def Saturated (outgoing : V → List (Option V)) (previous : V → Option Nat) : Prop :=
  ∀ a b, Mutual outgoing a b → (previous a = none ↔ previous b = none)

def Highest (finished : List V) (previous : V → Option Nat) (root : V) : Prop :=
  ∀ vertex, previous vertex = none → finished.idxOf vertex ≤ finished.idxOf root

omit [DecidableEq V] in
theorem fresh_walk_endpoint (previous : V → Option Nat) (parents : V → List V)
    {source target : V} (path : Walk (ReverseDfsStack.FreshEdge previous parents) source target) :
    previous source = none → previous target = none := by
  induction path with
  | nil => exact id
  | cons edge _ ih => intro _; exact ih edge.2.2

omit [DecidableEq V] in
theorem fresh_reverse_to_original (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (previous : V → Option Nat) (root vertex : V)
    (reachable : ReverseDfsStack.FreshReach previous parents root vertex) : Reach outgoing vertex root := by
  obtain ⟨path⟩ : Nonempty (Walk (ReverseDfsStack.FreshEdge previous parents) root vertex) := reachable
  have mapped : Walk (fun a b => Edge outgoing b a) root vertex :=
    path.map (fun a b edge => (correct a b).mp edge.1)
  exact ⟨mapped.reverse⟩

/-- 根へ到達する別の未割当SCCがあれば、その最大順位が根より大きくなり矛盾する。 -/
theorem fresh_predecessor_mutual (outgoing : V → List (Option V)) (last : ForwardDfs.State V)
    (run : Timeline outgoing ForwardDfs.initial last) (empty : last.stack = [])
    (listed : ∀ vertex, vertex ∈ last.finished) (previous : V → Option Nat)
    (whole : Saturated outgoing previous) (root : V) (highest : Highest last.finished previous root)
    (vertex : V) (fresh : previous vertex = none) (back : Reach outgoing vertex root) :
    Mutual outgoing root vertex := by
  refine ⟨?_, back⟩
  apply Classical.byContradiction
  intro no_forward
  obtain ⟨representative, same, latest⟩ := latest_exists outgoing last listed vertex
  have representative_fresh := (whole vertex representative same).mp fresh
  have bounded := highest representative representative_fresh
  have onward := reach_trans same.2 back
  have no_return : ¬Reach outgoing root representative := by
    intro reached
    exact no_forward (reach_trans reached same.2)
  have later := latest_reaches_earlier outgoing last run empty representative (listed representative)
    latest root onward no_return
  omega

omit [DecidableEq V] in
/-- 同一SCC内の歩道を逆にたどるときは、割当済みSCCを通る必要がない。 -/
theorem lift_reverse_walk (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (previous : V → Option Nat) (whole : Saturated outgoing previous) (root : V)
    (root_fresh : previous root = none) {source target : V} (path : Walk (Edge outgoing) source target) :
    Reach outgoing root source → Reach outgoing target root →
    Nonempty (Walk (ReverseDfsStack.FreshEdge previous parents) target source) := by
  induction path with
  | nil => intro _ _; exact ⟨.nil _⟩
  | @cons source next target edge tail ih =>
    intro from_root to_root
    have root_to_next := reach_trans from_root ⟨.cons edge (.nil next)⟩
    have next_to_root := reach_trans ⟨tail⟩ to_root
    have source_to_root := reach_trans ⟨.cons edge tail⟩ to_root
    have source_fresh := (whole root source ⟨from_root, source_to_root⟩).mp root_fresh
    have next_fresh := (whole root next ⟨root_to_next, next_to_root⟩).mp root_fresh
    obtain ⟨lifted⟩ := ih root_to_next to_root
    exact ⟨lifted.append (.cons ⟨(correct next source).mpr edge, next_fresh, source_fresh⟩ (.nil source))⟩

theorem fresh_reverse_iff_mutual (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last) (empty : last.stack = [])
    (listed : ∀ vertex, vertex ∈ last.finished) (previous : V → Option Nat) (whole : Saturated outgoing previous)
    (root : V) (root_fresh : previous root = none) (highest : Highest last.finished previous root) (vertex : V) :
    ReverseDfsStack.FreshReach previous parents root vertex ↔ Mutual outgoing root vertex := by
  constructor
  · intro reached
    have back := fresh_reverse_to_original outgoing parents correct previous root vertex reached
    obtain ⟨path⟩ : Nonempty (Walk (ReverseDfsStack.FreshEdge previous parents) root vertex) := reached
    exact fresh_predecessor_mutual outgoing last run empty listed previous whole root highest vertex
      (fresh_walk_endpoint previous parents path root_fresh)
      back
  · intro same
    obtain ⟨back⟩ : Nonempty (Walk (Edge outgoing) vertex root) := same.2
    exact lift_reverse_walk outgoing parents correct previous whole root root_fresh back same.1 ⟨.nil root⟩

/-- 実際の第二DFSの新規番号と、根と同じSCCであることが一致する。 -/
theorem descend_one_component (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last) (empty : last.stack = [])
    (listed : ∀ vertex, vertex ∈ last.finished) (state : ComponentNumbering.State V)
    (valid : ComponentNumbering.Invariant state) (whole : Saturated outgoing state.result)
    (root : V) (fresh : state.result root = none) (highest : Highest last.finished state.result root) (vertex : V) :
    (ComponentNumbering.descend vertices.length parents state root).result vertex = some state.roots.length ↔
      Mutual outgoing root vertex :=
  (ComponentNumbering.descend_reach_exact vertices unique covered parents state valid root vertex fresh).trans
    (fresh_reverse_iff_mutual outgoing parents correct last run empty listed state.result whole root fresh highest vertex)

theorem remaining_component (outgoing : V → List (Option V)) (previous : V → Option Nat)
    (id : Nat) (root : V) (next : ReverseDfsStack.State V)
    (history : ReverseDfsStack.Run id (ReverseDfsStack.initial previous) next)
    (current : ∀ vertex, next.result vertex = some id ↔ Mutual outgoing root vertex) (vertex : V) :
    next.result vertex = none ↔ previous vertex = none ∧ ¬Mutual outgoing root vertex := by
  constructor
  · intro fresh
    refine ⟨history.none_was_fresh vertex fresh, ?_⟩
    intro same
    have assigned := (current vertex).mpr same
    rw [fresh] at assigned
    cases assigned
  · rintro ⟨fresh, outside⟩
    rcases history.label_cases vertex with old | assigned
    · exact old.trans fresh
    · exact False.elim (outside ((current vertex).mp assigned))

omit [DecidableEq V] in
/-- 同じSCCを丸ごと除去すれば、次回の未割当集合もSCC単位である。 -/
theorem remove_component_preserves_saturated (outgoing : V → List (Option V))
    (previous next : V → Option Nat) (root : V) (whole : Saturated outgoing previous)
    (remaining : ∀ vertex, next vertex = none ↔ previous vertex = none ∧ ¬Mutual outgoing root vertex) :
    Saturated outgoing next := by
  intro a b connected
  have same_root : Mutual outgoing root a ↔ Mutual outgoing root b := by
    constructor
    · intro same
      exact ⟨reach_trans same.1 connected.1, reach_trans connected.2 same.2⟩
    · intro same
      exact ⟨reach_trans same.1 connected.2, reach_trans connected.1 same.2⟩
  rw [remaining a, remaining b]
  constructor
  · rintro ⟨fresh, outside⟩
    exact ⟨(whole a b connected).mp fresh, fun same => outside (same_root.mpr same)⟩
  · rintro ⟨fresh, outside⟩
    exact ⟨(whole a b connected).mpr fresh, fun same => outside (same_root.mp same)⟩

theorem step_preserves_saturated (vertices : List V) (unique : vertices.Nodup) (covered : ∀ vertex, vertex ∈ vertices)
    (outgoing : V → List (Option V)) (parents : V → List V)
    (correct : ∀ source target, target ∈ parents source ↔ Edge outgoing target source)
    (last : ForwardDfs.State V) (run : Timeline outgoing ForwardDfs.initial last) (empty : last.stack = [])
    (listed : ∀ vertex, vertex ∈ last.finished) (state : ComponentNumbering.State V)
    (valid : ComponentNumbering.Invariant state) (whole : Saturated outgoing state.result)
    (root : V) (highest : state.result root = none → Highest last.finished state.result root) :
    Saturated outgoing (ComponentNumbering.step vertices.length parents state root).result := by
  by_cases fresh : state.result root = none
  · have exact_component := descend_one_component vertices unique covered outgoing parents correct
      last run empty listed state valid whole root fresh (highest fresh)
    have history := ComponentNumbering.descend_run vertices.length parents state root
    have remaining := remaining_component outgoing state.result state.roots.length root _ history exact_component
    have after := remove_component_preserves_saturated outgoing state.result _ root whole remaining
    simpa only [ComponentNumbering.step, if_pos fresh] using after
  · simpa only [ComponentNumbering.step, if_neg fresh] using whole

end PetaProof.KosarajuStep
