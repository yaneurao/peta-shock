import PetaProof.ForwardDfsFinishRank
import PetaProof.FiniteSink

namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

def Mutual (outgoing : V → List (Option V)) (left right : V) : Prop :=
  Reach outgoing left right ∧ Reach outgoing right left

def Latest (outgoing : V → List (Option V)) (last : State V) (vertex : V) : Prop :=
  ∀ other, Mutual outgoing vertex other → last.finished.idxOf other ≤ last.finished.idxOf vertex

omit [DecidableEq V] in
theorem reach_trans {outgoing : V → List (Option V)} {a b c : V}
    (first : Reach outgoing a b) (second : Reach outgoing b c) : Reach outgoing a c := by
  obtain ⟨left⟩ : Nonempty (Walk (Edge outgoing) a b) := first
  obtain ⟨right⟩ : Nonempty (Walk (Edge outgoing) b c) := second
  exact ⟨left.append right⟩

/-- 最大終了順位の代表は有限列から存在する。SCCを全列挙する実装を追加しない。 -/
theorem latest_exists (outgoing : V → List (Option V)) (last : State V)
    (covered : ∀ vertex, vertex ∈ last.finished) (start : V) :
    ∃ vertex, Mutual outgoing start vertex ∧ Latest outgoing last vertex := by
  let cost := fun vertex => last.finished.length - last.finished.idxOf vertex
  obtain ⟨vertex, same, minimal⟩ := minimum_on_domain last.finished (Mutual outgoing start) cost
    (fun v _ => covered v) ⟨start, ⟨⟨.nil start⟩, ⟨.nil start⟩⟩⟩
  refine ⟨vertex, same, ?_⟩
  intro other connected
  have in_domain : Mutual outgoing start other :=
    ⟨reach_trans same.1 connected.1, reach_trans connected.2 same.2⟩
  have smallest := minimal other in_domain
  have first_bound := List.idxOf_lt_length (covered vertex)
  have second_bound := List.idxOf_lt_length (covered other)
  dsimp only [cost] at smallest
  omega

/-- SCC内で最後に終了する頂点を今終了すると、その到達先は全て終了済みになる。 -/
theorem latest_retirement_closed (outgoing : V → List (Option V)) (state last : State V)
    (scans : ScanInvariant outgoing state) (path : ActivePath outgoing state)
    (last_valid : Invariant last) (empty : last.stack = [])
    (frame : Frame V) (rest : List (Frame V)) (stack : state.stack = frame :: rest)
    (done : frame.todo = []) (tail : Timeline outgoing (tick outgoing state) last)
    (latest : Latest outgoing last frame.vertex) (vertex : V) (reachable : Reach outgoing frame.vertex vertex) :
    vertex ∈ (tick outgoing state).finished := by
  have after_scans := tick_scanned outgoing state scans
  have expanded : (frame.vertex :: rest.map Frame.vertex).Pairwise
      (fun descendant ancestor => Reach outgoing ancestor descendant) := by
    simpa [ActivePath, State.active, stack] using path
  have cannot_active : ∀ target, Reach outgoing frame.vertex target →
      target ∈ (tick outgoing state).active → False := by
    intro target from_root active
    have below : target ∈ rest.map Frame.vertex := by
      simpa [tick, stack, done, retire, State.active] using active
    have back := (List.pairwise_cons.mp expanded).1 target below
    have smaller := latest target ⟨from_root, back⟩
    have larger := retirement_ancestor_later outgoing state last scans.base last_valid empty
      frame rest stack done tail target below
    omega
  have follow : ∀ {source target : V}, Walk (Edge outgoing) source target →
      Reach outgoing frame.vertex source → source ∈ (tick outgoing state).finished →
      target ∈ (tick outgoing state).finished := by
    intro source target route
    induction route with
    | nil => intro _ member; exact member
    | @cons source next target edge _ ih =>
      intro to_source member
      have to_next : Reach outgoing frame.vertex next := reach_trans to_source ⟨.cons edge (.nil next)⟩
      have seen := after_scans.closed source member next edge
      have position := (after_scans.base.covers next).mp seen
      rcases List.mem_append.mp position with finished | active
      · exact ih to_next finished
      · exact False.elim (cannot_active next to_next active)
  obtain ⟨route⟩ : Nonempty (Walk (Edge outgoing) frame.vertex vertex) := reachable
  apply follow route ⟨.nil frame.vertex⟩
  simp [tick, stack, done, retire]

/-- 異なる到達先SCCは、始点SCCの最大終了順位より厳密に先に終了している。 -/
theorem latest_reaches_earlier (outgoing : V → List (Option V)) (last : State V)
    (run : Timeline outgoing initial last) (empty : last.stack = [])
    (source : V) (member : source ∈ last.finished) (latest : Latest outgoing last source)
    (target : V) (reachable : Reach outgoing source target) (no_return : ¬Reach outgoing target source) :
    last.finished.idxOf target < last.finished.idxOf source := by
  obtain ⟨state, before, retiring, tail⟩ := run.retirement_witness source member (by simp [initial])
  obtain ⟨frame, rest, stack, same, done⟩ := retiring
  subst source
  have scans := before.scanned (initial_scanned outgoing)
  have path := before.path (initial_scanned outgoing) (initial_active_path outgoing)
  have last_valid := (run.scanned (initial_scanned outgoing)).base
  have finished := latest_retirement_closed outgoing state last scans path last_valid empty
    frame rest stack done tail latest target reachable
  have different : target ≠ frame.vertex := by
    intro same
    subst target
    exact no_return ⟨.nil _⟩
  have old : target ∈ state.finished := by
    have candidates : target ∈ state.finished ∨ target = frame.vertex := by
      simpa [tick, stack, done, retire] using finished
    exact candidates.resolve_right different
  have earlier := (Timeline.next (Event.advance state) tail).finished_index target old
  have rank := retirement_rank outgoing state last scans.base frame rest stack done tail
  omega

theorem finish_latest_exists (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V)) (start : V) :
    ∃ vertex, Mutual outgoing start vertex ∧ Latest outgoing (finish vertices roots outgoing) vertex :=
  latest_exists outgoing _ (finish_covers vertices unique covered roots roots_cover outgoing) start

/-- 実際に構成した第一DFSの終了順に対する、異なるSCC間の最大終了順位の関係。 -/
theorem finish_scc_order (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V))
    (source target : V) (latest : Latest outgoing (finish vertices roots outgoing) source)
    (reachable : Reach outgoing source target) (no_return : ¬Reach outgoing target source) :
    (finish vertices roots outgoing).finished.idxOf target <
      (finish vertices roots outgoing).finished.idxOf source :=
  latest_reaches_earlier outgoing _ (finish_timeline vertices unique covered outgoing roots)
    (forest_drains vertices unique covered outgoing roots initial rfl) source
    (finish_covers vertices unique covered roots roots_cover outgoing source) latest target reachable no_return

/-- C→Dの辺を、各成分の代表間の終了順位へ直接持ち上げる。 -/
theorem finish_scc_edge_order (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) (roots : List V)
    (roots_cover : ∀ vertex, vertex ∈ roots) (outgoing : V → List (Option V))
    (source target representative nextRepresentative : V) (edge : Edge outgoing source target)
    (same_source : Mutual outgoing source representative) (same_target : Mutual outgoing target nextRepresentative)
    (latest : Latest outgoing (finish vertices roots outgoing) representative)
    (different : ¬Reach outgoing target source) :
    (finish vertices roots outgoing).finished.idxOf nextRepresentative <
      (finish vertices roots outgoing).finished.idxOf representative := by
  apply finish_scc_order vertices unique covered roots roots_cover outgoing representative nextRepresentative latest
  · exact reach_trans same_source.2 (reach_trans ⟨.cons edge (.nil target)⟩ same_target.1)
  · intro back
    exact different (reach_trans same_target.1 (reach_trans back same_source.2))

end PetaProof.ForwardDfs
