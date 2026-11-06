import PetaProof.FinitePayoff

/-!
吸収アリーナの負け領域の方策を、元の合法手と有限終局用の反証順位へ戻す。
成功leafへの逃げ道を残さず、相手の王手が続く区間では順位が厳密減少する。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 相手方策の選択先を、その行き先を実現する元の合法手へ復元する。 -/
noncomputable def decodeResponse (response : AbsorbedState V → AbsorbedState V)
    (legal : ∀ v, G.owner v ≠ G.player → G.absorbedArena.edge (.node v) (response (.node v)))
    (v : V) : Move V := by
  classical
  exact if other : G.owner v ≠ G.player then
    Classical.choose ((G.absorbed_edge_iff v (response (.node v))).mp (legal v other))
  else Classical.choose (G.nonempty_moves v)

theorem decodeResponse_spec (response : AbsorbedState V → AbsorbedState V)
    (legal : ∀ v, G.owner v ≠ G.player → G.absorbedArena.edge (.node v) (response (.node v)))
    (v : V) (other : G.owner v ≠ G.player) :
    G.legal v (G.decodeResponse response legal v) ∧
      G.encodeMove (G.decodeResponse response legal v) = response (.node v) := by
  classical
  simp only [decodeResponse, dif_pos other]
  exact Classical.choose_spec ((G.absorbed_edge_iff v (response (.node v))).mp (legal v other))

/-- 成功状態を含む確定領域の補集合にある反証証拠から、元のゲームの反証領域を作る。 -/
noncomputable def extractRefutationRegion {won : AbsorbedState V → Prop}
    (ordinary : G.absorbedArena.OrdinaryClosed won) (success : won .success)
    (counter : (G.absorbedArena.complementTrap ordinary).restricted.Counterstrategy) :
    G.RefutationRegion (fun v => ¬ won (.node v)) := by
  classical
  let trap := G.absorbedArena.complementTrap ordinary
  let response := trap.liftResponse counter
  have legal (v : V) (other : G.owner v ≠ G.player) :
      G.absorbedArena.edge (.node v) (response (.node v)) :=
    trap.liftResponse_legal counter (.node v) other
  let original := G.decodeResponse response legal
  have follows (v : V) (m : Move V) (reply : G.Replies original v m) :
      G.absorbedArena.FollowsResponse response (.node v) (G.encodeMove m) := by
    refine ⟨(G.absorbed_edge_iff v _).mpr ⟨m, reply.1, rfl⟩, ?_⟩
    intro other
    rw [← reply.2 other]
    exact (G.decodeResponse_spec response legal v other).2
  have stays (v : V) (inside : ¬ won (.node v)) (m : Move V) (reply : G.Replies original v m) :
      ¬ won (G.encodeMove m) :=
    trap.liftResponse_stays counter (.node v) (G.encodeMove m) inside (follows v m reply)
  let rank := fun v => if inside : ¬ won (.node v) then
    counter.ranking.rank ⟨.node v, inside⟩ else 0
  exact {
    response := original
    chosen_legal := fun v _ other => (G.decodeResponse_spec response legal v other).1
    closed := by
      intro v inside m reply
      have child := stays v inside m reply
      cases m with
      | node w => exact child
      | leaf score =>
        have below : ¬ G.threshold ≤ score := by
          intro good
          simp only [encodeMove, if_pos good] at child
          exact child success
        omega
    rank := rank
    strict_checking := by
      intro v w inside reply checking
      have child : ¬ won (.node w) := stays v inside (.node w) reply
      have subfollows := trap.liftResponse_follows counter
        ⟨.node v, inside⟩ ⟨.node w, child⟩ (follows v (.node w) reply)
      have good : ¬ G.absorbedArena.bad (.node v) (.node w) := by
        intro bad
        exact bad.2 (checking bad.1)
      have decrease := counter.ranking.strict_good _ _ subfollows good
      simpa only [rank, dif_pos inside, dif_pos child] using decrease
  }

/-- 吸収モデルで勝てない局面には、元のleaf・反復の利得を閾値未満に抑える証拠がある。 -/
theorem refutation_of_not_absorbed_winning (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (not_winning : ¬ G.absorbedArena.HistoryWinning (.node root)) :
    ∃ lost, Nonempty (G.RefutationRegion lost) ∧ lost root := by
  let states := G.absorbedVertices vertices
  have covers := G.absorbedVertices_cover vertices covered
  obtain ⟨won, ⟨policy⟩, maximal⟩ := G.absorbedArena.maximal_policy_exists states covers
  have ordinary := G.absorbedArena.maximal_policy_ordinary policy maximal
  have exactness := G.absorbedArena.maximal_policy_exact_history policy maximal states covers
  have success := (exactness .success).mpr G.success_history_winning
  obtain ⟨counter⟩ := G.absorbedArena.residual_counter_exists policy maximal ordinary states covers
  exact ⟨(fun v => ¬ won (.node v)), ⟨G.extractRefutationRegion ordinary success counter⟩,
    fun inside => not_winning ((exactness (.node root)).mp inside)⟩

theorem refutation_of_not_positional (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (not_winning : ¬ G.PositionalWinning root) :
    ∃ lost, Nonempty (G.RefutationRegion lost) ∧ lost root :=
  G.refutation_of_not_absorbed_winning vertices covered root
    (fun winning => not_winning ((G.absorbed_history_iff_positional vertices covered root).mp winning))

/-- 停止した元の閾値解法の外側にも、有限終局用の反証方策を構成できる。 -/
theorem stopped_outside_refutation {won : V → Prop} (sound : G.RankedRegion won)
    (ordinary : G.OrdinaryClosed won) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (core : V → Prop) (covers_core : ∀ v, CyclicVertex G.OpponentChecking v → core v)
    (n : Nat) (empty : ∀ v, ¬ G.pruneIter won (fun w => core w ∧ ¬ won w) n v)
    (root : V) (outside : ¬ won root) :
    ∃ lost, Nonempty (G.RefutationRegion lost) ∧ lost root := by
  apply G.refutation_of_not_positional vertices covered root
  intro winning
  exact outside ((G.stopped_exact_for_positional sound ordinary vertices covered core covers_core n empty root).mpr winning)

/-- 有限グラフの各局面には、正の保証か有限終局の反証のどちらかを構成できる。 -/
theorem finite_certificate_dichotomy (vertices : List V) (covered : ∀ v, v ∈ vertices) (root : V) :
    (∃ won, Nonempty (G.RankedRegion won) ∧ won root) ∨
      (∃ lost, Nonempty (G.RefutationRegion lost) ∧ lost root) := by
  classical
  by_cases winning : G.absorbedArena.HistoryWinning (.node root)
  · obtain ⟨won, ⟨policy⟩, inside⟩ := (G.absorbedArena.history_winning_iff_ranked
      (G.absorbedVertices vertices) (G.absorbedVertices_cover vertices covered) (.node root)).mp winning
    exact Or.inl ⟨(fun v => won (.node v)), ⟨G.extractRankedRegion policy⟩, inside⟩
  · exact Or.inr (G.refutation_of_not_absorbed_winning vertices covered root winning)

/-- 同じrootに正反両方の証拠は存在しない。共有方策にleafがなければ有限性から閉路を取る。 -/
theorem finite_certificates_disjoint {won lost : V → Prop} (positive : G.RankedRegion won)
    (negative : G.RefutationRegion lost) (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) (wins : won root) (loses : lost root) : False := by
  let common := fun v => won v ∧ lost v
  let R := fun v w => common v ∧ G.Follows positive.choice v (.node w) ∧ G.Replies negative.response v (.node w)
  have successor (v : V) (inside : common v) : ∃ w, R v w := by
    have move : ∃ m, G.Follows positive.choice v m ∧ G.Replies negative.response v m := by
      by_cases own : G.owner v = G.player
      · exact ⟨positive.choice v, ⟨positive.chosen_legal v inside.1 own, fun _ => rfl⟩,
          ⟨positive.chosen_legal v inside.1 own, fun other => False.elim (other own)⟩⟩
      · exact ⟨negative.response v,
          ⟨negative.chosen_legal v inside.2 own, fun self => False.elim (own self)⟩,
          ⟨negative.chosen_legal v inside.2 own, fun _ => rfl⟩⟩
    obtain ⟨m, selected, replied⟩ := move
    cases m with
    | node w => exact ⟨w, inside, selected, replied⟩
    | leaf score =>
      have lower := positive.closed v inside.1 (.leaf score) selected
      have upper := negative.closed v inside.2 (.leaf score) replied
      exact False.elim (by omega)
  have closed : ∀ v w, R v w → common v → common w := by
    intro v w e _
    exact ⟨positive.closed v e.1.1 (.node w) e.2.1, negative.closed v e.1.2 (.node w) e.2.2⟩
  obtain ⟨sink⟩ := finite_sink_exists R common vertices (fun v _ => covered v) closed ⟨root, wins, loses⟩
  obtain ⟨a, member⟩ := sink.nonempty
  obtain ⟨b, edge, ⟨back⟩⟩ := sink.cyclic successor a member
  let loop := Walk.cons edge back
  have all : loop.Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
    apply Walk.every_returning _ _ loop (.nil a)
    intro v w e returning other
    exact positive.positional.cycle_checks v w e.1.1 e.2.1
      (returning.map (fun _ _ h => ⟨h.1.1, h.2.1⟩)) other
  let toNegative : ∀ v w, R v w → negative.Internal v w := fun _ _ h => ⟨h.1.2, h.2.2⟩
  exact negative.no_opponent_check_loop (toNegative a b edge) (back.map toNegative)
    ((loop.every_map toNegative _).mpr all)

/-- 元の有限終局用反証証拠があることと、吸収モデルで勝てないことが一致する。 -/
theorem refutation_iff_not_absorbed_winning (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (root : V) :
    (∃ lost, Nonempty (G.RefutationRegion lost) ∧ lost root) ↔
      ¬ G.absorbedArena.HistoryWinning (.node root) := by
  constructor
  · rintro ⟨lost, ⟨negative⟩, loses⟩ winning
    obtain ⟨won, ⟨policy⟩, wins⟩ := (G.absorbedArena.history_winning_iff_ranked
      (G.absorbedVertices vertices) (G.absorbedVertices_cover vertices covered) (.node root)).mp winning
    exact G.finite_certificates_disjoint (G.extractRankedRegion policy) negative vertices covered root wins loses
  · exact G.refutation_of_not_absorbed_winning vertices covered root

end PetaProof.ThresholdGame
