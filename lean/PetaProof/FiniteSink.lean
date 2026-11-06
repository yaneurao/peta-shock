import PetaProof.Pruning
import PetaProof.Localization

/-!
有限グラフの空でない領域には、外へ出る辺を持たない強連結部分がある。
Kosarajuの結果を仮定せず、到達集合の大きさが最小の頂点を使って存在を示す。
これは存在証明であり、実用上のSCC計算を到達集合の全列挙へ変更する提案ではない。
-/

namespace PetaProof

universe u
variable {V : Type u}

def Reachable (R : V → V → Prop) (a b : V) : Prop := Nonempty (Walk R a b)

namespace Reachable

variable {R : V → V → Prop} {a b c : V}

theorem refl (v : V) : Reachable R v v := ⟨.nil v⟩

theorem trans (first : Reachable R a b) (second : Reachable R b c) : Reachable R a c := by
  obtain ⟨left⟩ := first
  obtain ⟨right⟩ := second
  exact ⟨left.append right⟩

theorem edge (e : R a b) : Reachable R a b := ⟨.cons e (.nil b)⟩

theorem closed {domain : V → Prop} (inside : ∀ x y, R x y → domain x → domain y)
    (path : Reachable R a b) (start : domain a) : domain b := by
  obtain ⟨walk⟩ := path
  induction walk with
  | nil => exact start
  | cons e _ ih => exact ih (inside _ _ e start)

end Reachable

/-- 空でない有限リストから自然数の費用が最小の要素を取れる。 -/
theorem minimum_in_list (vertices : List V) (cost : V → Nat) (nonempty : vertices ≠ []) :
    ∃ v ∈ vertices, ∀ w ∈ vertices, cost v ≤ cost w := by
  classical
  induction vertices with
  | nil => contradiction
  | cons v rest ih =>
    by_cases empty : rest = []
    · subst rest
      exact ⟨v, by simp, by intro w hw; simp only [List.mem_singleton] at hw; subst w; exact Nat.le_refl _⟩
    · obtain ⟨best, member, minimal⟩ := ih empty
      by_cases lower : cost v ≤ cost best
      · refine ⟨v, by simp, ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with same | tail
        · subst w; exact Nat.le_refl _
        · exact Nat.le_trans lower (minimal w tail)
      · refine ⟨best, by simp [member], ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with same | tail
        · subst w; omega
        · exact minimal w tail

/-- 有限領域上で費用を最小にする頂点の存在。 -/
theorem minimum_on_domain (vertices : List V) (domain : V → Prop) (cost : V → Nat)
    (covered : ∀ v, domain v → v ∈ vertices) (nonempty : ∃ v, domain v) :
    ∃ v, domain v ∧ ∀ w, domain w → cost v ≤ cost w := by
  classical
  let candidates := vertices.filter (fun v => decide (domain v))
  have exists_member : ∃ v, v ∈ candidates := by
    obtain ⟨v, hv⟩ := nonempty
    exact ⟨v, by simp only [candidates, List.mem_filter, decide_eq_true_eq]; exact ⟨covered v hv, hv⟩⟩
  have not_empty : candidates ≠ [] := by
    intro empty
    obtain ⟨v, hv⟩ := exists_member
    rw [empty] at hv
    contradiction
  obtain ⟨v, hv, minimal⟩ := minimum_in_list candidates cost not_empty
  have original : v ∈ vertices ∧ domain v := by
    simpa only [candidates, List.mem_filter, decide_eq_true_eq] using hv
  refine ⟨v, original.2, ?_⟩
  intro w hw
  exact minimal w (by
    simp only [candidates, List.mem_filter, decide_eq_true_eq]
    exact ⟨covered w hw, hw⟩)

/-- 有限列挙内に差分の要素があれば、部分集合の要素数は厳密に小さい。 -/
theorem population_strict_subset (vertices : List V) (small large : V → Prop)
    (sub : ∀ v, small v → large v) (v : V) (member : v ∈ vertices)
    (in_large : large v) (not_small : ¬ small v) :
    ThresholdGame.population vertices small < ThresholdGame.population vertices large := by
  classical
  let kept := vertices.filter (fun w => decide (large w))
  let selected := fun w => decide (small w)
  have witness : v ∈ kept := by
    simp only [kept, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, in_large⟩
  have smaller := List.length_filter_le selected kept
  have different : (kept.filter selected).length ≠ kept.length := by
    intro same
    have all := (List.length_filter_eq_length_iff).1 same
    exact not_small (by simpa only [selected, decide_eq_true_eq] using all v witness)
  have filters : vertices.filter (fun w => decide (small w)) = kept.filter selected := by
    simp only [kept, selected, List.filter_filter]
    congr 1
    funext w
    by_cases hs : small w
    · simp [hs, sub w hs]
    · simp [hs]
  unfold ThresholdGame.population
  rw [filters]
  change (kept.filter selected).length < kept.length
  omega

/-- 強連結で、領域内の内部辺に関して外へ出ることがない部分集合。 -/
structure SinkComponent (R : V → V → Prop) (domain : V → Prop) where
  member : V → Prop
  nonempty : ∃ v, member v
  within : ∀ v, member v → domain v
  closed : ∀ v w, member v → R v w → member w
  connected : ∀ v w, member v → member w → Reachable R v w

/-- 有限グラフの最下流成分の存在。SCCアルゴリズムの正しさを前提にしない。 -/
theorem finite_sink_exists (R : V → V → Prop) (domain : V → Prop) (vertices : List V)
    (covered : ∀ v, domain v → v ∈ vertices)
    (closed : ∀ v w, R v w → domain v → domain w)
    (nonempty : ∃ v, domain v) : Nonempty (SinkComponent R domain) := by
  classical
  obtain ⟨root, hroot, minimum⟩ := minimum_on_domain vertices domain
    (fun v => ThresholdGame.population vertices (Reachable R v)) covered nonempty
  have returns (v : V) (path : Reachable R root v) : Reachable R v root := by
    apply Classical.byContradiction
    intro no_return
    have smaller := population_strict_subset vertices (Reachable R v) (Reachable R root)
      (fun w onward => path.trans onward) root (covered root hroot)
      (Reachable.refl root) no_return
    have lower := minimum v (path.closed closed hroot)
    omega
  exact ⟨{
    member := Reachable R root
    nonempty := ⟨root, Reachable.refl root⟩
    within := fun v path => path.closed closed hroot
    closed := fun v w path e => path.trans (Reachable.edge e)
    connected := fun v w hv hw => (returns v hv).trans hw
  }⟩

/-- 行き止まりがなければ、最下流成分の全頂点は循環に含まれる。 -/
theorem SinkComponent.cyclic {R : V → V → Prop} {domain : V → Prop}
    (sink : SinkComponent R domain) (successor : ∀ v, domain v → ∃ w, R v w)
    (v : V) (hv : sink.member v) : CyclicVertex R v := by
  obtain ⟨w, edge⟩ := successor v (sink.within v hv)
  exact ⟨w, edge, sink.connected w v (sink.closed v w hv edge) hv⟩

end PetaProof
