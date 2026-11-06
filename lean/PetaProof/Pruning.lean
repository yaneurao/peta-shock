import PetaProof.Propagation

/-!
局所安全集合の削除の不変条件と、有限候補集合での安定化。
同期的な削除と、キューによる逐次削除の両方に使える集合としての仕様。
C++のcount/incomingの更新を直接モデル化しているわけではない。
-/

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 自分の手番は少なくとも1つの安全手、相手の手番は全合法手の安全性を要求する。 -/
def CanStay (won current : V → Prop) (v : V) : Prop :=
  (G.owner v = G.player → ∃ m, G.legal v m ∧ G.SafeMove won current v m) ∧
  (G.owner v ≠ G.player → ∀ m, G.legal v m → G.SafeMove won current v m)

def SafeSet (won current : V → Prop) : Prop := ∀ v, current v → G.CanStay won current v

theorem safeSet_of_batch {won current : V → Prop} (batch : G.SafeBatch won current) :
    G.SafeSet won current := by
  intro v hv
  constructor
  · intro own
    exact ⟨batch.choice v, batch.chosen_legal v hv own,
      batch.safe v hv _ ⟨batch.chosen_legal v hv own, fun _ => rfl⟩⟩
  · intro other m legal
    exact batch.safe v hv m ⟨legal, fun impossible => False.elim (other impossible)⟩

def prune (won current : V → Prop) (v : V) : Prop := current v ∧ G.CanStay won current v

def pruneIter (won initial : V → Prop) : Nat → V → Prop
  | 0 => initial
  | n + 1 => G.prune won (pruneIter won initial n)

theorem safeMove_mono {won small large : V → Prop} (sub : ∀ v, small v → large v)
    {v : V} {m : Move V} (safe : G.SafeMove won small v m) : G.SafeMove won large v m := by
  cases m with
  | leaf _ => exact safe
  | node w => exact safe.elim Or.inl (fun h => Or.inr ⟨sub w h.1, h.2⟩)

theorem canStay_mono {won small large : V → Prop} (sub : ∀ v, small v → large v)
    {v : V} (safe : G.CanStay won small v) : G.CanStay won large v := by
  constructor
  · intro own
    obtain ⟨m, legal, good⟩ := safe.1 own
    exact ⟨m, legal, G.safeMove_mono sub good⟩
  · intro other m legal
    exact G.safeMove_mono sub (safe.2 other m legal)

/-- 候補を削る際、安全な部分集合の要素を消してしまうことはない。 -/
theorem prune_preserves {won safe current : V → Prop} (safe_set : G.SafeSet won safe)
    (sub : ∀ v, safe v → current v) {v : V} (hv : safe v) : G.prune won current v :=
  ⟨sub v hv, G.canStay_mono sub (safe_set v hv)⟩

theorem safe_survives {won safe initial : V → Prop} (safe_set : G.SafeSet won safe)
    (sub : ∀ v, safe v → initial v) (n : Nat) :
    ∀ v, safe v → G.pruneIter won initial n v := by
  induction n with
  | zero => exact sub
  | succ n ih => exact fun _ hv => G.prune_preserves safe_set ih hv

theorem iterate_subset {won initial : V → Prop} (n : Nat) :
    ∀ v, G.pruneIter won initial n v → initial v := by
  induction n with
  | zero => exact fun _ h => h
  | succ n ih => exact fun v h => ih v h.1

/-- 安定時に残った集合は安全であり、初期候補内のどの安全集合よりも大きい。 -/
theorem greatest_at_stable {won initial : V → Prop} (n : Nat)
    (stable : G.SafeSet won (G.pruneIter won initial n)) :
    G.SafeSet won (G.pruneIter won initial n) ∧
      ∀ safe, G.SafeSet won safe → (∀ v, safe v → initial v) →
        ∀ v, safe v → G.pruneIter won initial n v :=
  ⟨stable, fun _ safe sub => G.safe_survives safe sub n⟩

/-- キュー方式でも、現在の集合で条件を満たさない頂点だけを除外すればよい。
まだ条件を満たしている頂点を、将来消えるはずだという理由だけで除外してはいけない。 -/
theorem asynchronous_preserves {won safe before after : V → Prop}
    (safe_set : G.SafeSet won safe) (sub : ∀ v, safe v → before v)
    (removed_invalid : ∀ v, before v → ¬ after v → ¬ G.CanStay won before v) :
    ∀ v, safe v → after v := by
  intro v hv
  apply Classical.byContradiction
  intro removed
  exact removed_invalid v (sub v hv) removed (G.canStay_mono sub (safe_set v hv))

/-- 安全集合のOR側の存在証拠から選択手を取り出す。 -/
noncomputable def safeChoice {won current : V → Prop} (safe : G.SafeSet won current)
    (v : V) : Move V := by
  classical
  exact if own : current v ∧ G.owner v = G.player then
    Classical.choose ((safe v own.1).1 own.2) else .leaf 0

/-- 確定済み集合と重ならない安全集合は、順位付き領域に追加可能なバッチを構成する。 -/
noncomputable def batchOfSafeSet {won current : V → Prop} (safe : G.SafeSet won current)
    (fresh : ∀ v, current v → ¬ won v) : G.SafeBatch won current := by
  classical
  apply SafeBatch.ofOrAnd fresh (G.safeChoice safe)
  · intro v hv own
    simp only [safeChoice, dif_pos (And.intro hv own)]
    exact (Classical.choose_spec ((safe v hv).1 own)).1
  · intro v hv own
    simp only [safeChoice, dif_pos (And.intro hv own)]
    exact (Classical.choose_spec ((safe v hv).1 own)).2
  · intro v hv other m legal
    exact (safe v hv).2 other m legal

/-- 有限候補列挙に含まれる頂点を数える。列挙の重複があっても停止上界は保守的に使える。 -/
noncomputable def population (vertices : List V) (current : V → Prop) : Nat := by
  classical
  exact (vertices.filter (fun v => decide (current v))).length

theorem population_bound (vertices : List V) (current : V → Prop) :
    population vertices current ≤ vertices.length := by
  classical
  exact List.length_filter_le _ _

/-- 安全条件に違反した候補が残っているなら、1回の同期削除で候補数が厳密に減る。 -/
theorem population_prune_lt {won current : V → Prop} (vertices : List V)
    (covered : ∀ v, current v → v ∈ vertices) (unstable : ¬ G.SafeSet won current) :
    population vertices (G.prune won current) < population vertices current := by
  classical
  have bad : ∃ v, current v ∧ ¬ G.CanStay won current v := by
    apply Classical.byContradiction
    intro none
    apply unstable
    intro v hv
    apply Classical.byContradiction
    intro invalid
    exact none ⟨v, hv, invalid⟩
  obtain ⟨v, hv, fails⟩ := bad
  let kept := vertices.filter (fun w => decide (current w))
  let valid := fun w => decide (G.CanStay won current w)
  have member : v ∈ kept := by simp only [kept, List.mem_filter, decide_eq_true_eq]; exact ⟨covered v hv, hv⟩
  have le := List.length_filter_le valid kept
  have different : (kept.filter valid).length ≠ kept.length := by
    intro same
    have all := (List.length_filter_eq_length_iff).1 same
    have good := all v member
    exact fails (by simpa only [valid, decide_eq_true_eq] using good)
  have rewrite_filter : vertices.filter (fun w => decide (G.prune won current w)) = kept.filter valid := by
    simp only [kept, valid, List.filter_filter]
    congr 1
    funext w
    by_cases hc : current w <;> by_cases hs : G.CanStay won current w <;>
      simp [prune, hc, hs]
  unfold population
  rw [rewrite_filter]
  change (kept.filter valid).length < kept.length
  omega

/-- 不安定な削除をn回続けるなら、少なくともn個分の候補が減る。 -/
theorem deletion_bound {won initial : V → Prop} (vertices : List V)
    (covered : ∀ v, initial v → v ∈ vertices) (n : Nat)
    (unstable : ∀ i, i < n → ¬ G.SafeSet won (G.pruneIter won initial i)) :
    population vertices (G.pruneIter won initial n) + n ≤ population vertices initial := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have earlier := ih (fun i hi => unstable i (by omega))
    have decrease := G.population_prune_lt vertices
      (fun v hv => covered v (G.iterate_subset n v hv)) (unstable n (by omega))
    change population vertices (G.pruneIter won initial (n + 1)) <
      population vertices (G.pruneIter won initial n) at decrease
    omega

/-- N候補なら高々N回の同期削除で安全集合に達する。C++キューの計算量の主張ではない。 -/
theorem stable_exists {won initial : V → Prop} (vertices : List V)
    (covered : ∀ v, initial v → v ∈ vertices) :
    ∃ n, n ≤ vertices.length ∧ G.SafeSet won (G.pruneIter won initial n) := by
  classical
  apply Classical.byContradiction
  intro none
  have unstable : ∀ i, i < vertices.length + 1 → ¬ G.SafeSet won (G.pruneIter won initial i) := by
    intro i hi safe
    exact none ⟨i, by omega, safe⟩
  have limit := G.deletion_bound vertices covered (vertices.length + 1) unstable
  have bound := population_bound vertices initial
  omega

/-- 局所候補から有限回の削除で得た最大安全集合を、既存の保証領域へ安全に追加できる。 -/
theorem local_extension_exists {won initial : V → Prop} (old : G.RankedRegion won)
    (vertices : List V) (covered : ∀ v, initial v → v ∈ vertices)
    (fresh : ∀ v, initial v → ¬ won v) :
    ∃ n, n ≤ vertices.length ∧
      Nonempty (G.RankedRegion (fun v => won v ∨ G.pruneIter won initial n v)) ∧
      ∀ safe, G.SafeSet won safe → (∀ v, safe v → initial v) →
        ∀ v, safe v → G.pruneIter won initial n v := by
  obtain ⟨n, bound, stable⟩ := G.stable_exists vertices covered
  let batch := G.batchOfSafeSet stable
    (fun v hv => fresh v (G.iterate_subset n v hv))
  exact ⟨n, bound, ⟨old.extend batch⟩, fun _ safe sub => G.safe_survives safe sub n⟩

end PetaProof.ThresholdGame
