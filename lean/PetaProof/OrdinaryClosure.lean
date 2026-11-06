import PetaProof.PropagationTransitions
import PetaProof.Progress

/-!
通常伝播の終了集合を、有限回の集合拡大で定義する数学的仕様。
全頂点の同期走査を高速な待機列処理に代えて採用するものではない。
-/
namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

def OrdinaryReady (won : V → Prop) (v : V) : Prop :=
  (G.owner v = G.player ∧ ∃ m, G.legal v m ∧ G.GoodExit won m) ∨
  (G.owner v ≠ G.player ∧ ∀ m, G.legal v m → G.GoodExit won m)

def ordinaryGrow (won : V → Prop) (v : V) : Prop := won v ∨ G.OrdinaryReady won v

def ordinaryIter (won : V → Prop) : Nat → V → Prop
  | 0 => won
  | n + 1 => G.ordinaryGrow (ordinaryIter won n)

theorem ordinaryReady_mono {old next : V → Prop} (sub : ∀ v, old v → next v)
    {v : V} (ready : G.OrdinaryReady old v) : G.OrdinaryReady next v := by
  rcases ready with ⟨own, m, legal, good⟩ | ⟨other, all⟩
  · exact Or.inl ⟨own, m, legal, G.goodExit_mono sub m good⟩
  · exact Or.inr ⟨other, fun m legal => G.goodExit_mono sub m (all m legal)⟩

theorem ordinaryIter_subset (won : V → Prop) (n : Nat) : ∀ v, won v → G.ordinaryIter won n v := by
  induction n with
  | zero => exact fun _ h => h
  | succ n ih => exact fun v h => Or.inl (ih v h)

theorem ordinaryIter_add (won : V → Prop) (a b : Nat) :
    G.ordinaryIter won (a + b) = G.ordinaryIter (G.ordinaryIter won a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, ordinaryIter, ih, ordinaryIter]

theorem ordinaryGrow_of_closed {won : V → Prop} (closed : G.OrdinaryClosed won) : G.ordinaryGrow won = won := by
  funext v
  apply propext
  exact ⟨fun h => h.elim id (closed v), Or.inl⟩

theorem ordinaryIter_of_closed {won : V → Prop} (closed : G.OrdinaryClosed won) (n : Nat) :
    G.ordinaryIter won n = won := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ordinaryIter, ih, ordinaryGrow_of_closed G closed]

theorem ordinary_population_grows {won : V → Prop} (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (not_closed : ¬ G.OrdinaryClosed won) : population vertices won < population vertices (G.ordinaryGrow won) := by
  classical
  have missing : ∃ v, G.OrdinaryReady won v ∧ ¬ won v := by
    apply Classical.byContradiction
    intro none
    apply not_closed
    intro v ready
    apply Classical.byContradiction
    intro outside
    exact none ⟨v, ready, outside⟩
  obtain ⟨v, ready, outside⟩ := missing
  exact population_strict_subset vertices won (G.ordinaryGrow won) (fun _ => Or.inl) v (covered v) (Or.inr ready) outside

theorem ordinary_stable_exists (vertices : List V) (covered : ∀ v, v ∈ vertices) (won : V → Prop) :
    ∃ n, n ≤ vertices.length ∧ G.OrdinaryClosed (G.ordinaryIter won n) := by
  classical
  apply Classical.byContradiction
  intro none
  have growth : ∀ n, n ≤ vertices.length + 1 →
      population vertices won + n ≤ population vertices (G.ordinaryIter won n) := by
    intro n
    induction n with
    | zero => exact fun _ => Nat.le_refl _
    | succ n ih =>
      intro bound
      have earlier := ih (by omega)
      have not_closed : ¬ G.OrdinaryClosed (G.ordinaryIter won n) := fun closed => none ⟨n, by omega, closed⟩
      have more := G.ordinary_population_grows vertices covered not_closed
      change population vertices (G.ordinaryIter won n) < population vertices (G.ordinaryIter won (n + 1)) at more
      omega
  have impossible := growth (vertices.length + 1) (Nat.le_refl _)
  have upper := population_bound vertices (G.ordinaryIter won (vertices.length + 1))
  omega

def ordinaryClosure (vertices : List V) (won : V → Prop) : V → Prop := G.ordinaryIter won vertices.length

theorem ordinaryClosure_closed (vertices : List V) (covered : ∀ v, v ∈ vertices) (won : V → Prop) :
    G.OrdinaryClosed (G.ordinaryClosure vertices won) := by
  obtain ⟨n, bound, closed⟩ := G.ordinary_stable_exists vertices covered won
  have split : vertices.length = n + (vertices.length - n) := by omega
  unfold ordinaryClosure
  rw [split, ordinaryIter_add, ordinaryIter_of_closed G closed]
  exact closed

theorem ordinaryClosure_subset (vertices : List V) (won : V → Prop) :
    ∀ v, won v → G.ordinaryClosure vertices won v := G.ordinaryIter_subset won vertices.length

/-- 通常閉性を持つ任意の上位集合へ含まれるので、終了集合は走査順に依存しない。 -/
theorem ordinaryClosure_least (vertices : List V) {won closed : V → Prop}
    (sub : ∀ v, won v → closed v) (stable : G.OrdinaryClosed closed) :
    ∀ v, G.ordinaryClosure vertices won v → closed v := by
  have all : ∀ n v, G.ordinaryIter won n v → closed v := by
    intro n
    induction n with
    | zero => exact sub
    | succ n ih =>
      intro v inside
      rcases inside with old | ready
      · exact ih v old
      · exact stable v (G.ordinaryReady_mono ih ready)
  exact all vertices.length

/-- 通常追加だけの実行列。待機列の走査順や、一回に追加する頂点数は固定しない。 -/
inductive OrdinaryRun : (V → Prop) → (V → Prop) → Prop
  | refl (won) : OrdinaryRun won won
  | add {initial before after} : OrdinaryRun initial before →
      (∀ v, before v → after v) → (∀ v, after v → ¬ before v → G.OrdinaryReady before v) →
      OrdinaryRun initial after

theorem OrdinaryRun.extends {initial final : V → Prop} (run : G.OrdinaryRun initial final) :
    ∀ v, initial v → final v := by
  induction run with
  | refl => exact fun _ h => h
  | add _ sub _ ih => exact fun v h => sub v (ih v h)

theorem OrdinaryRun.contained {initial final : V → Prop} (run : G.OrdinaryRun initial final)
    {upper : V → Prop} (sub : ∀ v, initial v → upper v) (closed : G.OrdinaryClosed upper) :
    ∀ v, final v → upper v := by
  classical
  induction run with
  | refl => exact sub
  | @add before after _ _ ready ih =>
    intro v inside
    by_cases old : before v
    · exact ih v old
    · exact closed v (G.ordinaryReady_mono ih (ready v inside old))

/-- 正当な通常追加を終えて閉じた結果は集合仕様と一致する。余分な同期走査は要求しない。 -/
theorem OrdinaryRun.closed_result_eq (vertices : List V) (covered : ∀ v, v ∈ vertices)
    {initial final : V → Prop} (run : G.OrdinaryRun initial final) (closed : G.OrdinaryClosed final) :
    final = G.ordinaryClosure vertices initial := by
  funext v
  apply propext
  constructor
  · exact run.contained G (G.ordinaryClosure_subset vertices initial) (G.ordinaryClosure_closed vertices covered initial) v
  · exact G.ordinaryClosure_least vertices (run.extends G) closed v

theorem ordinaryGrow_sound {won : V → Prop} (old : G.RankedRegion won) : Nonempty (G.RankedRegion (G.ordinaryGrow won)) := by
  classical
  let new := fun v => ¬ won v ∧ G.OrdinaryReady won v
  have safe : G.SafeSet won new := by
    intro v hv
    have move_safe : ∀ m, G.GoodExit won m → G.SafeMove won new v m := by
      intro m good
      cases m with
      | node w => exact Or.inl good
      | leaf score => exact good
    constructor
    · intro own
      rcases hv.2 with ⟨_, m, legal, good⟩ | ⟨other, _⟩
      · exact ⟨m, legal, move_safe m good⟩
      · exact False.elim (other own)
    · intro other m legal
      rcases hv.2 with ⟨own, _⟩ | ⟨_, all⟩
      · exact False.elim (other own)
      · exact move_safe m (all m legal)
  let extended := old.extend (G.batchOfSafeSet safe (fun _ hv => hv.1))
  refine ⟨extended.reindex ?_⟩
  intro v
  change (won v ∨ (¬ won v ∧ G.OrdinaryReady won v)) ↔ (won v ∨ G.OrdinaryReady won v)
  by_cases inside : won v <;> simp [inside]

theorem ordinaryClosure_sound (vertices : List V) {won : V → Prop} (old : G.RankedRegion won) :
    Nonempty (G.RankedRegion (G.ordinaryClosure vertices won)) := by
  have all : ∀ n, Nonempty (G.RankedRegion (G.ordinaryIter won n)) := by
    intro n
    induction n with
    | zero => exact ⟨old⟩
    | succ n ih => obtain ⟨before⟩ := ih; exact G.ordinaryGrow_sound before
  exact all vertices.length

end PetaProof.ThresholdGame
