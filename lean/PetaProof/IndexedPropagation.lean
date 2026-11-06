import PetaProof.AdmissionQueue

/-!
有限の辺IDを持つ出辺列と、hit・キューの条件を通常伝播の閉性へ接続する。
入力列挙、逆辺通知、カウンターを実装からこの仕様へ写す対応は別の証明課題である。
-/
namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} (G : ThresholdGame V)

/-- 同じ指し手や子局面でも、異なる辺IDなら別々に数える列挙仕様。 -/
structure IndexedMoves (E : Type v) where
  outgoing : V → List E
  source : E → V
  move : E → Move V
  unique : ∀ v, (outgoing v).Nodup
  at_source : ∀ e, e ∈ outgoing (source e)
  source_of_mem : ∀ v e, e ∈ outgoing v → source e = v
  legal : ∀ v e, e ∈ outgoing v → G.legal v (move e)
  covers : ∀ v m, G.legal v m → ∃ e, e ∈ outgoing v ∧ move e = m

namespace IndexedMoves

variable {G}

theorem outgoing_nonempty (indexed : G.IndexedMoves E) (v : V) : 0 < (indexed.outgoing v).length := by
  obtain ⟨m, legal⟩ := G.nonempty_moves v
  obtain ⟨e, member, _⟩ := indexed.covers v m legal
  exact List.length_pos_of_mem member

theorem initial_counter_invariant (indexed : G.IndexedMoves E) (v : V) :
    HitCounter.Invariant (decide (G.owner v = G.player)) (indexed.outgoing v)
      (HitCounter.initial (indexed.outgoing v)) :=
  HitCounter.initial_invariant _ _ (indexed.outgoing_nonempty v)

/-- hitで新規確定するなら、OR/ANDの通常伝播条件を満たす。
通知済みの辺が良い出口であることと、新規通知が重複でないことを明示的に要求する。 -/
theorem hit_ready [DecidableEq E] (indexed : G.IndexedMoves E) (won : V → Prop)
    (v : V) (counter : HitCounter E) (edge : E)
    (invariant : HitCounter.Invariant (decide (G.owner v = G.player)) (indexed.outgoing v) counter)
    (member : edge ∈ indexed.outgoing v) (fresh : counter.seen edge = false)
    (pending : counter.admitted = false)
    (sound : ∀ e ∈ indexed.outgoing v, counter.seen e = true → G.GoodExit won (indexed.move e))
    (new_good : G.GoodExit won (indexed.move edge))
    (admitted : (HitCounter.hit (decide (G.owner v = G.player)) counter edge).admitted = true) :
    (G.owner v = G.player ∧ ∃ m, G.legal v m ∧ G.GoodExit won m) ∨
      (G.owner v ≠ G.player ∧ ∀ m, G.legal v m → G.GoodExit won m) := by
  classical
  by_cases own : G.owner v = G.player
  · exact Or.inl ⟨own, indexed.move edge, indexed.legal v edge member, new_good⟩
  · right
    refine ⟨own, ?_⟩
    have flag : decide (G.owner v = G.player) = false := by simp [own]
    have and_invariant : HitCounter.Invariant false (indexed.outgoing v) counter := by simpa only [flag] using invariant
    have and_admitted : (HitCounter.hit false counter edge).admitted = true := by simpa only [flag] using admitted
    have all_seen := (HitCounter.and_hit_iff_complete counter edge (indexed.outgoing v) and_invariant
      (indexed.unique v) member fresh pending).mp and_admitted
    intro m legal
    obtain ⟨e, present, same⟩ := indexed.covers v m legal
    have good : G.GoodExit won (indexed.move e) := by
      rcases (markSeen_true_iff counter.seen edge e).mp (all_seen e present) with equal | old
      · simpa only [equal] using new_good
      · exact sound e present old
    simpa only [same] using good

/-- 通知による新規確定を、既存の順位付き領域追加にそのまま渡せる安全な単一バッチへ戻す。 -/
def hit_batch [DecidableEq E] (indexed : G.IndexedMoves E) (won : V → Prop)
    (v : V) (counter : HitCounter E) (edge : E)
    (invariant : HitCounter.Invariant (decide (G.owner v = G.player)) (indexed.outgoing v) counter)
    (member : edge ∈ indexed.outgoing v) (fresh : counter.seen edge = false)
    (pending : counter.admitted = false) (outside : ¬ won v)
    (sound : ∀ e ∈ indexed.outgoing v, counter.seen e = true → G.GoodExit won (indexed.move e))
    (new_good : G.GoodExit won (indexed.move edge))
    (admitted : (HitCounter.hit (decide (G.owner v = G.player)) counter edge).admitted = true) :
    G.SafeBatch won (fun w => w = v) := by
  refine SafeBatch.ofOrdinary (choice := fun _ => indexed.move edge) ?_ ?_ ?_
  · intro w same
    subst w
    exact outside
  · intro w same _
    subst w
    exact indexed.legal v edge member
  · intro w same m follows
    subst w
    by_cases own : G.owner v = G.player
    · rw [← follows.2 own]
      exact new_good
    · have all := (indexed.hit_ready won v counter edge invariant member fresh pending sound new_good admitted).resolve_left
        (fun self => own self.1)
      exact all.2 m follows.1

/-- 全ての良い出口が通知され、カウンターが正しければ、追加できる通常局面は残らない。 -/
theorem ordinary_closed_of_notifications (indexed : G.IndexedMoves E) (won : V → Prop)
    (counters : V → HitCounter E)
    (represented : ∀ v, won v ↔ (counters v).admitted = true)
    (invariants : ∀ v, HitCounter.Invariant (decide (G.owner v = G.player)) (indexed.outgoing v) (counters v))
    (complete : ∀ v, ¬ won v → ∀ e ∈ indexed.outgoing v,
      G.GoodExit won (indexed.move e) → (counters v).seen e = true) : G.OrdinaryClosed won := by
  classical
  intro v ordinary
  apply Classical.byContradiction
  intro outside
  have pending : (counters v).admitted = false := by
    cases flag : (counters v).admitted with
    | false => rfl
    | true => exact False.elim (outside ((represented v).mpr flag))
  rcases ordinary with ⟨own, m, legal, good⟩ | ⟨_, all_good⟩
  · obtain ⟨e, member, same⟩ := indexed.covers v m legal
    have seen := complete v outside e member (by simpa only [same] using good)
    have unseen := (invariants v).or_unseen (by simp [own]) pending e member
    rw [unseen] at seen
    cases seen
  · have all_seen : ∀ e ∈ indexed.outgoing v, (counters v).seen e = true := by
      intro e member
      exact complete v outside e member (all_good (indexed.move e) (indexed.legal v e member))
    have zero := (remaining_zero_iff (counters v).seen (indexed.outgoing v)).mpr all_seen
    have count := (invariants v).exact_count pending
    have positive := (invariants v).positive pending
    omega

/-- キューが空で、取り出した全頂点の逆辺通知と良いleafの通知が完了すれば、通常伝播は閉じる。
popしただけで通知完了とはしない。parents走査が完了する条件をnode_completeに分けている。 -/
theorem ordinary_closed_when_drained (indexed : G.IndexedMoves E) (won : V → Prop)
    (counters : V → HitCounter E) (queue : AdmissionQueue V)
    (counter_rep : ∀ v, won v ↔ (counters v).admitted = true)
    (queue_rep : ∀ v, won v ↔ queue.admitted v = true)
    (invariants : ∀ v, HitCounter.Invariant (decide (G.owner v = G.player)) (indexed.outgoing v) (counters v))
    (queue_invariant : queue.Invariant) (empty : queue.pending = [])
    (leaf_complete : ∀ v, ¬ won v → ∀ e ∈ indexed.outgoing v, ∀ score,
      indexed.move e = .leaf score → G.threshold ≤ score → (counters v).seen e = true)
    (node_complete : ∀ w ∈ queue.popped, ∀ v, ¬ won v → ∀ e ∈ indexed.outgoing v,
      indexed.move e = .node w → (counters v).seen e = true) : G.OrdinaryClosed won := by
  apply indexed.ordinary_closed_of_notifications won counters counter_rep invariants
  intro v outside e member good
  cases command : indexed.move e with
  | leaf score =>
    exact leaf_complete v outside e member score command (by simpa only [command, GoodExit] using good)
  | node w =>
    have child : won w := by simpa only [command, GoodExit] using good
    have popped := (AdmissionQueue.drained_iff_popped queue queue_invariant empty w).mp ((queue_rep w).mp child)
    exact node_complete w popped v outside e member command

end IndexedMoves
end PetaProof.ThresholdGame
