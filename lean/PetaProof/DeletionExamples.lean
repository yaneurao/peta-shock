import PetaProof.DeletionCounterstrategy
import PetaProof.HistoryStrategyExamples

/-! 削除回からの反証方策構成と、勝てる安全集合を削除しないことの検査。 -/
namespace PetaProof.DeletionExamples

open HistoryStrategyExamples
open HistoryStrategyExamples.Node

theorem own_survives_first_round : arena.goodIter 1 .own := by
  refine ⟨trivial, ?_⟩
  constructor
  · intro _
    exact ⟨.left, by simp [arena], by simp [arena], trivial⟩
  · intro other
    exact False.elim (other rfl)

theorem reply_deleted_first_round (v : Node) (other : v ≠ .own) : ¬ arena.goodIter 1 v := by
  intro alive
  cases v with
  | own => exact other rfl
  | left =>
    have good := alive.2.2 (by decide) .own rfl
    exact good.1 (by simp [arena])
  | right =>
    have good := alive.2.2 (by decide) .own rfl
    exact good.1 (by simp [arena])

/-- 相手の頂点が先に消え、その次に自分の頂点が消える2段階の例。 -/
theorem empty_after_two : ∀ v, ¬ arena.goodIter 2 v := by
  intro v alive
  cases v with
  | own =>
    obtain ⟨w, edge, _, previous⟩ := alive.2.1 rfl
    exact reply_deleted_first_round w edge previous
  | left => exact reply_deleted_first_round .left (by decide) alive.1
  | right => exact reply_deleted_first_round .right (by decide) alive.1

noncomputable def constructedCounter : arena.Counterstrategy :=
  arena.counterstrategyOfEmpty 2 empty_after_two

theorem constructed_rank_own : constructedCounter.ranking.rank .own = 2 := by
  change arena.deletionTime 2 empty_after_two .own = 2
  have spec := arena.deletionTime_spec 2 empty_after_two .own
  have positive := arena.deletionTime_pos 2 empty_after_two .own
  have not_one : arena.deletionTime 2 empty_after_two .own ≠ 1 := by
    intro equal
    rw [equal] at spec
    exact spec.2.1 own_survives_first_round
  omega

theorem constructed_rank_reply : constructedCounter.ranking.rank .left = 1 := by
  change arena.deletionTime 2 empty_after_two .left = 1
  have bound := arena.deletionTime_le_of_absent 2 empty_after_two .left 1
    (reply_deleted_first_round .left (by decide))
  have positive := arena.deletionTime_pos 2 empty_after_two .left
  omega

theorem constructed_counter_defeats_all_histories (root : Node) : ¬ arena.HistoryWinning root :=
  constructedCounter.not_history_winning arena root

/-- 反証方策を入力せず、空の候補削除結果だけから履歴依存戦略を排除する。 -/
theorem emptiness_alone_defeats_all_histories (root : Node) : ¬ arena.HistoryWinning root :=
  arena.empty_excludes_history 2 empty_after_two root

def safeArena : HistoryArena Unit where
  edge := fun _ _ => True
  owner := fun _ => false
  player := false
  bad := fun _ _ => False
  moves_exist := fun _ => ⟨(), trivial⟩

theorem safe_all : safeArena.GoodSafeSet (fun _ => True) := by
  intro v _
  exact ⟨fun _ => ⟨(), trivial, fun h => h, trivial⟩,
    fun other => False.elim (other rfl)⟩

theorem safe_vertex_never_deleted (n : Nat) : safeArena.goodIter n () :=
  safeArena.goodSafeSet_survives safe_all n () trivial

theorem safe_vertex_history_winning : safeArena.HistoryWinning () :=
  safeArena.goodSafeSet_history_winning safe_all () trivial

theorem safe_arena_has_no_counter : ¬ Nonempty safeArena.Counterstrategy := by
  rintro ⟨counter⟩
  exact counter.not_history_winning safeArena () safe_vertex_history_winning

end PetaProof.DeletionExamples
