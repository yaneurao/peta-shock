import PetaProof.DeletionCounterstrategy

/-! 有限隣接リストから同期削除を実行し、最初の削除回を選択公理なしで数値化する。
これは参照計算であり、局所化やキューによる高速化の計算量は扱わない。 -/
namespace PetaProof.HistoryArena

variable {n : Nat} {A : HistoryArena (Fin n)}

structure DeletionInput (A : HistoryArena (Fin n)) where
  next : Fin n → List (Fin n)
  edges : ∀ v w, w ∈ next v ↔ A.edge v w
  bad : Fin n → Fin n → Bool
  bad_correct : ∀ v w, bad v w = true ↔ A.bad v w

namespace DeletionInput

variable (input : DeletionInput A)

def aliveAt (alive : Array Bool) (v : Fin n) : Bool := (alive[v.val]?).getD false
def rankAt (ranks : Array Nat) (v : Fin n) : Nat := (ranks[v.val]?).getD 0

def stays (alive : Array Bool) (v : Fin n) : Bool :=
  if A.owner v = A.player then
    (input.next v).any (fun w => !input.bad v w && aliveAt alive w)
  else (input.next v).all (fun w => !input.bad v w && aliveAt alive w)

theorem stays_correct (alive : Array Bool) (v : Fin n) :
    input.stays alive v = true ↔ A.StayGood (fun w => aliveAt alive w = true) v := by
  have good (w : Fin n) : (!input.bad v w && aliveAt alive w) = true ↔
      ¬ A.bad v w ∧ aliveAt alive w = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    have flag := input.bad_correct v w
    cases b : input.bad v w <;> simp_all
  by_cases own : A.owner v = A.player
  · rw [stays, if_pos own, List.any_eq_true]
    constructor
    · rintro ⟨w, member, flag⟩
      exact ⟨fun _ => ⟨w, (input.edges v w).mp member, (good w).mp flag⟩,
        fun other => False.elim (other own)⟩
    · intro safe
      obtain ⟨w, edge, nonbad, inside⟩ := safe.1 own
      exact ⟨w, (input.edges v w).mpr edge, (good w).mpr ⟨nonbad, inside⟩⟩
  · rw [stays, if_neg own, List.all_eq_true]
    constructor
    · intro all
      exact ⟨fun impossible => False.elim (own impossible),
        fun _ w edge => (good w).mp (all w ((input.edges v w).mpr edge))⟩
    · intro safe w member
      exact (good w).mpr (safe.2 own w ((input.edges v w).mp member))

structure State where
  alive : Array Bool
  ranks : Array Nat

def initial : State := ⟨Array.replicate n true, Array.replicate n 0⟩

/-- 新しい生存表は旧表のみから計算する。順位は旧表で生存していた回数を数える。 -/
def step (state : State) : State where
  alive := Array.ofFn (fun v : Fin n => aliveAt state.alive v && input.stays state.alive v)
  ranks := Array.ofFn (fun v : Fin n => rankAt state.ranks v + if aliveAt state.alive v then 1 else 0)

def run (data : DeletionInput A) : Nat → State
  | 0 => initial (n := n)
  | k + 1 => data.step (run data k)

theorem run_sizes (k : Nat) : (input.run k).alive.size = n ∧ (input.run k).ranks.size = n := by
  cases k <;> simp [run, initial, step]

theorem run_alive (k : Nat) (v : Fin n) :
    aliveAt (input.run k).alive v = true ↔ A.goodIter k v := by
  induction k generalizing v with
  | zero => simp [run, initial, aliveAt, goodIter]
  | succ k ih =>
    have same : (fun w => aliveAt (input.run k).alive w = true) = A.goodIter k := by
      funext w
      exact propext (ih w)
    simp only [run, step, aliveAt, Array.getElem?_ofFn, v.isLt, ↓reduceDIte,
      Option.getD_some, Bool.and_eq_true]
    change (aliveAt (input.run k).alive v = true ∧ input.stays (input.run k).alive v = true) ↔ _
    rw [ih v, input.stays_correct, same]
    rfl

end DeletionInput

/-- 同期削除は一度消した頂点を復活させない。 -/
theorem goodIter_earlier (k j : Nat) (before : j ≤ k) (v : Fin n) (alive : A.goodIter k v) :
    A.goodIter j v := by
  induction k with
  | zero =>
    have same : j = 0 := by omega
    simpa [same] using alive
  | succ k ih =>
    by_cases same : j = k + 1
    · simpa [same] using alive
    · exact ih (by omega) alive.1

theorem goodIter_iff_before_deletion (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v)
    (k : Nat) (v : Fin n) : A.goodIter k v ↔ k < A.deletionTime horizon empty v := by
  have spec := A.deletionTime_spec horizon empty v
  constructor
  · intro alive
    apply Nat.lt_of_not_ge
    intro notBefore
    exact spec.2.1 (goodIter_earlier k _ notBefore v alive)
  · exact spec.2.2 k

namespace DeletionInput

variable (input : DeletionInput A)

theorem run_rank (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v)
    (k : Nat) (v : Fin n) :
    rankAt (input.run k).ranks v = min k (A.deletionTime horizon empty v) := by
  induction k with
  | zero => simp [run, initial, rankAt]
  | succ k ih =>
    change rankAt (Array.ofFn (fun w : Fin n => rankAt (input.run k).ranks w +
      if aliveAt (input.run k).alive w then 1 else 0)) v = _
    simp only [rankAt, Array.getElem?_ofFn, v.isLt, ↓reduceDIte, Option.getD_some]
    change rankAt (input.run k).ranks v + (if aliveAt (input.run k).alive v then 1 else 0) = _
    rw [ih]
    by_cases alive : aliveAt (input.run k).alive v = true
    · have before := (goodIter_iff_before_deletion horizon empty k v).mp ((input.run_alive k v).mp alive)
      simp only [alive, ↓reduceIte]
      omega
    · have after : ¬ k < A.deletionTime horizon empty v := by
        intro before
        exact alive ((input.run_alive k v).mpr ((goodIter_iff_before_deletion horizon empty k v).mpr before))
      have flag : aliveAt (input.run k).alive v = false := Bool.eq_false_iff.mpr alive
      simp only [flag, Bool.false_eq_true, ↓reduceIte]
      omega

/-- 数値配列の結果は、存在証明から選んだ最初の削除回と等しい。 -/
theorem final_rank (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    rankAt (input.run horizon).ranks v = A.deletionTime horizon empty v := by
  rw [input.run_rank horizon empty horizon v]
  exact Nat.min_eq_right (A.deletionTime_spec horizon empty v).1

/-- 空になった後で余分な同期回を実行しても、記録済み順位は変わらない。 -/
theorem rank_stable_after_empty (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v)
    (later : Nat) (after : horizon ≤ later) (v : Fin n) :
    rankAt (input.run later).ranks v = rankAt (input.run horizon).ranks v := by
  rw [input.run_rank horizon empty later v, input.final_rank horizon empty v]
  have bound := (A.deletionTime_spec horizon empty v).1
  exact Nat.min_eq_right (by omega)

end DeletionInput
end PetaProof.HistoryArena
