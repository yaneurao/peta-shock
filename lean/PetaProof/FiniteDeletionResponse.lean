import PetaProof.FiniteDeletionRanks

/-! 計算した削除順位を使い、有限出辺から反証の応手を選択する。 -/
namespace PetaProof.HistoryArena.DeletionInput

variable {n : Nat} {A : HistoryArena (Fin n)} (input : DeletionInput A)

def responseFlag (ranks : Array Nat) (v w : Fin n) : Bool :=
  input.bad v w || decide (rankAt ranks w < rankAt ranks v)

theorem responseFlag_correct (ranks : Array Nat) (v w : Fin n) :
    input.responseFlag ranks v w = true ↔
      (¬ A.bad v w → rankAt ranks w < rankAt ranks v) := by
  simp only [responseFlag, Bool.or_eq_true, decide_eq_true_eq, input.bad_correct]
  constructor
  · rintro (bad | less) nonbad
    · exact False.elim (nonbad bad)
    · exact less
  · intro safe
    by_cases bad : A.bad v w
    · exact Or.inl bad
    · exact Or.inr (safe bad)

def response (ranks : Array Nat) (v : Fin n) : Fin n :=
  ((input.next v).find? (input.responseFlag ranks v)).getD v

theorem response_sound (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v)
    (ranks : Array Nat) (correct : ∀ v, rankAt ranks v = A.deletionTime horizon empty v)
    (v : Fin n) (other : A.owner v ≠ A.player) :
    A.edge v (input.response ranks v) ∧
      (¬ A.bad v (input.response ranks v) → rankAt ranks (input.response ranks v) < rankAt ranks v) := by
  obtain ⟨w, edge, decreases⟩ := A.response_exists horizon empty v other
  have flag : input.responseFlag ranks v w = true :=
    (input.responseFlag_correct ranks v w).mpr (by simpa only [correct] using decreases)
  cases found : (input.next v).find? (input.responseFlag ranks v) with
  | none => exact False.elim ((List.find?_eq_none.mp found) w ((input.edges v w).mpr edge) flag)
  | some child =>
    have legal := (input.edges v child).mp (List.mem_of_find?_eq_some found)
    have safe := (input.responseFlag_correct ranks v child).mp (List.find?_some found)
    simpa only [response, found, Option.getD_some] using And.intro legal safe

/-- 証明は消去され、実行時には既存の順位配列と有限出辺だけを使う。 -/
def counterFromRanks (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v)
    (ranks : Array Nat) (correct : ∀ v, rankAt ranks v = A.deletionTime horizon empty v) : A.Counterstrategy :=
  { response := input.response ranks
    legal := fun v other => (input.response_sound horizon empty ranks correct v other).1
    ranking := {
      rank := rankAt ranks
      strict_good := by
        intro v w follows nonbad
        by_cases own : A.owner v = A.player
        · rw [correct w, correct v]
          exact A.own_good_decreases horizon empty v w own follows.1 nonbad
        · have same := follows.2 own
          subst w
          exact (input.response_sound horizon empty ranks correct v own).2 nonbad
    } }

/-- 実行結果は一回束縛し、各応手の選択では順位配列だけを参照する。 -/
def counter (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) : A.Counterstrategy :=
  let ranks := (input.run horizon).ranks
  input.counterFromRanks horizon empty ranks (input.final_rank horizon empty)

theorem counter_rank (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    (input.counter horizon empty).ranking.rank v = A.deletionTime horizon empty v :=
  input.final_rank horizon empty v

theorem counter_rank_bound (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    0 < (input.counter horizon empty).ranking.rank v ∧
      (input.counter horizon empty).ranking.rank v ≤ horizon := by
  rw [input.counter_rank horizon empty v]
  exact ⟨A.deletionTime_pos horizon empty v, (A.deletionTime_spec horizon empty v).1⟩

include input in
theorem counter_refutes (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (root : Fin n) :
    ¬ A.HistoryWinning root := (input.counter horizon empty).not_history_winning A root

/-- 停止回そのものを探索・選択せず、頂点数を固定の実行上限として使える。 -/
theorem empty_at_size (noWinners : ∀ v, ¬ A.HistoryWinning v) : ∀ v, ¬ A.goodIter n v := by
  obtain ⟨k, bounded, empty⟩ := A.empty_of_no_history_winners (List.finRange n)
    (by intro v; simp [List.finRange, List.mem_ofFn]) noWinners
  have cap : k ≤ n := by simpa using bounded
  intro v alive
  exact empty v (goodIter_earlier n k cap v alive)

def counterOfNoWinners (noWinners : ∀ v, ¬ A.HistoryWinning v) : A.Counterstrategy :=
  input.counter n (empty_at_size noWinners)

theorem counterOfNoWinners_bound (noWinners : ∀ v, ¬ A.HistoryWinning v) (v : Fin n) :
    0 < (input.counterOfNoWinners noWinners).ranking.rank v ∧
      (input.counterOfNoWinners noWinners).ranking.rank v ≤ n :=
  input.counter_rank_bound n (empty_at_size noWinners) v

def emptyFlag (state : State) : Bool :=
  (List.finRange n).all (fun v => !aliveAt state.alive v)

theorem emptyFlag_correct (state : State) :
    emptyFlag (n := n) state = true ↔ ∀ v : Fin n, aliveAt state.alive v = false := by
  simp [emptyFlag, List.all_eq_true, List.finRange, List.mem_ofFn]

/-- 空集合の検査が成功した場合にだけ、同じ実行の順位から反証証拠を返す。 -/
def checkedCounter : Option A.Counterstrategy :=
  let state := input.run n
  if gone : emptyFlag (n := n) state = true then
    let empty : ∀ v, ¬ A.goodIter n v := fun v alive => by
      have no := (emptyFlag_correct state).mp gone v
      change aliveAt (input.run n).alive v = false at no
      have yes := (input.run_alive n v).mpr alive
      simp only [no, Bool.false_eq_true] at yes
    some (input.counterFromRanks n empty state.ranks (input.final_rank n empty))
  else none

theorem checkedCounter_complete (noWinners : ∀ v, ¬ A.HistoryWinning v) :
    input.checkedCounter.isSome = true := by
  have empty := empty_at_size noWinners
  have flag : emptyFlag (n := n) (input.run n) = true := by
    apply (emptyFlag_correct _).mpr
    intro v
    apply Bool.eq_false_iff.mpr
    intro alive
    exact empty v ((input.run_alive n v).mp alive)
  simp [checkedCounter, flag]

theorem checkedCounter_iff : input.checkedCounter.isSome = true ↔ ∀ v, ¬ A.HistoryWinning v := by
  constructor
  · intro success
    cases found : input.checkedCounter with
    | none => simp [found] at success
    | some counter => exact fun v => counter.not_history_winning A v
  · exact input.checkedCounter_complete

end PetaProof.HistoryArena.DeletionInput
