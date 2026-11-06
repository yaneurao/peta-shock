import PetaProof.QueueWorkBudget

/-! safety() の局所削除キュー。親の重複投入を許し、削除済みガードで逆辺の再走査を防ぐ。 -/
namespace PetaProof.DeletionQueue

universe u
variable {V : Type u} [DecidableEq V]

/-- 未削除頂点が持つ逆辺の残予算。証明用であり、実装で再集計しない。 -/
def credit (weight : V → Nat) (deleted : V → Bool) : List V → Nat
  | [] => 0
  | v :: rest => (if deleted v then 0 else weight v) + credit weight deleted rest

theorem credit_absent (weight : V → Nat) (deleted : V → Bool) (v : V)
    (vertices : List V) (absent : v ∉ vertices) :
    credit weight (markSeen deleted v) vertices = credit weight deleted vertices := by
  induction vertices with
  | nil => rfl
  | cons w rest ih =>
    have different : w ≠ v := by intro same; subst w; exact absent (by simp)
    have tail : v ∉ rest := by intro member; exact absent (by simp [member])
    simp [credit, markSeen, different, ih tail]

theorem credit_mark (weight : V → Nat) (deleted : V → Bool) (v : V)
    (vertices : List V) (unique : vertices.Nodup) (member : v ∈ vertices)
    (fresh : deleted v = false) :
    credit weight (markSeen deleted v) vertices + weight v = credit weight deleted vertices := by
  induction vertices with
  | nil => simp at member
  | cons w rest ih =>
    have nodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | tail
    · subst w
      have unchanged := credit_absent weight deleted v rest nodup.1
      simp [credit, markSeen, fresh, unchanged, Nat.add_comm]
    · by_cases same : w = v
      · subst w; exact False.elim (nodup.1 tail)
      · have decrease := ih nodup.2 tail
        simp only [credit, markSeen, if_neg same] at *
        split <;> omega

structure State (V : Type u) where
  deleted : V → Bool
  pending : List V

def budget (vertices : List V) (weight : V → Nat) (state : State V) : Nat :=
  state.pending.length + credit weight state.deleted vertices

/-- alive ガードを通過した場合だけ逆辺を走査する。
    emitted はその走査で積む親。別の辺から同じ親が出てもよく、一辺あたり高々一件。 -/
inductive Step (weight : V → Nat) : State V → State V → Prop
  | stale (deleted : V → Bool) (v : V) (rest : List V) (old : deleted v = true) :
      Step weight ⟨deleted, v :: rest⟩ ⟨deleted, rest⟩
  | remove (deleted : V → Bool) (v : V) (rest emitted : List V)
      (fresh : deleted v = false) (bounded : emitted.length ≤ weight v) :
      Step weight ⟨deleted, v :: rest⟩ ⟨markSeen deleted v, rest ++ emitted⟩

theorem decreases (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat) {before after : State V}
    (step : Step weight before after) : budget vertices weight after + 1 ≤ budget vertices weight before := by
  cases step with
  | stale deleted v rest old => simp only [budget, List.length_cons]; omega
  | remove deleted v rest emitted fresh bounded =>
    have decrement := credit_mark weight deleted v vertices unique (covered v) fresh
    simp only [budget, List.length_cons, List.length_append]
    omega

inductive Run (weight : V → Nat) : State V → Nat → State V → Prop
  | done (state) : Run weight state 0 state
  | next {start middle finish n} : Step weight start middle → Run weight middle n finish →
      Run weight start (n + 1) finish

theorem deleted_preserved (weight : V → Nat) {before after : State V}
    (step : Step weight before after) (v : V) (old : before.deleted v = true) :
    after.deleted v = true := by
  cases step with
  | stale => exact old
  | remove deleted w rest emitted fresh bounded =>
    change deleted v = true at old
    simp [markSeen, old]

/-- 一度削除した頂点は、重複した待機項目が残っていても再走査の対象にならない。 -/
theorem run_deleted_preserved (weight : V → Nat) {start finish : State V} {n : Nat}
    (run : Run weight start n finish) (v : V) (old : start.deleted v = true) :
    finish.deleted v = true := by
  induction run with
  | done => exact old
  | next step tail ih => exact ih (deleted_preserved weight step v old)

theorem run_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat)
    {start finish : State V} {n : Nat} (run : Run weight start n finish) :
    budget vertices weight finish + n ≤ budget vertices weight start := by
  induction run with
  | done => omega
  | next step tail ih =>
    have drop := decreases vertices unique covered weight step
    omega

/-- 各走査が有限個の親を返すなら、どの有効な選択でも有限回で空にできる。
    counter/bad の正しさを仮定せず、キュー制御だけを対象とする。 -/
theorem drains (vertices : List V) (unique : vertices.Nodup) (covered : ∀ v, v ∈ vertices)
    (weight : V → Nat)
    (progress : ∀ state, state.pending ≠ [] → ∃ after, Step weight state after)
    (start : State V) : ∃ n finish, Run weight start n finish ∧ finish.pending = [] ∧
      n ≤ budget vertices weight start := by
  suffices ∀ b state, budget vertices weight state = b → ∃ n finish,
      Run weight state n finish ∧ finish.pending = [] ∧ n ≤ budget vertices weight state by
    exact this _ start rfl
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro state same
    by_cases empty : state.pending = []
    · exact ⟨0, state, Run.done state, empty, Nat.zero_le _⟩
    · obtain ⟨after, step⟩ := progress state empty
      have drop := decreases vertices unique covered weight step
      obtain ⟨n, finish, run, ended, bounded⟩ := ih (budget vertices weight after) (by omega) after rfl
      exact ⟨n + 1, finish, Run.next step run, ended, by omega⟩

omit [DecidableEq V] in
theorem initial_credit (vertices : List V) (weight : V → Nat) :
    credit weight (fun _ => false) vertices = (vertices.map weight).sum := by
  induction vertices with
  | nil => rfl
  | cons v rest ih => simp [credit, ih]

/-- 全候補をaliveで開始する場合、pop回数は初期投入数＋逆辺総数以下。 -/
theorem initial_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat) (seeds : List V)
    {finish : State V} {n : Nat}
    (run : Run weight ⟨fun _ => false, seeds⟩ n finish) :
    n ≤ seeds.length + (vertices.map weight).sum := by
  have bound := run_bound vertices unique covered weight run
  have initial : budget vertices weight ⟨fun _ => false, seeds⟩ =
      seeds.length + (vertices.map weight).sum := by simp [budget, initial_credit]
  omega

/-- 各popが実際に読む逆辺数。削除済みの重複項目では0。 -/
def scanned (weight : V → Nat) (state : State V) : Nat :=
  match state.pending with
  | [] => 0
  | v :: _ => if state.deleted v then 0 else weight v

theorem scan_credit (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat) {before after : State V}
    (step : Step weight before after) :
    credit weight after.deleted vertices + scanned weight before = credit weight before.deleted vertices := by
  cases step with
  | stale deleted v rest old => simp [scanned, old]
  | remove deleted v rest emitted fresh bounded =>
    simpa [scanned, fresh] using credit_mark weight deleted v vertices unique (covered v) fresh

/-- 通常の実行列に、証明用の逆辺走査数だけを付記する。 -/
inductive ScannedRun (weight : V → Nat) : State V → Nat → Nat → State V → Prop
  | done (state) : ScannedRun weight state 0 0 state
  | next {start middle finish n scans} : Step weight start middle →
      ScannedRun weight middle n scans finish →
      ScannedRun weight start (n + 1) (scanned weight start + scans) finish

theorem scan_conservation (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat)
    {start finish : State V} {n scans : Nat} (run : ScannedRun weight start n scans finish) :
    credit weight finish.deleted vertices + scans = credit weight start.deleted vertices := by
  induction run with
  | done => omega
  | next step tail ih =>
    have conserved := scan_credit vertices unique covered weight step
    omega

theorem initial_scan_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat) (seeds : List V)
    {finish : State V} {n scans : Nat}
    (run : ScannedRun weight ⟨fun _ => false, seeds⟩ n scans finish) :
    scans ≤ (vertices.map weight).sum := by
  have conserved := scan_conservation vertices unique covered weight run
  have initial := initial_credit vertices weight
  change credit weight finish.deleted vertices + scans = credit weight (fun _ => false) vertices at conserved
  omega

omit [DecidableEq V] in
theorem credit_le_total (vertices : List V) (weight : V → Nat) (deleted : V → Bool) :
    credit weight deleted vertices ≤ (vertices.map weight).sum := by
  induction vertices with
  | nil => exact Nat.le_refl _
  | cons v rest ih =>
    simp only [credit, List.map_cons, List.sum_cons]
    split <;> omega

/-- 初期wonを候補から除外している場合も、同じS+M上界を使える。 -/
theorem arbitrary_initial_bound (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ v, v ∈ vertices) (weight : V → Nat)
    {start finish : State V} {n : Nat} (run : Run weight start n finish) :
    n ≤ start.pending.length + (vertices.map weight).sum := by
  have bound := run_bound vertices unique covered weight run
  have total := credit_le_total vertices weight start.deleted
  unfold budget at bound
  omega

end PetaProof.DeletionQueue
