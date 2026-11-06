import PetaProof.DeletionReachability
import PetaProof.EscapeExact

/-! 同期削除の最初の削除回を、単一目標へ向かう実FIFOの距離に接続する。 -/
namespace PetaProof.HistoryArena.DeletionInput

universe u
variable {n : Nat} {A : HistoryArena (Fin n)} (input : DeletionInput A)

theorem reach_distance_eq (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    input.reachArena.escapeDistance (fun v => v = none) (reachVertices (n := n)).length (some v) =
      some (A.deletionTime horizon empty v) := by
  classical
  let arena := input.reachArena
  let goal := fun v : Option (Fin n) => v = none
  let vertices := reachVertices (n := n)
  have spec := A.deletionTime_spec horizon empty v
  have arrived := (input.reach_layer_iff (A.deletionTime horizon empty v) v).mpr spec.2.1
  have inside := arena.escapeLayer_complete goal vertices reachVertices_cover _ (some v) arrived
  have lower : A.deletionTime horizon empty v ≤ arena.escapeRank goal vertices.length (some v) :=
    A.deletionTime_le_of_absent horizon empty v _
      ((input.reach_layer_iff _ v).mp (arena.escapeRank_spec goal vertices.length (some v) inside).2.1)
  have upper := (arena.escapeRank_le_iff goal vertices.length (some v) inside _).mpr arrived
  have same : arena.escapeRank goal vertices.length (some v) = A.deletionTime horizon empty v := by omega
  change (if arena.escapeLayer goal vertices.length (some v) then
    some (arena.escapeRank goal vertices.length (some v)) else none) = _
  rw [if_pos inside, same]

variable {E : Type u} [DecidableEq E]

-- 逆辺と出辺の索引は帰着先のグラフを表すものを受け取る。
variable (indexed : EscapePropagation.Input (Option (Fin n)) E)

def fifoTable : Array (Option Nat) :=
  let final := (EscapePropagation.State.start indexed [none]).map
    (EscapePropagation.State.run indexed (reachVertices (n := n)).length)
  Array.ofFn (fun v : Fin n => match final with
    | none => none
    | some state => (state.counters (some v)).result)

theorem fifoTable_size : (fifoTable indexed (n := n)).size = n := by
  simp [fifoTable]

theorem fifoTable_cell (v : Fin n) : (fifoTable indexed (n := n))[v.val]? =
    some (EscapePropagation.State.runLabels indexed [none] (reachVertices (n := n)) (some v)) := by
  cases started : EscapePropagation.State.start indexed [none] <;>
    simp [fifoTable, EscapePropagation.State.runLabels, started, Array.getElem?_ofFn, v.isLt]

/-- 経路数ではなく、一意な頂点の投入と元辺IDの通知を数える。 -/
theorem fifo_events_bound (edges : List E) (covered : ∀ edge, edge ∈ edges)
    (state : EscapePropagation.State (Option (Fin n)) E)
    (started : EscapePropagation.State.start indexed [none] = some state) :
    let final := EscapePropagation.State.run indexed (n + 1) state
    final.frame.queue.total.length ≤ n + 1 ∧
      (indexed.toInput.notifications (final.frame.queue.popped.map Prod.fst)).length ≤ edges.length := by
  let final := EscapePropagation.State.run indexed (n + 1) state
  have valid := (EscapePropagation.State.started_run_good indexed [none] state started (n + 1)).1
  refine ⟨?_, indexed.toInput.fifo_notification_count_bound final.frame.queue valid.frame.queue edges covered⟩
  have bound := EscapeFifo.total_length_bound final.frame.queue valid.frame.queue
    (reachVertices (n := n)) reachVertices_cover
  simpa only [reachVertices_length] using bound

/-- 辺関係の一致だけでは並行IDの個数は決まらないため、入力の辺数条件も明示する。 -/
theorem fifo_events_input_bound (edges : List E) (covered : ∀ edge, edge ∈ edges)
    (size : edges.length = 1 + ((List.finRange n).map (fun v => (input.next v).length)).sum)
    (state : EscapePropagation.State (Option (Fin n)) E)
    (started : EscapePropagation.State.start indexed [none] = some state) :
    let final := EscapePropagation.State.run indexed (n + 1) state
    final.frame.queue.total.length ≤ n + 1 ∧
      (indexed.toInput.notifications (final.frame.queue.popped.map Prod.fst)).length ≤
        1 + ((List.finRange n).map (fun v => (input.next v).length)).sum := by
  have bound := fifo_events_bound indexed edges covered state started
  simpa only [size] using bound

variable (matching : EscapePropagation.ArenaMatch indexed input.reachArena)

include matching in
theorem fifoTable_exact (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    (fifoTable indexed (n := n))[v.val]? = some (some (A.deletionTime horizon empty v)) := by
  rw [fifoTable_cell]
  rw [EscapePropagation.State.runLabels_exact (target := fun vertex => vertex = none)
    indexed matching [none] (reachVertices (n := n))
    (by intro vertex; simp) reachVertices_cover]
  rw [input.reach_distance_eq horizon empty v]

def fifoRanks (labels : Array (Option Nat)) : Array Nat := labels.map (fun label => label.getD 0)

include matching in
theorem fifoRanks_exact (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    rankAt (fifoRanks (fifoTable indexed (n := n))) v = A.deletionTime horizon empty v := by
  have cell := input.fifoTable_exact indexed matching horizon empty v
  simp [rankAt, fifoRanks, Array.getElem?_map, cell]

include matching in
/-- 同期計算とFIFO計算は、同じ数値順位を返す。 -/
theorem fifoRanks_reference (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    rankAt (fifoRanks (fifoTable indexed (n := n))) v = rankAt (input.run horizon).ranks v := by
  rw [input.fifoRanks_exact indexed matching horizon empty v, input.final_rank horizon empty v]

/-- FIFOの返却表を一回束縛し、同期削除を再実行せずに反証応手を構成する。 -/
def fifoCounter (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) : A.Counterstrategy :=
  let labels := fifoTable indexed (n := n)
  input.counterFromRanks horizon empty (fifoRanks labels) (input.fifoRanks_exact indexed matching horizon empty)

theorem fifoCounter_rank (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    (input.fifoCounter indexed matching horizon empty).ranking.rank v = A.deletionTime horizon empty v :=
  input.fifoRanks_exact indexed matching horizon empty v

def tableComplete (labels : Array (Option Nat)) : Bool :=
  (List.finRange n).all (fun v => ((labels[v.val]?).getD none).isSome)

theorem tableComplete_correct (labels : Array (Option Nat)) :
    tableComplete (n := n) labels = true ↔
      ∀ v : Fin n, ((labels[v.val]?).getD none).isSome = true := by
  simp [tableComplete, List.all_eq_true, List.finRange, List.mem_ofFn]

include matching in
theorem fifo_complete_empty (complete : tableComplete (n := n) (fifoTable indexed) = true) :
    ∀ v, ¬ A.goodIter (n + 1) v := by
  intro v
  have known := (tableComplete_correct _).mp complete v
  rw [fifoTable_cell] at known
  simp only [Option.getD_some] at known
  cases found : EscapePropagation.State.runLabels indexed [none] (reachVertices (n := n)) (some v) with
  | none => simp [found] at known
  | some distance =>
    have reached := (EscapePropagation.State.runLabels_finite_iff
      (target := fun vertex => vertex = none) indexed matching [none] (reachVertices (n := n))
      (by intro vertex; simp) reachVertices_cover (some v)).mp ⟨distance, found⟩
    have absent := (input.reach_layer_iff _ v).mp reached
    simpa only [reachVertices_length] using absent

/-- 順位表を一度だけ作り、全て有限なら同じ表から反証方策を返す。同期削除は実行しない。 -/
def fifoCheckedCounter : Option A.Counterstrategy :=
  let labels := fifoTable indexed (n := n)
  if complete : tableComplete (n := n) labels = true then
    let empty := input.fifo_complete_empty indexed matching complete
    some (input.counterFromRanks (n + 1) empty (fifoRanks labels)
      (input.fifoRanks_exact indexed matching (n + 1) empty))
  else none

include matching in
theorem fifoCheckedCounter_complete (noWinners : ∀ v, ¬ A.HistoryWinning v) :
    (input.fifoCheckedCounter indexed matching).isSome = true := by
  have empty := empty_at_size noWinners
  have complete : tableComplete (n := n) (fifoTable indexed) = true := by
    apply (tableComplete_correct _).mpr
    intro v
    rw [input.fifoTable_exact indexed matching n empty v]
    rfl
  simp [fifoCheckedCounter, complete]

theorem fifoCheckedCounter_iff : (input.fifoCheckedCounter indexed matching).isSome = true ↔
    ∀ v, ¬ A.HistoryWinning v := by
  constructor
  · intro success
    cases found : input.fifoCheckedCounter indexed matching with
    | none => simp [found] at success
    | some counter => exact fun v => counter.not_history_winning A v
  · exact input.fifoCheckedCounter_complete indexed matching

theorem fifoCheckedCounter_agrees : (input.fifoCheckedCounter indexed matching).isSome =
    input.checkedCounter.isSome := by
  have first := input.fifoCheckedCounter_iff indexed matching
  have second := input.checkedCounter_iff
  cases left : (input.fifoCheckedCounter indexed matching).isSome <;>
    cases right : input.checkedCounter.isSome <;> simp_all

end PetaProof.HistoryArena.DeletionInput
