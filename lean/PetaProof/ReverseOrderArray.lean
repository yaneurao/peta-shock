import PetaProof.ForwardDfsOrderArray

/-!
終了列をsize-1から0へ直接読む第二DFSの外側ループ。
欠落・復号失敗分岐は全域化用で、実行範囲内では必ず成功することを別に証明する。
-/
namespace PetaProof.ReverseOrderArray

variable {n : Nat} {E : Type}

def loop (array : Array UInt32) (parents : Fin n → List (Fin n)) : Nat → ComponentResultArray.State n → ComponentResultArray.State n
  | 0, state => state
  | remaining + 1, state =>
    match array[remaining]?.bind (VertexStack32.decode n) with
    | none => loop array parents remaining state
    | some root => loop array parents remaining (ComponentStackArray.step parents state root)

/-- 末尾の追加要素をまだ読まない区間では、元の配列と同じ実行になる。 -/
theorem loop_prefix (array : Array UInt32) (word : UInt32) (parents : Fin n → List (Fin n))
    (remaining : Nat) (inside : remaining ≤ array.size) (state : ComponentResultArray.State n) :
    loop (array.push word) parents remaining state = loop array parents remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have bound : remaining < array.size := by omega
    have different : remaining ≠ array.size := Nat.ne_of_lt bound
    simp only [loop, Array.getElem?_push, if_neg different]
    cases found : array[remaining]?.bind (VertexStack32.decode n) <;>
      simp only [found] <;> exact ih (by omega) _

def run (array : Array UInt32) (parents : Fin n → List (Fin n)) (state : ComponentResultArray.State n) : ComponentResultArray.State n :=
  loop array parents array.size state

theorem run_refines (array : Array UInt32) (valid : VertexStack32.Valid n array)
    (parents : Fin n → List (Fin n)) (state : ComponentResultArray.State n) :
    run array parents state = ComponentStackArray.pass parents (VertexStack32.model n array) state := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some word =>
    have inside := VertexStack32.top_range array valid word top
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    have previous := VertexStack32.valid_of_push rest word valid
    simp only [run, Array.size_push, loop, Array.getElem?_push_size]
    have decoded : (some word).bind (VertexStack32.decode n) = some (⟨word.toNat, inside⟩ : Fin n) := by
      simp [VertexStack32.decode, inside]
    rw [decoded]
    simp only []
    rw [loop_prefix rest word parents rest.size (Nat.le_refl _)]
    change run rest parents _ = _
    rw [run_refines rest previous parents, VertexStack32.model_push_word rest word inside, ComponentStackArray.pass]
termination_by array.size
decreasing_by simp_all [Array.size_push]

/-- 全ての実反復が読む添字を一括して覆う。0からのアンダーフローは起こさない。 -/
theorem all_reads_success (array : Array UInt32) (valid : VertexStack32.Valid n array)
    (remaining : Nat) (bounded : remaining ≤ array.size) (index : Nat) (inside : index < remaining) :
    ∃ vertex : Fin n, array[index]?.bind (VertexStack32.decode n) = some vertex := by
  obtain ⟨vertex, decoded, _⟩ := FinishingArray32.read_success array valid index (Nat.lt_of_lt_of_le inside bounded)
  exact ⟨vertex, decoded⟩

def labels (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n)) : ComponentResultArray.State n :=
  run (ForwardDfsOrderArray.finish outgoing (List.finRange n)).finished parents (ComponentResultArray.initial n)

theorem labels_exact (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (parents : Fin n → List (Fin n)) :
    labels outgoing parents = ComponentStackArray.finish parents (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing) := by
  unfold labels
  rw [run_refines _ (ForwardDfsOrderArray.finish_valid fits outgoing _).finished,
    ForwardDfsOrderArray.reverse_order_exact fits]
  rfl

theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat)
    (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge outgoing parent child) (a b : Fin n) :
    ComponentResultArray.component (labels outgoing parents) a = ComponentResultArray.component (labels outgoing parents) b ↔
      ForwardDfs.Mutual outgoing a b := by
  rw [labels_exact (ComponentStackArray.word_capacity fits)]
  exact ComponentStackArray.computed_component_iff fits outgoing parents transpose a b

theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let outgoing := SccIndexedView.outgoing view allow
    let table := labels outgoing (SccIndexedView.parents view (List.finRange n) allow)
    let order := VertexStack32.model n (ForwardDfsOrderArray.finish outgoing (List.finRange n)).finished
    let flags := SccCycleArray.finish view (List.finRange n) order allow
    (ComponentLabels32.get table.result vertex).toNat < flags.number.roots.length ∧
      (ComponentLabels32.get table.result vertex).toNat < flags.flags.size := by
  dsimp only
  rw [labels_exact (ComponentStackArray.word_capacity fits),
    ForwardDfsOrderArray.reverse_order_exact (ComponentStackArray.word_capacity fits)]
  exact ComponentStackArray.flag_read_written fits view _
    (ForwardDfs.order_covers (List.finRange n) (CoreEnumeration.finRange_unique n) (CoreEnumeration.finRange_covers n)
      (List.finRange n) (CoreEnumeration.finRange_covers n) _) allow vertex

theorem core_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let outgoing := SccIndexedView.outgoing view allow
    let order := VertexStack32.model n (ForwardDfsOrderArray.finish outgoing (List.finRange n)).finished
    vertex ∈ ComponentResultArray.extract (labels outgoing (SccIndexedView.parents view (List.finRange n) allow))
      (SccCycleArray.finish view (List.finRange n) order allow).flags ↔
        CyclicVertex (SccIndexedView.relation view allow) vertex := by
  dsimp only
  rw [labels_exact (ComponentStackArray.word_capacity fits),
    ForwardDfsOrderArray.reverse_order_exact (ComponentStackArray.word_capacity fits)]
  exact ComponentStackArray.extract_correct fits view allow vertex

end PetaProof.ReverseOrderArray
