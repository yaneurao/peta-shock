import PetaProof.ReverseDfsStackArray

/-!
第二DFSのラベルとLIFOをともにUInt32配列にした根走査。
以前の根走査とのState自体の一致を示し、SCC分割・生番号によるcore読出しへ接続する。
-/
namespace PetaProof.ComponentStackArray

variable {n : Nat} {E : Type}

def step (parents : Fin n → List (Fin n)) (state : ComponentResultArray.State n)
    (root : Fin n) : ComponentResultArray.State n :=
  if ComponentLabels32.get state.result root = ComponentLabels32.unset then
    let report := ReverseDfsStackArray.explore state.roots.length state.result parents root
    ⟨report.result, state.roots ++ [root]⟩
  else state

theorem step_exact (fits : n ≤ UInt32.size) (parents : Fin n → List (Fin n))
    (state : ComponentResultArray.State n) (root : Fin n) :
    step parents state root = ComponentResultArray.step parents state root := by
  have result := congrArg ReverseDfsResultArray.State.result
    (ReverseDfsStackArray.explore_refines fits state.roots.length state.result parents root)
  change (ReverseDfsStackArray.explore state.roots.length state.result parents root).result = _ at result
  unfold step ComponentResultArray.step
  split <;> simp only [result]

def pass (parents : Fin n → List (Fin n)) : List (Fin n) → ComponentResultArray.State n → ComponentResultArray.State n
  | [], state => state
  | root :: rest, state => pass parents rest (step parents state root)

theorem pass_exact (fits : n ≤ UInt32.size) (parents : Fin n → List (Fin n))
    (order : List (Fin n)) (state : ComponentResultArray.State n) :
    pass parents order state = ComponentResultArray.pass parents order state := by
  induction order generalizing state with
  | nil => rfl
  | cons root rest ih => rw [pass, ih, step_exact fits, ComponentResultArray.pass]

def finish (parents : Fin n → List (Fin n)) (order : List (Fin n)) : ComponentResultArray.State n :=
  pass parents order (ComponentResultArray.initial n)

theorem finish_exact (fits : n ≤ UInt32.size) (parents : Fin n → List (Fin n)) (order : List (Fin n)) :
    finish parents order = ComponentResultArray.finish parents order :=
  pass_exact fits parents order _

theorem word_capacity (fits : n ≤ ComponentLabels32.unset.toNat) : n ≤ UInt32.size := by
  have limit : ComponentLabels32.unset.toNat < UInt32.size := by decide
  omega

theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat)
    (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge outgoing parent child) (a b : Fin n) :
    ComponentResultArray.component (finish parents (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing)) a =
      ComponentResultArray.component (finish parents (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing)) b ↔
        ForwardDfs.Mutual outgoing a b := by
  rw [finish_exact (word_capacity fits)]
  exact ComponentResultArray.computed_component_iff fits outgoing parents transpose a b

theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (order : List (Fin n)) (covered : ∀ vertex, vertex ∈ order) (allow : E → Bool) (vertex : Fin n) :
    let labels := finish (SccIndexedView.parents view (List.finRange n) allow) order
    let flags := SccCycleArray.finish view (List.finRange n) order allow
    (ComponentLabels32.get labels.result vertex).toNat < flags.number.roots.length ∧
      (ComponentLabels32.get labels.result vertex).toNat < flags.flags.size := by
  dsimp only
  rw [finish_exact (word_capacity fits)]
  exact ComponentResultArray.flag_read_written fits view order covered allow vertex

theorem extract_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let order := ForwardDfs.order (List.finRange n) (List.finRange n) (SccIndexedView.outgoing view allow)
    vertex ∈ ComponentResultArray.extract (finish (SccIndexedView.parents view (List.finRange n) allow) order)
      (SccCycleArray.finish view (List.finRange n) order allow).flags ↔
        CyclicVertex (SccIndexedView.relation view allow) vertex := by
  dsimp only
  rw [finish_exact (word_capacity fits)]
  exact ComponentResultArray.extract_correct fits view allow vertex

end PetaProof.ComponentStackArray
