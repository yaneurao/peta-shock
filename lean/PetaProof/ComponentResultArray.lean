import PetaProof.ReverseDfsResultArray

/-!
result配列を根走査の間も保持し、成分番号の書込を両DFSのSCC意味論へ接続する。
rootsは番号会計の証明用であり、本番に保存しない。idのループ変数自体はNatのまま。
-/
namespace PetaProof.ComponentResultArray

variable {n : Nat}

structure State (n : Nat) where
  result : Array UInt32
  roots : List (Fin n)

def unpack (state : State n) : ComponentNumbering.State (Fin n) := ⟨ComponentLabels32.model state.result, state.roots⟩
def initial (n : Nat) : State n := ⟨ComponentLabels32.empty n, []⟩

theorem initial_refines (n : Nat) : unpack (initial n) = ComponentNumbering.initial := by
  simp only [unpack, initial, ComponentLabels32.empty_model, ComponentNumbering.initial]

def step (parents : Fin n → List (Fin n)) (state : State n) (root : Fin n) : State n :=
  if ComponentLabels32.get state.result root = ComponentLabels32.unset then
    let report := ReverseDfsResultArray.explore state.roots.length state.result parents root
    ⟨report.result, state.roots ++ [root]⟩
  else state

theorem step_size (parents : Fin n → List (Fin n)) (state : State n) (root : Fin n) :
    (step parents state root).result.size = state.result.size := by
  unfold step
  split <;> simp only [ReverseDfsResultArray.explore_size]

/-- 新しい成分を開始するときだけid<nが必要。既割当の根では追加の番号を使わない。 -/
theorem fresh_id_bound (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (state : State n) (valid : ComponentNumbering.Invariant (unpack state)) (root : Fin n)
    (fresh : ComponentLabels32.get state.result root = ComponentLabels32.unset) :
    state.roots.length < ComponentLabels32.unset.toNat := by
  have fresh_model : (unpack state).result root = none := (ComponentLabels32.guard_exact state.result root).mp fresh
  have next := ComponentNumbering.step_preserves n parents (unpack state) valid root
  have bound := ComponentNumbering.roots_bound (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) _ next
  change ComponentLabels32.model state.result root = none at fresh_model
  simp only [ComponentNumbering.step, unpack, fresh_model, ↓reduceIte,
    List.length_append, List.length_singleton, List.length_finRange] at bound
  omega

theorem step_refines (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (state : State n) (size : state.result.size = n) (valid : ComponentNumbering.Invariant (unpack state)) (root : Fin n) :
    unpack (step parents state root) = ComponentNumbering.step n parents (unpack state) root := by
  by_cases fresh : ComponentLabels32.get state.result root = ComponentLabels32.unset
  · have found := (ComponentLabels32.guard_exact state.result root).mp fresh
    have bounded := fresh_id_bound fits parents state valid root fresh
    have report := ReverseDfsResultArray.explore_refines state.roots.length bounded state.result size parents root
    have labels : ComponentLabels32.model (ReverseDfsResultArray.explore state.roots.length state.result parents root).result =
        (ComponentNumbering.descend n parents (unpack state) root).result := by
      change (ReverseDfsResultArray.unpack _).result = _
      rw [report]
      simp only [ReverseDfsStack.explore, List.length_finRange, ComponentNumbering.descend, unpack]
    simp only [step, if_pos fresh, unpack, ComponentNumbering.step, found, ↓reduceIte, labels]
  · have assigned : (unpack state).result root ≠ none := by
      intro found
      exact fresh ((ComponentLabels32.guard_exact state.result root).mpr found)
    simp only [step, if_neg fresh, ComponentNumbering.step, if_neg assigned]

def pass (parents : Fin n → List (Fin n)) : List (Fin n) → State n → State n
  | [], state => state
  | root :: rest, state => pass parents rest (step parents state root)

theorem pass_refines (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (order : List (Fin n)) (state : State n) (size : state.result.size = n)
    (valid : ComponentNumbering.Invariant (unpack state)) :
    unpack (pass parents order state) = ComponentNumbering.pass n parents order (unpack state) ∧
      (pass parents order state).result.size = n := by
  induction order generalizing state with
  | nil => exact ⟨rfl, size⟩
  | cons root rest ih =>
    have same := step_refines fits parents state size valid root
    have next_valid : ComponentNumbering.Invariant (unpack (step parents state root)) := by
      rw [same]
      exact ComponentNumbering.step_preserves n parents (unpack state) valid root
    obtain ⟨after, after_size⟩ := ih (step parents state root) (by rw [step_size]; exact size) next_valid
    refine ⟨?_, after_size⟩
    rw [pass, after, same, ComponentNumbering.pass]

def finish (parents : Fin n → List (Fin n)) (order : List (Fin n)) : State n := pass parents order (initial n)

theorem finish_refines (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n)) (order : List (Fin n)) :
    unpack (finish parents order) = ComponentNumbering.finish (List.finRange n) order parents := by
  have valid : ComponentNumbering.Invariant (unpack (initial n)) := by
    rw [initial_refines]
    exact ComponentNumbering.initial_invariant
  have same := (pass_refines fits parents order (initial n) (by simp [initial, ComponentLabels32.empty]) valid).1
  simpa only [finish, ComponentNumbering.finish, List.length_finRange, initial_refines] using same

theorem finish_size (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n)) (order : List (Fin n)) :
    (finish parents order).result.size = n := by
  have valid : ComponentNumbering.Invariant (unpack (initial n)) := by
    rw [initial_refines]
    exact ComponentNumbering.initial_invariant
  exact (pass_refines fits parents order (initial n) (by simp [initial, ComponentLabels32.empty]) valid).2

def component (state : State n) (vertex : Fin n) : Nat := (ComponentLabels32.model state.result vertex).getD 0

theorem component_exact (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n)) (order : List (Fin n)) :
    component (finish parents order) = ComponentNumbering.component (List.finRange n) order parents := by
  funext vertex
  change ((unpack (finish parents order)).result vertex).getD 0 = _
  rw [finish_refines fits parents order]
  rfl

theorem final_labels (fits : n ≤ ComponentLabels32.unset.toNat) (parents : Fin n → List (Fin n))
    (order : List (Fin n)) (covered : ∀ vertex, vertex ∈ order) (vertex : Fin n) :
    let state := finish parents order
    ComponentLabels32.get state.result vertex ≠ ComponentLabels32.unset ∧
      (ComponentLabels32.get state.result vertex).toNat = component state vertex ∧
      component state vertex < state.roots.length ∧ component state vertex < n := by
  have same := finish_refines fits parents order
  have assigned := ComponentNumbering.finish_result (List.finRange n) order parents covered vertex
  have valid := ComponentNumbering.finish_invariant (List.finRange n) order parents
  have bound := ComponentNumbering.component_bound (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) order covered parents vertex
  rw [← same, ← component_exact fits parents order] at assigned
  have decoded := (ComponentLabels32.decode_some_iff _ _).mp assigned
  have roots_bound := valid.bounded vertex _ (ComponentNumbering.finish_result (List.finRange n) order parents covered vertex)
  rw [← same, ← component_exact fits parents order] at roots_bound
  refine ⟨decoded.1, decoded.2, roots_bound, ?_⟩
  simpa only [List.length_finRange, ← component_exact fits parents order] using bound

/-- 正しいSCC分割を仮定せず、第一DFSの実終了順を入力した配列結果の意味を導く。 -/
theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat)
    (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge outgoing parent child) (a b : Fin n) :
    component (finish parents (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing)) a =
      component (finish parents (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing)) b ↔
        ForwardDfs.Mutual outgoing a b := by
  rw [component_exact fits]
  exact KosarajuStep.component_eq_iff_mutual (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) (List.finRange n) (CoreEnumeration.finRange_covers n) outgoing parents transpose a b

end PetaProof.ComponentResultArray
