import PetaProof.ForwardDfsFrameArray

/-!
フレーム・訪問表・終了列を配列にした第一DFSを、直接逆順走査へ渡す。
フレームの中身と循環フラグの同時実行は未精密化である。
-/
namespace PetaProof.FrameArrayScc

variable {n : Nat} {E : Type}

def labels (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n)) : ComponentResultArray.State n :=
  ReverseOrderArray.run (ForwardDfsFrameArray.finish outgoing (List.finRange n)).finished parents (ComponentResultArray.initial n)

theorem labels_exact (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n)) :
    labels outgoing parents = ReverseOrderArray.labels outgoing parents := by
  unfold labels ReverseOrderArray.labels
  rw [ForwardDfsFrameArray.finish_array_exact]

theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat)
    (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge outgoing parent child) (a b : Fin n) :
    ComponentResultArray.component (labels outgoing parents) a = ComponentResultArray.component (labels outgoing parents) b ↔
      ForwardDfs.Mutual outgoing a b := by
  rw [labels_exact]
  exact ReverseOrderArray.computed_component_iff fits outgoing parents transpose a b

theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let outgoing := SccIndexedView.outgoing view allow
    let table := labels outgoing (SccIndexedView.parents view (List.finRange n) allow)
    let order := VertexStack32.model n (ForwardDfsFrameArray.finish outgoing (List.finRange n)).finished
    let flags := SccCycleArray.finish view (List.finRange n) order allow
    (ComponentLabels32.get table.result vertex).toNat < flags.number.roots.length ∧
      (ComponentLabels32.get table.result vertex).toNat < flags.flags.size := by
  dsimp only
  rw [labels_exact, ForwardDfsFrameArray.finish_array_exact]
  exact ReverseOrderArray.flag_read_written fits view allow vertex

theorem core_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let outgoing := SccIndexedView.outgoing view allow
    let order := VertexStack32.model n (ForwardDfsFrameArray.finish outgoing (List.finRange n)).finished
    vertex ∈ ComponentResultArray.extract (labels outgoing (SccIndexedView.parents view (List.finRange n) allow))
      (SccCycleArray.finish view (List.finRange n) order allow).flags ↔
        CyclicVertex (SccIndexedView.relation view allow) vertex := by
  dsimp only
  rw [labels_exact, ForwardDfsFrameArray.finish_array_exact]
  exact ReverseOrderArray.core_correct fits view allow vertex

end PetaProof.FrameArrayScc
