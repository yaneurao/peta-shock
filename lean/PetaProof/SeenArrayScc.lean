import PetaProof.ForwardDfsSeenArray

/-!
訪問表配列版の第一DFSから得た終了順を、番号表・スタック配列版の第二DFSへ渡す。
循環フラグは既存の別モデルとの結果照合であり、同時更新全体の形式化ではない。
-/
namespace PetaProof.SeenArrayScc

variable {n : Nat} {E : Type}

def order (outgoing : Fin n → List (Option (Fin n))) : List (Fin n) :=
  ForwardDfsSeenArray.order outgoing (List.finRange n)

def labels (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n)) : ComponentResultArray.State n :=
  ComponentStackArray.finish parents (order outgoing)

theorem order_exact (outgoing : Fin n → List (Option (Fin n))) :
    order outgoing = ForwardDfs.order (List.finRange n) (List.finRange n) outgoing :=
  ForwardDfsSeenArray.order_exact outgoing _

theorem labels_exact (fits : n ≤ UInt32.size) (outgoing : Fin n → List (Option (Fin n)))
    (parents : Fin n → List (Fin n)) :
    labels outgoing parents = ComponentResultArray.finish parents
      (ForwardDfs.order (List.finRange n) (List.finRange n) outgoing) := by
  rw [labels, order_exact, ComponentStackArray.finish_exact fits]

theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat)
    (outgoing : Fin n → List (Option (Fin n))) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge outgoing parent child) (a b : Fin n) :
    ComponentResultArray.component (labels outgoing parents) a = ComponentResultArray.component (labels outgoing parents) b ↔
      ForwardDfs.Mutual outgoing a b := by
  rw [labels_exact (ComponentStackArray.word_capacity fits)]
  exact ComponentResultArray.computed_component_iff fits outgoing parents transpose a b

def flags (view : SccIndexedView.View (Fin n) E) (allow : E → Bool) : Array UInt8 :=
  (SccCycleArray.finish view (List.finRange n) (order (SccIndexedView.outgoing view allow)) allow).flags

theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let table := labels (SccIndexedView.outgoing view allow) (SccIndexedView.parents view (List.finRange n) allow)
    let report := SccCycleArray.finish view (List.finRange n) (order (SccIndexedView.outgoing view allow)) allow
    (ComponentLabels32.get table.result vertex).toNat < report.number.roots.length ∧
      (ComponentLabels32.get table.result vertex).toNat < (flags view allow).size := by
  have covered := ForwardDfsSeenArray.order_covers (SccIndexedView.outgoing view allow)
    (List.finRange n) (CoreEnumeration.finRange_covers n)
  exact ComponentStackArray.flag_read_written fits view _ covered allow vertex

def core (view : SccIndexedView.View (Fin n) E) (allow : E → Bool) : List (Fin n) :=
  ComponentResultArray.extract
    (labels (SccIndexedView.outgoing view allow) (SccIndexedView.parents view (List.finRange n) allow)) (flags view allow)

theorem core_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    vertex ∈ core view allow ↔ CyclicVertex (SccIndexedView.relation view allow) vertex := by
  unfold core labels flags
  rw [order_exact]
  exact ComponentStackArray.extract_correct fits view allow vertex

end PetaProof.SeenArrayScc
