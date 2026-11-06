import PetaProof.KosarajuPartition
import PetaProof.KosarajuStepExamples

namespace PetaProof.KosarajuStep.PartitionExamples

open ForwardDfs

/-- 二つの循環SCCと一方向の接続。HighestやSaturatedを手で与えない。 -/
theorem two_components_exact (a b : Fin 4) :
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) (List.finRange 4) Examples.outgoing) Examples.parents a =
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) (List.finRange 4) Examples.outgoing) Examples.parents b ↔
      Mutual Examples.outgoing a b :=
  component_eq_iff_mutual _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) _ _ Examples.parents_correct a b

theorem cross_edge_order :
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) (List.finRange 4) Examples.outgoing) Examples.parents 1 ≤
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) (List.finRange 4) Examples.outgoing) Examples.parents 2 :=
  component_ordered _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    _ (CoreEnumeration.finRange_covers 4) _ _ Examples.parents_correct 1 2 (by
      change some (2 : Fin 4) ∈ Examples.outgoing 1
      decide)

def sparseOut (vertex : Fin 4) : List (Option (Fin 4)) :=
  match vertex.val with
  | 0 => [some 0]
  | 1 => [none, some 2, some 2]
  | _ => []

def sparseParents (vertex : Fin 4) : List (Fin 4) :=
  match vertex.val with
  | 0 => [0]
  | 2 => [1, 1]
  | _ => []

def duplicateRoots : List (Fin 4) := [3, 1, 1, 0, 2, 3]
def selfLoop (vertex : Fin 4) : Bool := vertex == 0

theorem roots_cover (vertex : Fin 4) : vertex ∈ duplicateRoots := by
  rcases Examples.fin4_cases vertex with rfl | rfl | rfl | rfl <;> decide

theorem sparse_correct (source target : Fin 4) :
    target ∈ sparseParents source ↔ Edge sparseOut target source := by
  change target ∈ sparseParents source ↔ some source ∈ sparseOut target
  rcases Examples.fin4_cases source with rfl | rfl | rfl | rfl <;>
    rcases Examples.fin4_cases target with rfl | rfl | rfl | rfl <;> decide

theorem self_correct (vertex : Fin 4) : selfLoop vertex = true ↔ Edge sparseOut vertex vertex := by
  change selfLoop vertex = true ↔ some vertex ∈ sparseOut vertex
  rcases Examples.fin4_cases vertex with rfl | rfl | rfl | rfl <;> decide

/-- 自己ループ・孤立点・終点・外部辺・重複辺と重複した根を一緒に検査する。 -/
theorem sparse_partition_exact (a b : Fin 4) :
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) duplicateRoots sparseOut) sparseParents a =
    ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) duplicateRoots sparseOut) sparseParents b ↔ Mutual sparseOut a b :=
  component_eq_iff_mutual _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    duplicateRoots roots_cover _ _ sparse_correct a b

def sparseCore := CoreEnumeration.core
  (ComponentCycleFlags.keep (List.finRange 4)
    (ComponentNumbering.component (List.finRange 4)
      (ForwardDfs.order (List.finRange 4) duplicateRoots sparseOut) sparseParents) selfLoop) (List.finRange 4)

theorem sparse_core_exact (vertex : Fin 4) : vertex ∈ sparseCore ↔ CyclicVertex (Edge sparseOut) vertex :=
  computed_core_correct _ (CoreEnumeration.finRange_unique 4) (CoreEnumeration.finRange_covers 4)
    duplicateRoots roots_cover _ _ sparse_correct selfLoop self_correct vertex

theorem only_self_loop_survives : sparseCore = [0] := by decide

/-- 逆終了順を使わない誤実装では、二つのSCCを混ぜてしまう。 -/
theorem unreversed_order_merges_components :
    (List.finRange 4).map (ComponentNumbering.finish (List.finRange 4)
      Examples.last.finished Examples.parents).result = [some 0, some 0, some 0, some 0] := by decide

theorem empty_core : CoreEnumeration.core
    (ComponentCycleFlags.keep ([] : List (Fin 0))
      (ComponentNumbering.component [] (ForwardDfs.order [] [] (fun _ => [])) (fun _ => [])) (fun _ => false)) [] = [] := rfl

end PetaProof.KosarajuStep.PartitionExamples
