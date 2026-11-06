import PetaProof.ComponentNumbering

namespace PetaProof.ComponentNumbering.Examples

def emptyParents (_ : Fin 3) : List (Fin 3) := []

theorem duplicate_roots_are_skipped :
    (finish [0, 1, 2] [0, 0, 1, 2, 1] emptyParents).roots = [0, 1, 2] ∧
    (List.finRange 3).map (component [0, 1, 2] [0, 0, 1, 2, 1] emptyParents) = [0, 1, 2] := by decide

def cycleParents (vertex : Fin 3) : List (Fin 3) :=
  match vertex.val with
  | 0 => [1, 1]
  | 1 => [0]
  | _ => []

def cycleFinish : State (Fin 3) := finish (List.finRange 3) [0, 1, 2, 0] cycleParents

theorem cycle_and_isolated_labels :
    cycleFinish.roots = [0, 2] ∧
    (List.finRange 3).map (component (List.finRange 3) [0, 1, 2, 0] cycleParents) = [0, 0, 1] := by decide

theorem all_ids_are_bounded (vertex : Fin 3) :
    component (List.finRange 3) [0, 1, 2, 0] cycleParents vertex < 3 := by
  apply component_bound _ (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
  intro v
  have small := v.isLt
  have split : v = 0 ∨ v = 1 ∨ v = 2 := by
    rcases Nat.lt_succ_iff.mp small with bound
    have values : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
    rcases values with same | same | same
    · exact Or.inl (Fin.ext same)
    · exact Or.inr (Or.inl (Fin.ext same))
    · exact Or.inr (Or.inr (Fin.ext same))
  rcases split with rfl | rfl | rfl <;> simp

theorem full_enum_uint32 (vertex : Fin 3) :
    let id := component (List.finRange 3) (List.finRange 3) cycleParents vertex
    (UInt32.ofNat id).toNat = id ∧ UInt32.ofNat id ≠ UInt32.ofNat 4294967295 :=
  component_uint32 _ (CoreEnumeration.finRange_unique 3) (CoreEnumeration.finRange_covers 3)
    _ (CoreEnumeration.finRange_covers 3) cycleParents (by decide) vertex

theorem missing_root_stays_unassigned :
    (finish (List.finRange 3) [0] emptyParents).result 1 = none := by decide

theorem empty_graph :
    (finish ([] : List (Fin 0)) [] (fun _ => [])).roots = [] := rfl

/-- 元の辺は0→1のみ。逆辺探索を1から始めると、範囲は正しくてもSCCではなくなる。 -/
def oneWayParents (vertex : Fin 2) : List (Fin 2) := if vertex = 1 then [0] else []

def oneWay (source target : Fin 2) : Prop := source = 0 ∧ target = 1

theorem wrong_order_merges :
    component (List.finRange 2) [1, 0] oneWayParents (0 : Fin 2) =
    component (List.finRange 2) [1, 0] oneWayParents (1 : Fin 2) := by decide

theorem no_return_walk : ¬Nonempty (Walk oneWay (1 : Fin 2) 0) := by
  rintro ⟨walk⟩
  have nondecreasing := walk.nat_monotone Fin.val (by
    intro source target edge
    rcases edge with ⟨rfl, rfl⟩
    decide)
  change 1 ≤ 0 at nondecreasing
  omega

theorem wrong_order_not_partition :
    ¬∃ partition : SccPartition oneWay,
      partition.component = component (List.finRange 2) [1, 0] oneWayParents := by
  rintro ⟨partition, computed⟩
  apply no_return_walk
  apply partition.connected 1 0
  rw [computed]
  exact wrong_order_merges.symm

theorem correct_order_separates :
    (List.finRange 2).map (component (List.finRange 2) [0, 1] oneWayParents) = [0, 1] := by decide

end PetaProof.ComponentNumbering.Examples
