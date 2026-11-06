import PetaProof.SccConstructedView
import PetaProof.CsrArrayExamples

namespace PetaProof.CsrConstructionExamples

def target := CsrArray.Examples.target
def edges := CsrArray.Examples.edges
def raw := CsrCountArray.built 4 target edges

theorem counted_with_shift : raw = #[0, 2, 0, 2, 0] := by decide

/-- 累積和の途中には、更新済みの累積値と未更新の入次数が混在する。 -/
theorem prefix_intermediate :
    CsrPrefixArray.run 2 1 raw = #[0, 2, 2, 2, 0] ∧
    CsrPrefixArray.run 3 1 raw = #[0, 2, 2, 4, 0] ∧
    CsrPrefixArray.run 4 1 raw = #[0, 2, 2, 4, 4] := by decide

theorem reverse_update_is_not_prefix_sum :
    CsrPrefixArray.step 1 (CsrPrefixArray.step 2 (CsrPrefixArray.step 3 (CsrPrefixArray.step 4 raw))) =
      #[0, 2, 2, 2, 2] := by decide

theorem full_construction :
    let book := CsrConstructArray.build 4 99 target edges
    book.positions = #[0, 2, 2, 4, 4] ∧ book.state.memory = #[1, 3, 0, 2] ∧
      book.state.cursor = #[2, 2, 4, 4, 4] := by decide

theorem full_rows :
    (List.range 4).map (CsrConstructArray.row 4 99 target edges) = [[1, 3], [], [0, 2], []] := by decide

theorem all_phases_safe : CsrConstructArray.Safe 4 99 target edges :=
  CsrConstructArray.build_safe 4 99 target edges CsrArray.Examples.bounded

theorem exact_rows_by_general_proof (vertex : Nat) (inside : vertex < 4) :
    CsrConstructArray.row 4 99 target edges vertex = Csr.bucket target edges vertex :=
  CsrConstructArray.row_exact 4 99 target edges CsrArray.Examples.bounded vertex inside

theorem first_child_uses_index_one :
    CsrCountArray.built 1 (fun _ : Nat => 0) [0, 1] = #[0, 2] := by decide

theorem last_child_uses_last_slot :
    CsrCountArray.built 3 (fun _ : Nat => 2) [0, 0] = #[0, 0, 0, 2] ∧
    CsrPrefixArray.built 3 (fun _ : Nat => 2) [0, 0] = #[0, 0, 0, 2] := by decide

theorem zero_vertices :
    let book := CsrConstructArray.build 0 99 target []
    book.positions = #[0] ∧ book.state.cursor = #[0] ∧ book.state.memory = #[] := by decide

theorem zero_vertices_safe : CsrConstructArray.Safe 0 99 target [] :=
  CsrConstructArray.build_safe 0 99 target [] (by intro edge member; cases member)

theorem no_edges :
    let book := CsrConstructArray.build 4 99 target []
    book.positions = #[0, 0, 0, 0, 0] ∧ book.state.memory = #[] ∧
      (List.range 4).map (CsrConstructArray.row 4 99 target []) = [[], [], [], []] := by decide

theorem unshifted_count_violates_zero :
    ¬CsrCountArray.Represents 1 (fun _ => 0) #[1, 0] := by
  intro rep
  have wrong := rep.zero
  change some (1 : Nat) = some 0 at wrong
  cases wrong

def view := CsrArray.Examples.view
def allow := CsrArray.Examples.allow

theorem constructed_core : SccConstructedView.core view 0 allow = [0, 1, 2] := by decide

theorem constructed_core_exact (vertex : Fin 3) :
    vertex ∈ SccConstructedView.core view 0 allow ↔ CyclicVertex (SccIndexedView.relation view allow) vertex :=
  SccConstructedView.core_correct view 0 allow vertex

theorem indexed_construction_safe :
    CsrConstructArray.Safe 3 0 (SccCsrView.target view) (SccCsrView.edges view) :=
  SccConstructedView.construction_safe view 0

end PetaProof.CsrConstructionExamples
