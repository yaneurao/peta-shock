import PetaProof.SccArrayView
import PetaProof.CsrExamples

namespace PetaProof.CsrArray.Examples

def target := Csr.Examples.target
def edges := Csr.Examples.edges

theorem bounded : ∀ edge ∈ edges, target edge < 4 := by
  intro edge member
  simp [edges, Csr.Examples.edges] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem finite_optional_storage :
    (built 4 target edges).cursor = #[2, 2, 4, 4, 4] ∧
    (built 4 target edges).memory = #[some 1, some 3, some 0, some 2] := by decide

theorem finite_plain_storage :
    (CsrPayloadArray.built 4 99 target edges).memory = #[1, 3, 0, 2] := by decide

theorem optional_all_safe : AllSafe target edges (initial 4 4 (Csr.degrees target edges)) :=
  (built_represents_and_safe 4 target edges bounded).2

theorem plain_all_safe :
    CsrPayloadArray.AllSafe target edges (CsrPayloadArray.initial 4 4 (Csr.degrees target edges) 99) :=
  CsrPayloadArray.built_safe 4 99 target edges bounded

theorem plain_rows : (List.range 4).map (CsrPayloadArray.row 4 99 target edges) = [[1, 3], [], [0, 2], []] := by decide

theorem initial_values_do_not_leak (vertex : Nat) (inside : vertex < 4) :
    CsrPayloadArray.row 4 99 target edges vertex = CsrPayloadArray.row 4 7 target edges vertex :=
  CsrPayloadArray.row_seed_independent 4 99 7 target edges bounded vertex inside

/-- 区間末尾のcursor=sizeは正しい終了値だが、そこへ追加で書くことは許さない。 -/
theorem one_past_end_is_not_writable :
    ¬CsrPayloadArray.StepSafe target 0 (CsrPayloadArray.built 4 99 target edges) := by
  unfold CsrPayloadArray.StepSafe
  decide

/-- M=0でもoffsetはn+1個あり、空区間ではメモリ要素を参照しない。 -/
theorem empty_storage :
    (CsrPayloadArray.built 4 99 target []).cursor = #[0, 0, 0, 0, 0] ∧
    (CsrPayloadArray.built 4 99 target []).memory = #[] ∧
    (List.range 4).map (CsrPayloadArray.row 4 99 target []) = [[], [], [], []] := by decide

theorem duplicate_values_keep_distinct_slots :
    (CsrPayloadArray.built 4 99 target [0, 1, 0]).memory = #[1, 0, 0] := by decide

theorem exact_rows_by_general_proof (vertex : Nat) (inside : vertex < 4) :
    CsrPayloadArray.row 4 99 target edges vertex = Csr.bucket target edges vertex :=
  CsrPayloadArray.row_exact 4 99 target edges bounded vertex inside

def view := SccIndexedView.Examples.view
def allow := SccIndexedView.Examples.allow

theorem array_cycle_core : SccArrayView.core view 0 allow = [0, 1, 2] := by decide

theorem array_core_exact (vertex : Fin 3) :
    vertex ∈ SccArrayView.core view 0 allow ↔ CyclicVertex (SccIndexedView.relation view allow) vertex :=
  SccArrayView.core_correct view 0 allow vertex

theorem array_core_seed_independent : SccArrayView.core view 0 allow = SccArrayView.core view 6 allow := by
  rw [SccArrayView.core_exact, SccArrayView.core_exact]

theorem indexed_array_safe :
    CsrPayloadArray.AllSafe (SccCsrView.target view) (SccCsrView.edges view)
      (CsrPayloadArray.initial 3 (SccCsrView.edges view).length
        (Csr.degrees (SccCsrView.target view) (SccCsrView.edges view)) 0) :=
  SccArrayView.writes_safe view 0

end PetaProof.CsrArray.Examples
