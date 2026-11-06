import PetaProof.MachineCsrScc64
import PetaProof.MachineFrameExamples32

/-! CSRの元j・重複callback・両DFSの結果を調べる人工例。合法棋譜ではない。 -/
namespace PetaProof.MachineCsrExamples64

set_option maxRecDepth 8192
open MachineFrameExamples32 (book allow fits counts)
def seed : MoveRowsCsr32.Pair := (4294967295, 4294967295)

theorem book_valid : MoveRows32.Valid book := by
  intro vertex move
  have cases_vertex : vertex.val = 0 ∨ vertex.val = 1 := by have bound := vertex.isLt; omega
  rcases cases_vertex with zero | one
  · have bound : move.val < 4 := by simpa [book, zero] using move.isLt
    have cases_index : move.val = 0 ∨ move.val = 1 ∨ move.val = 2 ∨ move.val = 3 := by omega
    rcases cases_index with h | h | h | h <;> simp [book, zero, h, MoveRows32.MoveValid]
  · have bound : move.val < 1 := by simpa [book, one] using move.isLt
    have index : move.val = 0 := by omega
    simp [book, one, index, MoveRows32.MoveValid]

theorem original_callback_slots : MachineCsrParents64.callbacks book seed 3 = [(0, 1), (0, 2), (0, 3)] := by decide
theorem duplicate_parents : MachineCsrParents64.parents book seed allow 3 = [0, 0] := by decide
theorem other_turn : MachineCsrParents64.parents book seed allow 2 = [1, 1] := by decide
theorem decoded_length : (MachineCsrParents64.parents book seed allow 3).length =
    (MachineCsrParents64.words book seed allow 3).length :=
  MachineCsrParents64.no_parent_dropped fits book counts seed allow 3
theorem duplicate_push_once :
    (RawCallbackDfs64.scan 0 allow (MachineCsrParents64.callbacks book seed 3)
      (ReverseDfsStackArray.initial (n := 4) (ComponentLabels32.empty 4))).pending = #[0] := by decide
theorem parent_and_move_filter :
    MachineCsrParents64.parents book seed (fun parent move => parent == 0 && move == 2) 3 = [0] ∧
    MachineCsrParents64.parents book seed (fun parent move => parent == 0 && move == 2) 0 = [] := by decide
theorem result_words : (MachineCsrScc64.labels book seed allow).result = #[1, 0, 0, 1] := by decide
theorem root_order : (MachineCsrScc64.labels book seed allow).roots = [1, 0] := by decide
theorem cyclic_core : MachineCsrScc64.core book seed allow = [0, 1, 2, 3] := by decide
theorem one_way_not_cyclic :
    MachineCsrScc64.core book seed (fun parent move => parent == 0 && move == 2) = [] := by decide
theorem different_seed : (MachineCsrScc64.labels book (0, 0) allow).result =
    (MachineCsrScc64.labels book seed allow).result := by decide
theorem all_denied : (MachineCsrScc64.labels book seed (fun _ _ => false)).result = #[3, 2, 1, 0] ∧
    MachineCsrScc64.core book seed (fun _ _ => false) = [] := by decide
theorem zero_vertices :
    (MachineCsrScc64.labels (n := 0) (fun vertex => Fin.elim0 vertex) seed (fun _ _ => true)).result = #[] := by decide
theorem base_loop_flips_turn :
    MachineCsrScc64.core (n := 1) (fun _ => #[.internal 0]) seed (fun _ _ => true) = [0, 1] := by decide
theorem actual_partition (a b : Fin 4) :
    ComponentResultArray.component (MachineCsrScc64.labels book seed allow) a =
      ComponentResultArray.component (MachineCsrScc64.labels book seed allow) b ↔
    ForwardDfs.Mutual (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) a b :=
  MachineCsrScc64.computed_component_iff fits book book_valid counts seed allow a b
theorem actual_core (vertex : Fin 4) : vertex ∈ MachineCsrScc64.core book seed allow ↔
    CyclicVertex (MoveRows32.relation book allow) (TurnEncoding.decode vertex) :=
  MachineCsrScc64.core_correct fits book book_valid counts seed allow vertex

theorem actual_raw_labels (a b : Fin 4) :
    ComponentLabels32.get (MachineCsrScc64.labels book seed allow).result a =
      ComponentLabels32.get (MachineCsrScc64.labels book seed allow).result b ↔
    Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode a) (TurnEncoding.decode b)) ∧
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode b) (TurnEncoding.decode a)) :=
  MachineCsrScc64.raw_labels_original_iff fits book book_valid counts seed allow a b

end PetaProof.MachineCsrExamples64
