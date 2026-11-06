import PetaProof.MoveRowsScc

/-! 抽象グラフによる回帰例。合法な将棋棋譜を表すという主張ではない。 -/
namespace PetaProof.MoveRowsExamples

open IndexedMoveRows

-- 0番局面は空。初期値(0,0)は不正IDだが、他局面の逆辺は正常に格納できる。
def rows : Rows 3 := fun vertex =>
  if vertex.val = 0 then #[]
  else if vertex.val = 1 then #[some 2, none, some 2]
  else #[some 1]

theorem invalid_default : decode rows (0, 0) = none := rfl
theorem invalid_vertex : decode rows (3, 0) = none := rfl
theorem invalid_move : decode rows (1, 3) = none := rfl
theorem leaf_keeps_its_slot : (decode rows (1, 1)).map (view rows).child = some none := by decide

theorem stable_parallel_edges : MoveRowsCsr.rawIncoming rows (0, 0) 2 = [(1, 0), (1, 2)] := by decide
theorem reverse_edge : MoveRowsCsr.rawIncoming rows (0, 0) 1 = [(2, 0)] := by decide
theorem empty_row : MoveRowsCsr.rawIncoming rows (0, 0) 0 = [] := by decide
theorem invalid_seed_does_not_leak : MoveRowsCsr.rawIncoming rows (999, 999) 2 = [(1, 0), (1, 2)] := by decide
theorem safe_with_invalid_seed : CsrConstructArray.Safe 3 (0, 0) (MoveRowsCsr.target rows) (MoveRowsCsr.rawEdges rows) :=
  MoveRowsCsr.construction_safe rows (0, 0)
theorem three_internal_edges :
    (CsrConstructArray.build 3 (0, 0) (MoveRowsCsr.target rows) (MoveRowsCsr.rawEdges rows)).state.memory.size = 3 := by decide

-- 親局面1の先手状態(番号2)だけ、指し手0を禁止する。平行な指し手2は残る。
def selective (parent move : Nat) : Bool := !(parent == 2 && move == 0)

theorem distinct_move_permission :
    MoveRowsScc.parents rows (0, 0) selective (2, true) = [(1, false)] := by decide
theorem both_parallel_moves_allowed :
    MoveRowsScc.parents rows (0, 0) selective (2, false) = [(1, true), (1, true)] := by decide

set_option maxRecDepth 4096 in
theorem parallel_alternative_keeps_cycle :
    (MoveRowsScc.core rows (0, 0) selective).map (fun state => (TurnEncoding.encode state).val) = [2, 3, 4, 5] := by decide

theorem actual_core_meaning (state : TurnEncoding.State 3) :
    state ∈ MoveRowsScc.core rows (0, 0) selective ↔
      CyclicVertex (SccIndexedView.relation (TurnSharedGraph.expanded (view rows))
        (MoveRowsScc.allowAt rows selective)) state :=
  MoveRowsScc.core_correct rows (0, 0) selective state

def noMoves : Rows 2 := fun _ => #[]
theorem no_typed_edge (edge : Edge noMoves) : False := by
  have impossible := edge.2.isLt
  change edge.2.val < 0 at impossible
  omega

theorem no_moves_capacity :
    (CsrConstructArray.build 2 (0, 0) (MoveRowsCsr.target noMoves) (MoveRowsCsr.rawEdges noMoves)).state.memory.size = 0 := by decide
theorem no_moves_core : MoveRowsScc.core noMoves (0, 0) (fun _ _ => true) = [] := by decide

def empty : Rows 0 := fun vertex => Fin.elim0 vertex
theorem empty_book_safe : CsrConstructArray.Safe 0 (0, 0) (MoveRowsCsr.target empty) (MoveRowsCsr.rawEdges empty) :=
  MoveRowsCsr.construction_safe empty (0, 0)
theorem empty_book_core : MoveRowsScc.core empty (0, 0) (fun _ _ => true) = [] := by decide

end PetaProof.MoveRowsExamples
