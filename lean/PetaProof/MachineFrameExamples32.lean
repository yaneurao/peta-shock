import PetaProof.MachineFrameRows32

/-! 二つの基礎局面の人工例。合法な将棋棋譜を表すものではない。 -/
namespace PetaProof.MachineFrameExamples32

set_option maxRecDepth 4096

def book : MoveRows32.Book 2 := fun vertex =>
  if vertex.val = 0 then #[.leaf, .internal 1, .internal 1, .internal 1]
  else #[.internal 0]
def allow (_ move : UInt32) : Bool := move != 1
def rows := MachineFrameRows32.rows book allow
def first := ForwardDfsRaw32.discover rows (ForwardDfsRaw32.initial 4) 0

theorem fits : TurnEncoding32.Fits 2 := by unfold TurnEncoding32.Fits; decide
theorem counts : MoveRows32.CountsFit book := by
  intro vertex
  simp only [book]
  split <;> decide
theorem original_slots : rows 0 = #[none, none, some 3, some 3] := by decide
theorem other_turn : rows 1 = #[none, none, some 2, some 2] := by decide
theorem leaf_query : MachineFrameRows32.query book allow 0 0 = none := by decide
theorem denied_query : MachineFrameRows32.query book allow 0 1 = none := by decide
theorem live_query : MachineFrameRows32.query book allow 0 2 = some 3 := by decide
theorem duplicate_query : MachineFrameRows32.query book allow 0 3 = some 3 := by decide
theorem leaf_consumed : (ForwardDfsRaw32.walk rows 1 first).stack = #[(0, 1)] := by decide
theorem denied_consumed : (ForwardDfsRaw32.walk rows 2 first).stack = #[(0, 2)] := by decide
theorem original_index_before_push : (ForwardDfsRaw32.walk rows 3 first).stack = #[(0, 3), (3, 0)] := by decide
theorem no_push_for_return : (ForwardDfsRaw32.walk rows 4 first).stack = #[(0, 3), (3, 1)] := by decide
theorem finish_order : (ForwardDfsRaw32.finish rows (List.finRange 4)).finished = #[3, 0, 2, 1] := by decide
theorem cyclic_core : RawFrameScc32.core rows = [0, 1, 2, 3] := by decide
theorem all_blocked : RawFrameScc32.core (MachineFrameRows32.rows book (fun _ _ => false)) = [] := by decide

theorem actual_core (vertex : Fin 4) : vertex ∈ RawFrameScc32.core rows ↔
    CyclicVertex (MoveRows32.relation book allow) (TurnEncoding.decode vertex) :=
  MachineFrameRows32.core_correct fits book counts allow vertex

end PetaProof.MachineFrameExamples32
