import PetaProof.BuiltParentInput
import PetaProof.GeneratedThresholdExamples

/-! 同じ子への別辺ID、自己辺、leaf除外、構築した逆辺からの値計算を検査する。 -/
namespace PetaProof.ReverseAdjacencyExamples

open ThresholdGame

inductive Edge where
  | first | second | leaf
  deriving DecidableEq

def move : Edge → Move Bool
  | .first | .second => .node false
  | .leaf => .leaf 20

def edges : List Edge := [.first, .second, .leaf]
def vertices : List Bool := [false, true]

theorem prepended_order : ReverseAdjacency.scan move edges (fun _ => []) false = [.second, .first] := by decide
theorem stable_row : ReverseAdjacency.build move vertices edges false = [.first, .second] := by decide
theorem empty_other_row : ReverseAdjacency.build move vertices edges true = [] := by decide
theorem reversal_two_items : ReverseAdjacency.reversalWork move vertices edges = 2 := by decide
theorem construction_eighteen : ReverseAdjacency.constructionWork move vertices edges = 18 := by decide
theorem construction_bound_twenty : ReverseAdjacency.constructionWork move vertices edges ≤ 20 :=
  ReverseAdjacency.constructionWork_bound move vertices (by decide) edges (by decide)

theorem self_edge_once : ReverseAdjacency.build (fun (_ : Unit) => Move.node ()) [()] [()] () = [()] := by decide
theorem leaf_not_registered : ReverseAdjacency.build (fun (_ : Unit) => Move.leaf 20) [()] [()] () = [] := by decide

def diamond : ForwardInput QueueScanAccountingExamples.game QueueScanAccountingExamples.Edge where
  vertices := QueueScanAccountingExamples.context.vertices
  unique := QueueScanAccountingExamples.context.unique
  covered := QueueScanAccountingExamples.context.covered
  indexed := QueueScanAccountingExamples.indexed
  core := fun _ => false
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [QueueScanAccountingExamples.game]

theorem diamond_incoming_child : diamond.parents.incoming .child = [.leftChild, .rightChild] := by decide
theorem diamond_incoming_root : diamond.parents.incoming .root = [] := by decide
theorem diamond_construction_thirty_four : diamond.parentConstructionWork = 34 := by decide
theorem diamond_construction_bound : diamond.parentConstructionWork ≤ 36 := diamond.parentConstructionWork_bound

theorem diamond_generated_value : diamond.context.generatedPositiveValues .root = 20 := by
  change diamond.context.positiveStreamingValues QueueScanAccountingExamples.levels QueueScanAccountingExamples.valid .root = 20
  rw [diamond.context.positiveStreamingValues_eq _ _ (by decide)]
  decide

end PetaProof.ReverseAdjacencyExamples
