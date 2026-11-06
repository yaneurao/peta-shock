import PetaProof.SccSelfLoop
import PetaProof.CertifiedPropagationExamples

namespace PetaProof.ComponentCycleExamples

inductive Vertex where
  | a | b | isolated | self
  deriving DecidableEq

def vertices : List Vertex := [.a, .b, .isolated, .self]
def edge (source target : Vertex) : Prop :=
  (source = .a ∧ target = .b) ∨ (source = .b ∧ target = .a) ∨ (source = .self ∧ target = .self)
def component : Vertex → Nat
  | .a | .b => 0
  | .isolated => 1
  | .self => 2

def partition : SccPartition edge := {
  component := component
  ordered := by intro source target legal; cases source <;> cases target <;> simp_all [edge, component]
  connected := by
    intro source target same
    cases source <;> cases target <;> simp_all [component]
    all_goals first
      | exact ⟨Walk.nil _⟩
      | exact ⟨Walk.cons (by simp [edge]) (Walk.nil _)⟩
}

def selfLoop (vertex : Vertex) : Bool := vertex == .self

theorem self_correct (vertex : Vertex) : selfLoop vertex = true ↔ edge vertex vertex := by
  cases vertex <;> simp [selfLoop, edge]

def extracted := CoreEnumeration.core (ComponentCycleFlags.keep vertices component selfLoop) vertices

theorem includes_two_cycle_and_self : extracted = [.a, .b, .self] := by decide
theorem isolated_rejected : Vertex.isolated ∉ extracted := by decide
theorem singleton_self_flag : ComponentCycleFlags.flag vertices component selfLoop 2 = true := by decide
theorem singleton_without_self_flag : ComponentCycleFlags.flag vertices component selfLoop 1 = false := by decide

theorem extracted_correct (vertex : Vertex) : vertex ∈ extracted ↔ CyclicVertex edge vertex :=
  ComponentCycleFlags.extracted_core_iff vertices (by decide)
    (by intro v; cases v <;> simp [vertices]) partition (by intro v; cases v <;> decide) selfLoop self_correct vertex

-- 頂点列に重複を許すと、同じ孤立頂点を二つの頂点と誤認する。Nodup前提は必要。
theorem duplicate_fakes_size : ComponentCycleFlags.flag [.isolated, .isolated] component selfLoop 1 = true := by decide
theorem isolated_not_cyclic : ¬ CyclicVertex edge Vertex.isolated := by
  rintro ⟨other, step, _⟩
  cases other <;> simp [edge] at step

open PropagationExamples (loopGame)
open CertifiedPropagationExamples (loopIndexed)

def loopRelation := SccSelfLoop.relation loopIndexed (fun _ => true)
def loopPartition : SccPartition loopRelation := {
  component := fun _ => 0
  ordered := by intros; exact Nat.le_refl _
  connected := by
    intro a b _
    cases a <;> cases b
    all_goals first
      | exact ⟨Walk.nil _⟩
      | exact ⟨Walk.cons (by simp [loopRelation, SccSelfLoop.relation, loopIndexed]) (Walk.nil _)⟩
}

def loopVertices : List Bool := [false, true]
def loopSelf := SccSelfLoop.fromParents loopIndexed (fun _ => true) (SccSelfLoop.parents loopIndexed loopVertices)
def loopCore := CoreEnumeration.core (ComponentCycleFlags.keep loopVertices loopPartition.component loopSelf) loopVertices

theorem loop_reverse_self_flags : loopSelf false = false ∧ loopSelf true = false := by decide
theorem loop_core_survives_without_self_edges : loopCore = [false, true] := by decide
theorem loop_core_correct (vertex : Bool) : vertex ∈ loopCore ↔ CyclicVertex loopRelation vertex :=
  SccSelfLoop.extracted_core loopIndexed (fun _ => true) loopVertices (by decide)
    (by intro v; cases v <;> simp [loopVertices]) loopPartition (by intro v; cases v <;> decide) vertex

def sparseKeep (vertex : Fin 5) : Bool := vertex.val == 1 || vertex.val == 4
def sparseCore := CoreEnumeration.finiteCore 5 sparseKeep

theorem sparse_ids : sparseCore.map Fin.val = [1, 4] := by decide
theorem sparse_local_indices : (LocalIndex.registered32 sparseCore 1).toInt = 0 ∧
    (LocalIndex.registered32 sparseCore 4).toInt = 1 := by decide
theorem sparse_access :
    let index := (LocalIndex.registered32 sparseCore 4).toUInt32.toNat
    index < sparseCore.length ∧ sparseCore[index]? = some 4 :=
  CoreEnumeration.finiteCore_local_access 5 (by decide) sparseKeep 4 (by decide)

theorem empty_enumeration : CoreEnumeration.finiteCore 0 (fun _ => true) = [] := rfl

end PetaProof.ComponentCycleExamples
