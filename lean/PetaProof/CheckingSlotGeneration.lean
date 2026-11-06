import PetaProof.ForwardDiscoveryCharge

/-! 正方向のDFS枠を未訪問発見時だけ生成し、全辺に対する変換・格納を会計へ加える。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (ctx : G.QueueContext E)

def slotProbe (vertex : V) : List (Option V) × Nat :=
  CountedRowOps.map (fun edge => if ctx.checkingAllow edge then
    (SccIndexedView.ofIndexed ctx.indexed).child edge else none) (ctx.indexed.outgoing vertex)

omit [DecidableEq V] [DecidableEq E] in
theorem slotProbe_spec (vertex : V) :
    (ctx.slotProbe vertex).1 = ctx.checkingOut vertex ∧
      (ctx.slotProbe vertex).2 = 2 * (ctx.indexed.outgoing vertex).length :=
  CountedRowOps.map_spec _ _

/-- seenの検査後にだけ一回生成し、その枠列を新しいフレームへ直接渡す。 -/
def discoverProbe (state : ForwardDfs.State V) (vertex : V) : ForwardDfs.State V × Nat :=
  if state.seen vertex then (state, 0) else
    let row := ctx.slotProbe vertex
    ({ state with seen := markSeen state.seen vertex
                  stack := ⟨vertex, row.1⟩ :: state.stack }, row.2)

omit [DecidableEq E] in
theorem discoverProbe_spec (state : ForwardDfs.State V) (vertex : V) :
    (ctx.discoverProbe state vertex).1 = ForwardDfs.discover ctx.checkingOut state vertex ∧
      (ctx.discoverProbe state vertex).2 =
        ForwardDiscoveryCharge.discoverCharge (fun vertex => (ctx.slotProbe vertex).2) state vertex := by
  cases seen : state.seen vertex <;>
    simp [discoverProbe, ForwardDfs.discover, ForwardDiscoveryCharge.discoverCharge,
      seen, (ctx.slotProbe_spec vertex).1]

def slotGenerationWork : Nat :=
  ForwardDiscoveryCharge.forestCharge ctx.vertices (fun vertex => (ctx.slotProbe vertex).2)
    ctx.checkingOut ctx.vertices ForwardDfs.initial

omit [DecidableEq E] in
theorem slotGenerationWork_eq : ctx.slotGenerationWork = 2 * ctx.allEdges.length := by
  rw [slotGenerationWork, ForwardDiscoveryCharge.finish_charge ctx.vertices ctx.unique ctx.covered _ _ _ ctx.covered]
  have same : ctx.vertices.map (fun vertex => (ctx.slotProbe vertex).2) =
      ctx.vertices.map (fun vertex => 2 * (ctx.indexed.outgoing vertex).length) :=
    List.map_congr_left (fun vertex _ => (ctx.slotProbe_spec vertex).2)
  have generic : ∀ selected : List V,
      (selected.map (fun vertex => 2 * (ctx.indexed.outgoing vertex).length)).sum =
        2 * (selected.map (fun vertex => (ctx.indexed.outgoing vertex).length)).sum := by
    intro selected
    induction selected with
    | nil => rfl
    | cons vertex rest ih =>
      simp only [List.map_cons, List.sum_cons] at *
      omega
  rw [same, generic]
  simp only [allEdges, List.length_flatMap]

def generatedDfsWork : Nat := ctx.storedDfsWork + ctx.slotGenerationWork

theorem generatedDfsWork_bound : ctx.generatedDfsWork ≤ 19 * ctx.vertices.length + 9 * ctx.allEdges.length := by
  have stored := ctx.storedDfsWork_bound
  unfold generatedDfsWork
  rw [ctx.slotGenerationWork_eq]
  omega

end PetaProof.ThresholdGame.QueueContext

namespace PetaProof.ThresholdGame.CoreGraphInput

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V} (input : CoreGraphInput G E)

def generatedMainWork : Nat :=
  input.forward.parentConstructionWork + input.prepared.1.generatedWork input.prepared.2 +
    input.prepared.1.generatedDfsWork + (input.prepared.1.opposite input.prepared.2).generatedDfsWork

theorem generatedMainWork_bound : input.generatedMainWork ≤
    57 * input.vertices.length + 48 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels := by
  have construction := input.forward.parentConstructionWork_bound
  have main := input.prepared.1.generatedWork_bound input.prepared.2
  have first := input.prepared.1.generatedDfsWork_bound
  have other := (input.prepared.1.opposite input.prepared.2).generatedDfsWork_bound
  change input.forward.parentConstructionWork ≤ 4 * input.vertices.length + 4 * input.forward.allEdges.length at construction
  change input.prepared.1.generatedWork input.prepared.2 ≤
    15 * input.vertices.length + 26 * input.forward.allEdges.length + 42 * (G.mate.toNat + 1) +
      input.prepared.1.localTerm input.prepared.1.generatedLevels +
      (input.prepared.1.opposite input.prepared.2).localTerm
        (input.prepared.1.opposite input.prepared.2).generatedLevels at main
  change input.prepared.1.generatedDfsWork ≤ 19 * input.vertices.length + 9 * input.forward.allEdges.length at first
  change (input.prepared.1.opposite input.prepared.2).generatedDfsWork ≤
    19 * input.vertices.length + 9 * input.forward.allEdges.length at other
  unfold generatedMainWork
  omega

theorem rows_and_generated_work (leaves : G.BoundedLeaves) :
    (∀ row ∈ input.valueRows, G.ExactValue row.1 row.2) ∧
      input.generatedMainWork ≤ 57 * input.vertices.length + 48 * input.forward.allEdges.length +
        42 * (G.mate.toNat + 1) + input.prepared.1.localTerm input.prepared.1.generatedLevels +
        (input.prepared.1.opposite input.prepared.2).localTerm
          (input.prepared.1.opposite input.prepared.2).generatedLevels :=
  ⟨input.valueRows_exact leaves, input.generatedMainWork_bound⟩

end PetaProof.ThresholdGame.CoreGraphInput
