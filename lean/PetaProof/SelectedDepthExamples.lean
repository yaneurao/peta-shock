import PetaProof.SelectedDepthWriter

/-! leaf、循環、循環への前置経路、長い有限経路、再合流を含む再構築の例。 -/
namespace PetaProof.SelectedDepthExamples

def next (vertex : Fin 6) : Option (Fin 6) :=
  if vertex = 0 then some 1 else if vertex = 1 then none
  else if vertex = 2 then some 3 else if vertex = 3 then some 2
  else if vertex = 4 then some 2 else some 0

def vertices : List (Fin 6) := [0, 1, 2, 3, 4, 5]

theorem covered (vertex : Fin 6) : vertex ∈ vertices := by
  have cases : vertex = 0 ∨ vertex = 1 ∨ vertex = 2 ∨ vertex = 3 ∨ vertex = 4 ∨ vertex = 5 := by
    have bound := vertex.isLt
    omega
  simpa [vertices] using cases

theorem leaf_depth :
    (SelectedDepth.reconstruct next 9999 vertices).map (fun table => table 1) = some 0 := by decide

theorem one_step_depth :
    (SelectedDepth.reconstruct next 9999 vertices).map (fun table => table 0) = some 1 := by decide

theorem cycle_depth :
    (SelectedDepth.reconstruct next 9999 vertices).map (fun table => table 2) = some 9999 := by decide

theorem reaches_cycle_depth :
    (SelectedDepth.reconstruct next 9999 vertices).map (fun table => table 4) = some 9999 := by decide

theorem rejoined_finite_depth :
    (SelectedDepth.reconstruct next 9999 vertices).map (fun table => table 5) = some 2 := by decide

theorem long_finite_saturates :
    (SelectedDepth.reconstruct next 1 vertices).map (fun table => table 5) = some 1 := by decide

theorem zero_cap :
    (SelectedDepth.reconstruct next 0 vertices).map (fun table => table 5) = some 0 := by decide

theorem root_order_preserves_table :
    SelectedDepth.reconstruct next 9999 vertices.reverse =
      SelectedDepth.reconstruct next 9999 vertices := by
  rw [SelectedDepth.reconstruct_exact next 9999 vertices covered,
    SelectedDepth.reconstruct_exact next 9999 vertices.reverse (by intro vertex; simpa using covered vertex)]

end PetaProof.SelectedDepthExamples
