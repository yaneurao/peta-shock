import PetaProof.ComponentResultArray

/-!
実際のUInt32ラベルをUInt8循環フラグ配列の添字として読む。
番号表モデルとフラグ表モデルの対応を照合する接続であり、両配列を含む単一C++実行の精密化ではない。
-/
namespace PetaProof.ComponentResultArray

variable {n : Nat} {E : Type}

def keepWithFlags (state : State n) (flags : Array UInt8) (vertex : Fin n) : Bool :=
  (flags[(ComponentLabels32.get state.result vertex).toNat]?.getD 0) != 0

theorem keepWithFlags_exact (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (order : List (Fin n)) (covered : ∀ vertex, vertex ∈ order) (allow : E → Bool) (vertex : Fin n) :
    keepWithFlags (finish (SccIndexedView.parents view (List.finRange n) allow) order)
      (SccCycleArray.finish view (List.finRange n) order allow).flags vertex =
        SccCycleArray.keep (SccCycleArray.finish view (List.finRange n) order allow) vertex := by
  have raw := final_labels fits (SccIndexedView.parents view (List.finRange n) allow) order covered vertex
  dsimp only at raw
  simp only [keepWithFlags, raw.2.1, component_exact fits, SccCycleArray.keep, SccCycleArray.component_exact]

/-- 実ラベルの値を添字にしても、配列内かつ書込済みprefix内に入る。 -/
theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (order : List (Fin n)) (covered : ∀ vertex, vertex ∈ order) (allow : E → Bool) (vertex : Fin n) :
    let labels := finish (SccIndexedView.parents view (List.finRange n) allow) order
    let flags := SccCycleArray.finish view (List.finRange n) order allow
    (ComponentLabels32.get labels.result vertex).toNat < flags.number.roots.length ∧
      (ComponentLabels32.get labels.result vertex).toNat < flags.flags.size := by
  have raw := final_labels fits (SccIndexedView.parents view (List.finRange n) allow) order covered vertex
  dsimp only at raw
  have written := SccCycleArray.read_written view (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) order covered allow vertex
  simp only [raw.2.1, component_exact fits]
  simpa only [SccCycleArray.component_exact] using And.intro written.1 written.2.1

theorem keepWithFlags_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let order := ForwardDfs.order (List.finRange n) (List.finRange n) (SccIndexedView.outgoing view allow)
    keepWithFlags (finish (SccIndexedView.parents view (List.finRange n) allow) order)
      (SccCycleArray.finish view (List.finRange n) order allow).flags vertex = true ↔
        CyclicVertex (SccIndexedView.relation view allow) vertex := by
  have covered := ForwardDfs.order_covers (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) (List.finRange n) (CoreEnumeration.finRange_covers n) (SccIndexedView.outgoing view allow)
  dsimp only
  rw [keepWithFlags_exact fits view _ covered allow vertex]
  have correct := SccCycleArray.core_correct view (List.finRange n) (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) (List.finRange n) (CoreEnumeration.finRange_covers n) allow vertex
  simpa only [SccCycleArray.core, CoreEnumeration.mem_core, CoreEnumeration.finRange_covers, true_and] using correct

def extract (state : State n) (flags : Array UInt8) : List (Fin n) :=
  CoreEnumeration.core (keepWithFlags state flags) (List.finRange n)

theorem extract_correct (fits : n ≤ ComponentLabels32.unset.toNat) (view : SccIndexedView.View (Fin n) E)
    (allow : E → Bool) (vertex : Fin n) :
    let order := ForwardDfs.order (List.finRange n) (List.finRange n) (SccIndexedView.outgoing view allow)
    vertex ∈ extract (finish (SccIndexedView.parents view (List.finRange n) allow) order)
      (SccCycleArray.finish view (List.finRange n) order allow).flags ↔
        CyclicVertex (SccIndexedView.relation view allow) vertex := by
  simp only [extract, CoreEnumeration.mem_core, CoreEnumeration.finRange_covers, true_and]
  exact keepWithFlags_correct fits view allow vertex

end PetaProof.ComponentResultArray
