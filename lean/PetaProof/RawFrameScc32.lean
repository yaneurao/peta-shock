import PetaProof.ForwardDfsRaw32

/-!
生フレームの第一DFSを終了配列の直接逆順走査と第二DFSへ接続する。
入力はnone枠を保持した型付き出辺配列で、逆辺・フラグは既存モデルとの結果照合。
-/
namespace PetaProof.RawFrameScc32

open FrameCursor32 (Rows)
variable {n : Nat}

def labels (rows : Rows n) (parents : Fin n → List (Fin n)) : ComponentResultArray.State n :=
  ReverseOrderArray.run (ForwardDfsRaw32.finish rows (List.finRange n)).finished parents (ComponentResultArray.initial n)

theorem labels_exact (fits : n ≤ UInt32.size) (rows : Rows n) (counts : FrameCursor32.CountsFit rows)
    (parents : Fin n → List (Fin n)) :
    labels rows parents = FrameArrayScc.labels (ForwardDfsRaw32.outgoing rows) parents := by
  unfold labels FrameArrayScc.labels
  rw [ForwardDfsRaw32.finish_array_exact fits rows counts]

theorem computed_component_iff (fits : n ≤ ComponentLabels32.unset.toNat) (rows : Rows n)
    (counts : FrameCursor32.CountsFit rows) (parents : Fin n → List (Fin n))
    (transpose : ∀ child parent, parent ∈ parents child ↔ ForwardDfs.Edge (ForwardDfsRaw32.outgoing rows) parent child)
    (a b : Fin n) :
    ComponentResultArray.component (labels rows parents) a = ComponentResultArray.component (labels rows parents) b ↔
      ForwardDfs.Mutual (ForwardDfsRaw32.outgoing rows) a b := by
  rw [labels_exact (ComponentStackArray.word_capacity fits) rows counts]
  exact FrameArrayScc.computed_component_iff fits (ForwardDfsRaw32.outgoing rows) parents transpose a b

theorem outgoing_exact (rows : Rows n) :
    ForwardDfsRaw32.outgoing rows = SccIndexedView.outgoing (IndexedMoveRows.view rows) (fun _ => true) := by
  funext vertex
  simp only [SccIndexedView.outgoing, ↓reduceIte]
  exact (IndexedMoveRows.children_in_order rows vertex).symm

def parents (rows : Rows n) : Fin n → List (Fin n) :=
  SccIndexedView.parents (IndexedMoveRows.view rows) (List.finRange n) (fun _ => true)

theorem parents_transpose (rows : Rows n) (child parent : Fin n) :
    parent ∈ parents rows child ↔ ForwardDfs.Edge (ForwardDfsRaw32.outgoing rows) parent child := by
  rw [parents, SccIndexedView.parents_transpose (IndexedMoveRows.view rows) (List.finRange n)
    (CoreEnumeration.finRange_covers n) (fun _ => true), ← outgoing_exact]

def flags (rows : Rows n) : Array UInt8 :=
  (SccCycleArray.finish (IndexedMoveRows.view rows) (List.finRange n)
    (VertexStack32.model n (ForwardDfsRaw32.finish rows (List.finRange n)).finished) (fun _ => true)).flags

def core (rows : Rows n) : List (Fin n) := ComponentResultArray.extract (labels rows (parents rows)) (flags rows)

theorem flag_read_written (fits : n ≤ ComponentLabels32.unset.toNat) (rows : Rows n)
    (counts : FrameCursor32.CountsFit rows) (vertex : Fin n) :
    let report := SccCycleArray.finish (IndexedMoveRows.view rows) (List.finRange n)
      (VertexStack32.model n (ForwardDfsRaw32.finish rows (List.finRange n)).finished) (fun _ => true)
    (ComponentLabels32.get (labels rows (parents rows)).result vertex).toNat < report.number.roots.length ∧
      (ComponentLabels32.get (labels rows (parents rows)).result vertex).toNat < (flags rows).size := by
  dsimp only
  unfold flags parents
  rw [labels_exact (ComponentStackArray.word_capacity fits) rows counts,
    ForwardDfsRaw32.finish_array_exact (ComponentStackArray.word_capacity fits) rows counts, outgoing_exact]
  exact FrameArrayScc.flag_read_written fits (IndexedMoveRows.view rows) (fun _ => true) vertex

theorem core_correct (fits : n ≤ ComponentLabels32.unset.toNat) (rows : Rows n)
    (counts : FrameCursor32.CountsFit rows) (vertex : Fin n) :
    vertex ∈ core rows ↔ CyclicVertex (ForwardDfs.Edge (ForwardDfsRaw32.outgoing rows)) vertex := by
  unfold core flags parents
  rw [labels_exact (ComponentStackArray.word_capacity fits) rows counts,
    ForwardDfsRaw32.finish_array_exact (ComponentStackArray.word_capacity fits) rows counts, outgoing_exact]
  have correct := FrameArrayScc.core_correct fits (IndexedMoveRows.view rows) (fun _ => true) vertex
  dsimp only at correct
  have relation : SccIndexedView.relation (IndexedMoveRows.view rows) (fun _ => true) =
      ForwardDfs.Edge (SccIndexedView.outgoing (IndexedMoveRows.view rows) (fun _ => true)) := by
    funext a b
    exact propext (SccIndexedView.outgoing_correct (IndexedMoveRows.view rows) (fun _ => true) a b).symm
  rw [relation] at correct
  exact correct

end PetaProof.RawFrameScc32
