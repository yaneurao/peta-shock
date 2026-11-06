import PetaProof.SeenArrayScc

/-!
第一DFSの終了列をUInt32配列へ保存する。通常順と逆順の復号を区別する。
復号列は仕様用であり、配列を走査する本番コードに別の列を追加しない。
-/
namespace PetaProof.FinishingArray32

variable {n : Nat}

def model (n : Nat) (array : Array UInt32) : List (Fin n) := array.toList.filterMap (VertexStack32.decode n)

theorem reverse_model (array : Array UInt32) : VertexStack32.model n array = (model n array).reverse := by
  simp only [VertexStack32.model, model, List.filterMap_reverse]

theorem model_empty (n : Nat) : model n #[] = [] := rfl

theorem model_push (fits : n ≤ UInt32.size) (array : Array UInt32) (vertex : Fin n) :
    model n (array.push (VertexStack32.encode vertex)) = model n array ++ [vertex] := by
  simp [model, VertexStack32.decode_encode fits vertex]

theorem model_length (array : Array UInt32) (valid : VertexStack32.Valid n array) : (model n array).length = array.size := by
  have length := VertexStack32.model_length array valid
  simpa only [reverse_model, List.length_reverse] using length

theorem decoded_all (array : Array UInt32) (valid : VertexStack32.Valid n array) :
    array.toList.map (VertexStack32.decode n) = (model n array).map some := by
  have all := congrArg List.reverse (VertexStack32.decoded_all array valid)
  simpa only [reverse_model, List.map_reverse, List.reverse_reverse] using all

theorem encode_injective (fits : n ≤ UInt32.size) {a b : Fin n} : VertexStack32.encode a = VertexStack32.encode b → a = b := by
  intro same
  have values := congrArg UInt32.toNat same
  simp only [VertexStack32.encode_toNat fits] at values
  exact Fin.ext values

/-- 復号後に元のUInt32列へ戻せるので、表現変換が格納値を変えない。 -/
theorem reencode (array : Array UInt32) (valid : VertexStack32.Valid n array) :
    (model n array).map VertexStack32.encode = array.toList := by
  unfold model
  generalize words : array.toList = input
  have bounded : ∀ word ∈ input, word.toNat < n := by
    intro word member
    rw [← words] at member
    exact valid word member
  clear words valid array
  induction input with
  | nil => rfl
  | cons word rest ih =>
    have inside := bounded word (by simp)
    have tail := ih (fun word member => bounded word (by simp [member]))
    simp [VertexStack32.decode, inside, VertexStack32.encode, tail]

/-- 任意の実読出しが成功し、復号で頂点を捨てないことの局所版。 -/
theorem read_success (array : Array UInt32) (valid : VertexStack32.Valid n array)
    (index : Nat) (inside : index < array.size) :
    ∃ vertex : Fin n, array[index]?.bind (VertexStack32.decode n) = some vertex ∧
      vertex.val = array[index].toNat := by
  have member : array[index] ∈ array.toList := by
    exact List.getElem_mem inside
  have bounded := valid _ member
  refine ⟨⟨array[index].toNat, bounded⟩, ?_, rfl⟩
  simp [inside, VertexStack32.decode, bounded]

end PetaProof.FinishingArray32
