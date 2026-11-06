import PetaProof.ReverseOrderArray

/-!
末尾を上側とする有限配列と、先頭を上側とするリストとの対応。
末尾更新はサイズを変えず、手前の要素も変えない。反転リストは証明用である。
-/
namespace PetaProof.ArrayLifo

universe u
variable {α : Type u}

def model (array : Array α) : List α := array.toList.reverse
def replaceBack (array : Array α) (value : α) : Array α := array.setIfInBounds (array.size - 1) value

theorem model_empty : model (#[] : Array α) = [] := rfl
theorem model_length (array : Array α) : (model array).length = array.size := by simp [model]
theorem model_push (array : Array α) (value : α) : model (array.push value) = value :: model array := by
  simp [model, List.reverse_append]

theorem model_back (array : Array α) : (model array).head? = array.back? := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some value =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simp only [model_push, List.head?_cons, Array.back?_push]

theorem model_pop (array : Array α) : model array.pop = (model array).tail := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some value =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simp only [Array.pop_push, model_push, List.tail_cons]

theorem back_safe (array : Array α) (value : α) (found : array.back? = some value) :
    0 < array.size ∧ array.size - 1 < array.size := by
  obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp found
  subst array
  simp only [Array.size_push]
  omega

theorem replace_size (array : Array α) (value : α) : (replaceBack array value).size = array.size := by
  simp [replaceBack]

theorem replace_empty (value : α) : replaceBack #[] value = #[] := rfl

theorem replace_push (array : Array α) (old value : α) : replaceBack (array.push old) value = array.push value := by
  apply Array.ext_getElem?
  intro index
  by_cases same : index = array.size
  · subst index
    simp [replaceBack, Array.getElem?_setIfInBounds]
  · have different : array.size ≠ index := Ne.symm same
    simp [replaceBack, Array.getElem?_setIfInBounds, Array.getElem?_push, same, different]

theorem model_replace (array : Array α) (value : α) :
    model (replaceBack array value) = match model array with
      | [] => []
      | _ :: rest => value :: rest := by
  cases top : array.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst array
    rfl
  | some old =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst array
    simp only [replace_push, model_push]

theorem replace_checked (array : Array α) (old value : α) (found : array.back? = some old) :
    replaceBack array value = array.set (array.size - 1) value (back_safe array old found).2 := by
  exact dif_pos (back_safe array old found).2

/-- 末尾より手前の全フレームは同一のまま。親のフレームを破壊しない。 -/
theorem replace_prefix (array : Array α) (value : α) (index : Nat) (inside : index < array.size - 1) :
    (replaceBack array value)[index]? = array[index]? := by
  have different : array.size - 1 ≠ index := by omega
  simp [replaceBack, Array.getElem?_setIfInBounds, different]

end PetaProof.ArrayLifo
