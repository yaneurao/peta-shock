import PetaProof.ComponentResultArrayCore

/-!
UInt32配列を末尾が上のLIFOとして読む。Fin nへの復号は範囲検査を全域化するための仕様。
Validにより全要素の復号成功を保証し、本番に復号走査を追加しない。
-/
namespace PetaProof.VertexStack32

variable {n : Nat}

def encode (vertex : Fin n) : UInt32 := UInt32.ofNat vertex.val
def decode (n : Nat) (word : UInt32) : Option (Fin n) :=
  if valid : word.toNat < n then some ⟨word.toNat, valid⟩ else none
def Valid (n : Nat) (stack : Array UInt32) : Prop := ∀ word ∈ stack.toList, word.toNat < n
def model (n : Nat) (stack : Array UInt32) : List (Fin n) := stack.toList.reverse.filterMap (decode n)

theorem encode_toNat (fits : n ≤ UInt32.size) (vertex : Fin n) : (encode vertex).toNat = vertex.val :=
  UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le vertex.isLt fits)

theorem decode_encode (fits : n ≤ UInt32.size) (vertex : Fin n) : decode n (encode vertex) = some vertex := by
  simp only [decode, encode_toNat fits vertex]
  rw [dif_pos vertex.isLt]

theorem valid_empty (n : Nat) : Valid n #[] := by simp [Valid]

theorem valid_push_word (stack : Array UInt32) (valid : Valid n stack) (word : UInt32) (inside : word.toNat < n) :
    Valid n (stack.push word) := by
  intro other member
  simp only [Array.push_toList, List.mem_append, List.mem_singleton] at member
  rcases member with old | same
  · exact valid other old
  · simpa only [same] using inside

theorem valid_of_push (stack : Array UInt32) (word : UInt32) (valid : Valid n (stack.push word)) : Valid n stack := by
  intro other member
  exact valid other (by simpa only [Array.push_toList] using List.mem_append_left [word] member)

theorem valid_pop (stack : Array UInt32) (valid : Valid n stack) : Valid n stack.pop := by
  cases top : stack.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst stack
    exact valid_empty n
  | some word =>
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst stack
    simpa only [Array.pop_push] using valid_of_push rest word valid

theorem top_range (stack : Array UInt32) (valid : Valid n stack) (word : UInt32) (found : stack.back? = some word) : word.toNat < n := by
  obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp found
  subst stack
  exact valid word (by simp)

theorem top_safe (stack : Array UInt32) (word : UInt32) (found : stack.back? = some word) :
    0 < stack.size ∧ stack.size - 1 < stack.size := by
  obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp found
  subst stack
  simp only [Array.size_push]
  omega

theorem model_push_word (stack : Array UInt32) (word : UInt32) (inside : word.toNat < n) :
    model n (stack.push word) = (⟨word.toNat, inside⟩ : Fin n) :: model n stack := by
  simp [model, decode, inside, List.reverse_append]

theorem model_push (fits : n ≤ UInt32.size) (stack : Array UInt32) (vertex : Fin n) :
    model n (stack.push (encode vertex)) = vertex :: model n stack := by
  simp [model, List.reverse_append, decode_encode fits vertex]

theorem model_top (stack : Array UInt32) (valid : Valid n stack) :
    (model n stack).head? = stack.back?.bind (decode n) := by
  cases top : stack.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst stack
    simp [model]
  | some word =>
    have inside := top_range stack valid word top
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst stack
    simp only [model_push_word rest word inside, List.head?_cons, Array.back?_push, Option.bind_some,
      decode, dif_pos inside]
    change some (⟨word.toNat, inside⟩ : Fin n) = decode n word
    simp [decode, inside]

theorem model_pop (stack : Array UInt32) (valid : Valid n stack) : model n stack.pop = (model n stack).tail := by
  cases top : stack.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp top
    subst stack
    simp [model]
  | some word =>
    have inside := top_range stack valid word top
    obtain ⟨rest, same⟩ := Array.back?_eq_some_iff.mp top
    subst stack
    simp only [Array.pop_push, model_push_word rest word inside, List.tail_cons]

theorem list_length (words : List UInt32) (valid : ∀ word ∈ words, word.toNat < n) :
    (words.filterMap (decode n)).length = words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    have inside := valid word (by simp)
    have tail := ih (fun word member => valid word (by simp [member]))
    simp [decode, inside, tail]

/-- filterMapは要素を落とさない。長さと、復号成功列の等式の両方を示す。 -/
theorem model_length (stack : Array UInt32) (valid : Valid n stack) : (model n stack).length = stack.size := by
  rw [model, list_length _ (fun word member => valid word (List.mem_reverse.mp member))]
  simp

theorem decoded_all (stack : Array UInt32) (valid : Valid n stack) :
    stack.toList.reverse.map (decode n) = (model n stack).map some := by
  unfold model
  generalize words : stack.toList.reverse = input
  have bounded : ∀ word ∈ input, word.toNat < n := by
    intro word member
    rw [← words] at member
    exact valid word (List.mem_reverse.mp member)
  change input.map (decode n) = (input.filterMap (decode n)).map some
  clear words valid stack
  induction input with
  | nil => rfl
  | cons word rest ih =>
    have inside := bounded word (by simp)
    have tail := ih (fun word member => bounded word (by simp [member]))
    simp [decode, inside, tail]

end PetaProof.VertexStack32
