import PetaProof.TurnSharedScc

/-!
局面ごとの有限な指し手配列から、辺ID=(局面番号,配列内番号)を生成する。
所有条件を入力せず列挙から導く。生の数値対は範囲検査後にだけ型付きIDへ戻す。
-/
namespace PetaProof.IndexedMoveRows

variable {n : Nat}

abbrev Rows (n : Nat) := Fin n → Array (Option (Fin n))
abbrev Edge (rows : Rows n) := (vertex : Fin n) × Fin (rows vertex).size
abbrev Raw := Nat × Nat

def encode (rows : Rows n) (edge : Edge rows) : Raw := (edge.1.val, edge.2.val)

def decode (rows : Rows n) (raw : Raw) : Option (Edge rows) :=
  if vertex_ok : raw.1 < n then
    let vertex : Fin n := ⟨raw.1, vertex_ok⟩
    if move_ok : raw.2 < (rows vertex).size then some ⟨vertex, ⟨raw.2, move_ok⟩⟩ else none
  else none

theorem decode_encode (rows : Rows n) (edge : Edge rows) : decode rows (encode rows edge) = some edge := by
  rcases edge with ⟨vertex, move⟩
  simp [decode, encode, vertex.isLt, move.isLt]

theorem encode_injective (rows : Rows n) {a b : Edge rows} (same : encode rows a = encode rows b) : a = b := by
  have decoded := congrArg (decode rows) same
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

def view (rows : Rows n) : SccIndexedView.View (Fin n) (Edge rows) where
  outgoing := fun vertex => (List.finRange (rows vertex).size).map (fun move => ⟨vertex, move⟩)
  source := fun edge => edge.1
  child := fun edge => (rows edge.1)[edge.2.val]'edge.2.isLt
  at_source := by
    rintro ⟨vertex, move⟩
    exact List.mem_map.mpr ⟨move, CoreEnumeration.finRange_covers _ move, rfl⟩
  source_of_mem := by
    intro vertex edge member
    obtain ⟨move, _, same⟩ := List.mem_map.mp member
    have owner := congrArg Sigma.fst same
    exact owner.symm

theorem degree (rows : Rows n) (vertex : Fin n) : ((view rows).outgoing vertex).length = (rows vertex).size := by
  simp [view]

/-- 列挙した辺の子を順番に読むと元の指し手配列になる。leafのnoneも落とさない。 -/
theorem children_in_order (rows : Rows n) (vertex : Fin n) :
    ((view rows).outgoing vertex).map (view rows).child = (rows vertex).toList := by
  apply List.ext_getElem
  · simp [view]
  · intro index left right
    simp [view, List.getElem_finRange]

theorem edge_at (rows : Rows n) (vertex : Fin n) (move : Fin (rows vertex).size) :
    (⟨vertex, move⟩ : Edge rows) ∈ (view rows).outgoing vertex :=
  List.mem_map.mpr ⟨move, CoreEnumeration.finRange_covers _ move, rfl⟩

/-- 生の番号が範囲内なら、decodeして得るIDの数値対は元と一致する。 -/
theorem encode_decoded (rows : Rows n) (raw : Raw) (edge : Edge rows)
    (found : decode rows raw = some edge) : encode rows edge = raw := by
  unfold decode at found
  split at found
  · dsimp only at found
    split at found
    · have same := Option.some.inj found
      subst edge
      rfl
    · cases found
  · cases found

end PetaProof.IndexedMoveRows
