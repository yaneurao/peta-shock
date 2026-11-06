import PetaProof.TurnEncoding32

/-!
leafタグとUInt32のnextから子番号配列を作り、機械式の許可辺とSCC/coreへ接続する。
leafのunion領域をnextとして読まないことを、別のコンストラクタで表現する。
入力内部辺のnext<nは明示的な前提であり、本番ローダーが検証済みだとは主張しない。
-/
namespace PetaProof.MoveRows32

open TurnEncoding (State)
variable {n : Nat}

inductive Move where
  | leaf
  | internal (next : UInt32)
  deriving DecidableEq

def MoveValid (n : Nat) : Move → Prop
  | .leaf => True
  | .internal next => next.toNat < n

instance (n : Nat) (move : Move) : Decidable (MoveValid n move) := by
  cases move <;> unfold MoveValid <;> infer_instance

def child (n : Nat) : Move → Option (Fin n)
  | .leaf => none
  | .internal next => if valid : next.toNat < n then some ⟨next.toNat, valid⟩ else none

/-- 本番はleafなら番兵を返し、内部手だけnextを展開する。 -/
def child32 (move : Move) (index : UInt32) : UInt32 :=
  match move with
  | .leaf => TurnEncoding32.none
  | .internal next => TurnEncoding32.flipIndex next index

theorem sentinel_iff_leaf (fits : TurnEncoding32.Fits n) (move : Move) (valid : MoveValid n move) (index : UInt32) :
    child32 move index = TurnEncoding32.none ↔ move = .leaf := by
  cases move with
  | leaf => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | internal next =>
    constructor
    · intro impossible
      exact False.elim (TurnEncoding32.flipIndex_ne_none fits next valid index impossible)
    · intro impossible
      cases impossible

theorem child_refines (fits : TurnEncoding32.Fits n) (move : Move) (valid : MoveValid n move) (state : State n) :
    TurnEncoding32.decode n (child32 move (TurnEncoding32.encode state)) =
      (child n move).map (fun vertex => (vertex, !state.2)) := by
  cases move with
  | leaf => exact TurnEncoding32.decode_none fits
  | internal next =>
    change next.toNat < n at valid
    have expanded := TurnEncoding32.flipIndex_encode fits (⟨next.toNat, valid⟩ : Fin n) state
    simp only [UInt32.ofNat_toNat] at expanded
    simp only [child32, expanded, TurnEncoding32.decode_encode fits, child, dif_pos valid, Option.map]

theorem child_eq_encode_iff (fits : TurnEncoding32.Fits n) (move : Move) (valid : MoveValid n move)
    (state target : State n) :
    child32 move (TurnEncoding32.encode state) = TurnEncoding32.encode target ↔
      (child n move).map (fun vertex => (vertex, !state.2)) = some target := by
  cases move with
  | leaf =>
    change TurnEncoding32.none = TurnEncoding32.encode target ↔ Option.none = some target
    constructor
    · intro same
      exact False.elim (TurnEncoding32.encode_ne_none fits target same.symm)
    · intro impossible
      cases impossible
  | internal next =>
    change next.toNat < n at valid
    have expanded := TurnEncoding32.flipIndex_encode fits (⟨next.toNat, valid⟩ : Fin n) state
    simp only [UInt32.ofNat_toNat] at expanded
    simp only [child32, expanded, child, dif_pos valid, Option.map, Option.some.injEq]
    exact ⟨TurnEncoding32.encode_injective fits, congrArg TurnEncoding32.encode⟩

abbrev Book (n : Nat) := Fin n → Array Move
def Valid (book : Book n) : Prop := ∀ vertex (move : Fin (book vertex).size), MoveValid n (book vertex)[move.val]
def CountsFit (book : Book n) : Prop := ∀ vertex, (book vertex).size < UInt32.size
def rows (book : Book n) : IndexedMoveRows.Rows n := fun vertex => (book vertex).map (child n)

theorem row_size (book : Book n) (vertex : Fin n) : (rows book vertex).size = (book vertex).size := by
  simp [rows]

/-- childはleaf位置も残すので、元配列と変換後配列の指し手番号は同じ。 -/
theorem row_get (book : Book n) (vertex : Fin n) (move : Nat) (inside : move < (book vertex).size) :
    (rows book vertex)[move]'(by simpa [rows] using inside) = child n (book vertex)[move] := by
  simp [rows]

theorem degree_cast (book : Book n) (counts : CountsFit book) (vertex : Fin n) :
    (UInt32.ofNat (book vertex).size).toNat = (rows book vertex).size := by
  rw [row_size]
  exact UInt32.toNat_ofNat_of_lt' (counts vertex)

theorem move_cast (book : Book n) (counts : CountsFit book) (vertex : Fin n) (move : Fin (book vertex).size) :
    (UInt32.ofNat move.val).toNat = move.val :=
  UInt32.toNat_ofNat_of_lt' (Nat.lt_trans move.isLt (counts vertex))

def edge32 (book : Book n) (edge : IndexedMoveRows.Edge (rows book)) : UInt32 × UInt32 :=
  (UInt32.ofNat edge.1.val, UInt32.ofNat edge.2.val)

/-- CSRの(v,j)をそれぞれUInt32へ写して戻しても番号は変わらない。 -/
theorem edge32_decodes (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (edge : IndexedMoveRows.Edge (rows book)) :
    ((edge32 book edge).1.toNat, (edge32 book edge).2.toNat) = IndexedMoveRows.encode (rows book) edge := by
  have limit := TurnEncoding32.fits_bound fits
  have vertex_small : edge.1.val < UInt32.size := by
    have bound := edge.1.isLt
    change edge.1.val < 4294967296
    omega
  have move_small : edge.2.val < UInt32.size := by
    have bound := Nat.lt_of_lt_of_le edge.2.isLt (Nat.le_of_eq (row_size book edge.1))
    exact Nat.lt_trans bound (counts edge.1)
  simp only [edge32, IndexedMoveRows.encode, UInt32.toNat_ofNat_of_lt' vertex_small,
    UInt32.toNat_ofNat_of_lt' move_small]

def allowNat (allow : UInt32 → UInt32 → Bool) (parent move : Nat) : Bool :=
  allow (UInt32.ofNat parent) (UInt32.ofNat move)

/-- 実際のUInt32子番号と、親番号・元のjを使う許可判定で定めた辺。 -/
def relation (book : Book n) (allow : UInt32 → UInt32 → Bool) (a b : State n) : Prop :=
  ∃ move : Fin (book a.1).size,
    child32 (book a.1)[move.val] (TurnEncoding32.encode a) = TurnEncoding32.encode b ∧
      allow (TurnEncoding32.encode a) (UInt32.ofNat move.val) = true

theorem relation_exact (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book)
    (allow : UInt32 → UInt32 → Bool) (a b : State n) :
    relation book allow a b ↔
      SccIndexedView.relation (TurnSharedGraph.expanded (IndexedMoveRows.view (rows book)))
        (MoveRowsScc.allowAt (rows book) (allowNat allow)) a b := by
  rw [← SccIndexedView.outgoing_correct, MoveRowsScc.forward_meaning]
  constructor
  · rintro ⟨move, found, permitted⟩
    have decoded := (child_eq_encode_iff fits _ (valid a.1 move) a b).mp found
    have parts : child n (book a.1)[move.val] = some b.1 ∧ b.2 = (!a.2) := by
      cases result : child n (book a.1)[move.val] with
      | none => simp [result] at decoded
      | some vertex =>
        rw [result] at decoded
        change some (vertex, !a.2) = some b at decoded
        have pair := Option.some.inj decoded
        exact ⟨congrArg some (congrArg Prod.fst pair), (congrArg Prod.snd pair).symm⟩
    exact ⟨⟨move.val, by simp [rows]⟩, by simpa [rows] using parts.1, parts.2, permitted⟩
  · rintro ⟨move, found, sides, permitted⟩
    let original : Fin (book a.1).size := ⟨move.val, by simpa [rows] using move.isLt⟩
    refine ⟨original, (child_eq_encode_iff fits _ (valid a.1 original) a b).mpr ?_, permitted⟩
    have child_found : child n (book a.1)[original.val] = some b.1 := by
      simpa [rows, original] using found
    rw [child_found]
    simp only [Option.map]
    exact congrArg some (Prod.ext rfl sides.symm)

def core (book : Book n) (seed : IndexedMoveRows.Raw) (allow : UInt32 → UInt32 → Bool) : List (State n) :=
  MoveRowsScc.core (rows book) seed (allowNat allow)

theorem core_correct (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book)
    (seed : IndexedMoveRows.Raw) (allow : UInt32 → UInt32 → Bool) (state : State n) :
    state ∈ core book seed allow ↔ CyclicVertex (relation book allow) state := by
  have same : relation book allow = SccIndexedView.relation
      (TurnSharedGraph.expanded (IndexedMoveRows.view (rows book)))
      (MoveRowsScc.allowAt (rows book) (allowNat allow)) := by
    funext a b
    exact propext (relation_exact fits book valid allow a b)
  rw [same]
  exact MoveRowsScc.core_correct (rows book) seed (allowNat allow) state

/-- 基礎CSRの親番号に反転手番を付け、元のjとともにcallbackへ渡す列。 -/
def callbacks32 (book : Book n) (seed : IndexedMoveRows.Raw) (state : State n) : List (UInt32 × UInt32) :=
  (MoveRowsCsr.incoming (rows book) seed state.1).map (fun edge =>
    (TurnEncoding32.flipIndex (UInt32.ofNat edge.1.val) (TurnEncoding32.encode state), UInt32.ofNat edge.2.val))

def parents32 (book : Book n) (seed : IndexedMoveRows.Raw) (allow : UInt32 → UInt32 → Bool)
    (state : State n) : List UInt32 :=
  ((callbacks32 book seed state).filter (fun edge => allow edge.1 edge.2)).map Prod.fst

/-- 順序・重複回数を含め、機械式callbackの親列は型付き親列のencodeに一致する。 -/
theorem parents32_exact (fits : TurnEncoding32.Fits n) (book : Book n) (seed : IndexedMoveRows.Raw)
    (allow : UInt32 → UInt32 → Bool) (state : State n) :
    parents32 book seed allow state =
      (MoveRowsScc.parents (rows book) seed (allowNat allow) state).map TurnEncoding32.encode := by
  unfold parents32 callbacks32 MoveRowsScc.parents MoveRowsScc.incoming
  simp only [List.filter_map, List.map_map, Function.comp_def]
  simp only [TurnEncoding32.flipIndex_encode fits]
  rfl

theorem parents32_transpose (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book)
    (seed : IndexedMoveRows.Raw) (allow : UInt32 → UInt32 → Bool) (parent target : State n) :
    TurnEncoding32.encode parent ∈ parents32 book seed allow target ↔ relation book allow parent target := by
  have machine : parent ∈ MoveRowsScc.parents (rows book) seed (allowNat allow) target ↔
      relation book allow parent target := by
    rw [MoveRowsScc.parents_transpose, SccIndexedView.outgoing_correct,
      ← relation_exact fits book valid allow parent target]
  rw [parents32_exact fits, List.mem_map]
  constructor
  · rintro ⟨original, present, same⟩
    have equal := TurnEncoding32.encode_injective fits same
    subst original
    exact machine.mp present
  · intro present
    exact ⟨parent, machine.mpr present, rfl⟩

end PetaProof.MoveRows32
