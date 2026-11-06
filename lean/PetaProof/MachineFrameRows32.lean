import PetaProof.RawFrameScc32

/-!
元の定跡配列のchild/allowを、生UInt32フレームが読む出辺枠へ接続する。
rowsは証明上の配列であり、本番に配列コピーや事前のフィルタ走査を追加しない。
-/
namespace PetaProof.MachineFrameRows32

variable {n : Nat}

/-- leafではallowを呼ばない。不許可手もnoneという枠を一つ残す。 -/
def slot (book : MoveRows32.Book n) (allow : UInt32 → UInt32 → Bool)
    (source : TurnEncoding.State n) (move : Fin (book source.1).size) : Option (Fin (2 * n)) :=
  let child := MoveRows32.child32 (book source.1)[move.val] (TurnEncoding32.encode source)
  if child = TurnEncoding32.none then none
  else if allow (TurnEncoding32.encode source) (UInt32.ofNat move.val) then
    (TurnEncoding32.decode n child).map TurnEncoding.encode
  else none

/-- 生の親番号と元のjによる読取り。範囲外分岐は仕様の全域化のためだけにある。 -/
def query (book : MoveRows32.Book n) (allow : UInt32 → UInt32 → Bool)
    (parent move : UInt32) : Option (Fin (2 * n)) :=
  match TurnEncoding32.decode n parent with
  | none => none
  | some source =>
    if inside : move.toNat < (book source.1).size then
      slot book allow source ⟨move.toNat, inside⟩
    else none

def rows (book : MoveRows32.Book n) (allow : UInt32 → UInt32 → Bool) : FrameCursor32.Rows (2 * n) :=
  fun vertex => Array.ofFn (slot book allow (TurnEncoding.decode vertex))

theorem row_size (book : MoveRows32.Book n) (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    (rows book allow vertex).size = (book (TurnEncoding.decode vertex).1).size := by
  simp [rows]

theorem counts_fit (book : MoveRows32.Book n) (counts : MoveRows32.CountsFit book)
    (allow : UInt32 → UInt32 → Bool) : FrameCursor32.CountsFit (rows book allow) := by
  intro vertex
  rw [row_size]
  exact counts _

theorem parent_word (vertex : Fin (2 * n)) :
    TurnEncoding32.encode (TurnEncoding.decode vertex) = VertexStack32.encode vertex := by
  unfold TurnEncoding32.encode VertexStack32.encode
  rw [TurnEncoding.encode_decode]

theorem query_slot (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (allow : UInt32 → UInt32 → Bool)
    (source : TurnEncoding.State n) (move : Fin (book source.1).size) :
    query book allow (TurnEncoding32.encode source) (UInt32.ofNat move.val) = slot book allow source move := by
  simp only [query, TurnEncoding32.decode_encode fits, MoveRows32.move_cast book counts source.1 move,
    dif_pos move.isLt]

/-- 次数まで達していない有効フレームは、元配列でも同じjの有効な指し手を指す。 -/
theorem source_read_safe (book : MoveRows32.Book n) (counts : MoveRows32.CountsFit book)
    (allow : UInt32 → UInt32 → Bool) (frame : FrameCursor32.Frame)
    (valid : FrameCursor32.Valid (rows book allow) frame)
    (running : frame.2 ≠ FrameCursor32.degree (rows book allow) frame valid) :
    frame.2.toNat < (book (TurnEncoding.decode (FrameCursor32.view (rows book allow) frame valid).vertex).1).size := by
  have inside := FrameCursor32.before_end (rows book allow) (counts_fit book counts allow) frame valid running
  simpa only [row_size] using inside

/-- フレームの旧jで読む子は、元配列に対する機械式child/allow問合せと一致する。 -/
theorem target_query (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (allow : UInt32 → UInt32 → Bool)
    (frame : FrameCursor32.Frame) (valid : FrameCursor32.Valid (rows book allow) frame)
    (running : frame.2 ≠ FrameCursor32.degree (rows book allow) frame valid) :
    FrameCursor32.target (rows book allow) frame valid = query book allow frame.1 frame.2 := by
  let vertex := (FrameCursor32.view (rows book allow) frame valid).vertex
  let move : Fin (book (TurnEncoding.decode vertex).1).size :=
    ⟨frame.2.toNat, source_read_safe book counts allow frame valid running⟩
  have parent : TurnEncoding32.encode (TurnEncoding.decode vertex) = frame.1 :=
    (parent_word vertex).trans (FrameCursor32.view_vertex_word _ frame valid)
  have same := query_slot fits book counts allow (TurnEncoding.decode vertex) move
  simp only [move, UInt32.ofNat_toNat, parent] at same
  rw [FrameCursor32.target_checked (rows book allow) (counts_fit book counts allow) frame valid running]
  simpa only [rows, Array.getElem_ofFn, vertex, move] using same.symm

theorem slot_some_iff (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (allow : UInt32 → UInt32 → Bool) (source : TurnEncoding.State n)
    (move : Fin (book source.1).size) (target : TurnEncoding.State n) :
    slot book allow source move = some (TurnEncoding.encode target) ↔
      MoveRows32.child32 (book source.1)[move.val] (TurnEncoding32.encode source) = TurnEncoding32.encode target ∧
      allow (TurnEncoding32.encode source) (UInt32.ofNat move.val) = true := by
  unfold slot
  dsimp only
  split
  · rename_i leaf
    constructor
    · intro impossible; cases impossible
    · rintro ⟨same, _⟩
      exact False.elim (TurnEncoding32.encode_ne_none fits target (same.symm.trans leaf))
  · split
    · rename_i permitted
      rw [Option.map_eq_some']
      constructor
      · rintro ⟨decoded, found, equal⟩
        have same := TurnEncoding.encode_injective equal
        subst decoded
        exact ⟨((TurnEncoding32.decode_some_iff fits _ target).mp found).symm, permitted⟩
      · rintro ⟨same, _⟩
        exact ⟨target, (TurnEncoding32.decode_some_iff fits _ target).mpr same.symm, rfl⟩
    · rename_i denied
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, permitted⟩
        exact False.elim (denied permitted)

/-- 有効な内部手が復号の失敗によって失われることはない。 -/
theorem allowed_internal_found (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (allow : UInt32 → UInt32 → Bool) (source : TurnEncoding.State n)
    (move : Fin (book source.1).size) (internal : (book source.1)[move.val] ≠ .leaf)
    (permitted : allow (TurnEncoding32.encode source) (UInt32.ofNat move.val) = true) :
    ∃ target, slot book allow source move = some target := by
  have bounded := valid source.1 move
  cases found : (book source.1)[move.val] with
  | leaf => exact False.elim (internal found)
  | internal next =>
    rw [found] at bounded
    let target : TurnEncoding.State n := (⟨next.toNat, bounded⟩, !source.2)
    refine ⟨TurnEncoding.encode target, (slot_some_iff fits book allow source move target).mpr ⟨?_, permitted⟩⟩
    have same := TurnEncoding32.flipIndex_encode fits (⟨next.toNat, bounded⟩ : Fin n) source
    simpa only [found, MoveRows32.child32, UInt32.ofNat_toNat, target] using same

/-- 元配列の枠番号を保ったまま、許可された内部辺だけをグラフの辺とする。 -/
theorem edge_exact (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (allow : UInt32 → UInt32 → Bool) (a b : Fin (2 * n)) :
    ForwardDfs.Edge (ForwardDfsRaw32.outgoing (rows book allow)) a b ↔
      MoveRows32.relation book allow (TurnEncoding.decode a) (TurnEncoding.decode b) := by
  change some b ∈ (rows book allow a).toList ↔ _
  rw [Array.mem_toList, rows, Array.mem_ofFn]
  have encoded : some b = some (TurnEncoding.encode (TurnEncoding.decode b)) :=
    congrArg some (TurnEncoding.encode_decode b).symm
  rw [encoded]
  change (∃ move, slot book allow (TurnEncoding.decode a) move = some (TurnEncoding.encode (TurnEncoding.decode b))) ↔ _
  simp only [slot_some_iff fits, MoveRows32.relation]

theorem cyclic_exact (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    CyclicVertex (ForwardDfs.Edge (ForwardDfsRaw32.outgoing (rows book allow))) vertex ↔
      CyclicVertex (MoveRows32.relation book allow) (TurnEncoding.decode vertex) := by
  constructor
  · rintro ⟨next, edge, ⟨back⟩⟩
    exact ⟨TurnEncoding.decode next, (edge_exact fits book allow vertex next).mp edge,
      ⟨back.mapVertices TurnEncoding.decode (fun a b => (edge_exact fits book allow a b).mp)⟩⟩
  · rintro ⟨next, edge, ⟨back⟩⟩
    have preserves : ∀ a b, MoveRows32.relation book allow a b →
        ForwardDfs.Edge (ForwardDfsRaw32.outgoing (rows book allow)) (TurnEncoding.encode a) (TurnEncoding.encode b) := by
      intro a b allowed
      apply (edge_exact fits book allow _ _).mpr
      simpa only [TurnEncoding.decode_encode] using allowed
    have first := preserves _ _ edge
    have returning := back.mapVertices TurnEncoding.encode preserves
    rw [TurnEncoding.encode_decode] at first returning
    exact ⟨TurnEncoding.encode next, first, ⟨returning⟩⟩

/-- 生フレームの第一DFSを用いたcoreは、元の機械式許可辺上の循環頂点そのもの。 -/
theorem core_correct (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    vertex ∈ RawFrameScc32.core (rows book allow) ↔
      CyclicVertex (MoveRows32.relation book allow) (TurnEncoding.decode vertex) := by
  have capacity : 2 * n ≤ ComponentLabels32.unset.toNat := by
    have bound := TurnEncoding32.fits_bound fits
    change 2 * n ≤ 4294967295
    omega
  rw [RawFrameScc32.core_correct capacity _ (counts_fit book counts allow)]
  exact cyclic_exact fits book allow vertex

end PetaProof.MachineFrameRows32
