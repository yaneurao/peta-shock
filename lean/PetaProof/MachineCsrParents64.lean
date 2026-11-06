import PetaProof.MachineFrameRows32
import PetaProof.MoveRowsCsr64

/-!
同じ元指し手配列から構築したUInt64 CSRを、番号化した2n頂点の逆辺へ接続する。
callbackはUInt32の親番号と元jの対を保ち、許可判定にはその両方を使う。
-/
namespace PetaProof.MachineCsrParents64

variable {n : Nat}

theorem label_capacity (fits : TurnEncoding32.Fits n) : 2 * n ≤ ComponentLabels32.unset.toNat := by
  have bound := TurnEncoding32.fits_bound fits
  change 2 * n ≤ 4294967295
  omega

theorem word_capacity (fits : TurnEncoding32.Fits n) : 2 * n ≤ UInt32.size :=
  ComponentStackArray.word_capacity (label_capacity fits)

/-- 手番付きの型へ復号してから番号化しても、生の頂点番号の復号と一致する。 -/
theorem decoder_exact (word : UInt32) :
    (TurnEncoding32.decode n word).map TurnEncoding.encode = VertexStack32.decode (2 * n) word := by
  by_cases inside : word.toNat < 2 * n
  · simp only [TurnEncoding32.decode, VertexStack32.decode, dif_pos inside]
    change some (TurnEncoding.encode (TurnEncoding.decode (⟨word.toNat, inside⟩ : Fin (2 * n)))) = _
    rw [TurnEncoding.encode_decode]
  · simp only [TurnEncoding32.decode, VertexStack32.decode, dif_neg inside]
    rfl

def callbacks (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (vertex : Fin (2 * n)) : List MoveRowsCsr32.Pair :=
  MoveRowsCsr64.callbacks book seed (TurnEncoding.decode vertex)

def words (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) : List UInt32 :=
  ((callbacks book seed vertex).filter (fun edge => allow edge.1 edge.2)).map Prod.fst

def parents (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) : List (Fin (2 * n)) :=
  (words book seed allow vertex).filterMap (VertexStack32.decode (2 * n))

theorem words_exact (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) :
    words book seed allow vertex = MoveRows32.parents32 book (MoveRowsCsr32.unpack seed) allow (TurnEncoding.decode vertex) := by
  unfold words callbacks
  rw [MoveRowsCsr64.callbacks_exact fits book counts (MoveRowsCsr64.capacityFits_of_bounds fits book counts),
    MoveRowsCsr32.callbacks_exact fits book counts]
  rfl

/-- 許可後の親列は順序・重複回数を含めて一致する。集合としてだけの一致ではない。 -/
theorem parents_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    parents book seed allow vertex =
      (MoveRowsCsr64.parents book seed allow (TurnEncoding.decode vertex)).map TurnEncoding.encode := by
  unfold parents words callbacks MoveRowsCsr64.parents
  rw [List.map_filterMap]
  simp only [decoder_exact]

/-- 既存の局面数・行長条件から、許可後の全callbackの親番号が範囲内になる。 -/
theorem words_valid (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) : ∀ word ∈ words book seed allow vertex, word.toNat < 2 * n := by
  rw [words_exact fits book counts, MoveRows32.parents32_exact fits]
  intro word member
  obtain ⟨source, _, same⟩ := List.mem_map.mp member
  rw [← same, TurnEncoding32.encode_toNat fits]
  exact (TurnEncoding.encode source).isLt

theorem no_parent_dropped (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) :
    (parents book seed allow vertex).length = (words book seed allow vertex).length :=
  VertexStack32.list_length _ (words_valid fits book counts seed allow vertex)

/-- 実際に許可されるcallbackは必ず復号でき、resultの同じ番号を参照する。 -/
theorem allowed_callback_safe (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (vertex : Fin (2 * n)) (edge : MoveRowsCsr32.Pair) (member : edge ∈ callbacks book seed vertex)
    (permitted : allow edge.1 edge.2 = true) :
    ∃ parent : Fin (2 * n), VertexStack32.decode (2 * n) edge.1 = some parent ∧
      VertexStack32.encode parent = edge.1 ∧ parent.val = edge.1.toNat := by
  have present : edge.1 ∈ words book seed allow vertex :=
    List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨member, permitted⟩, rfl⟩
  have bound := words_valid fits book counts seed allow vertex edge.1 present
  refine ⟨⟨edge.1.toNat, bound⟩, ?_, ?_, rfl⟩
  · simp only [VertexStack32.decode, dif_pos bound]
  · simp only [VertexStack32.encode, UInt32.ofNat_toNat]

/-- resultのガードはallowより先なので、不許可手を含む全callbackの復号を保証する。 -/
theorem callback_safe (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (vertex : Fin (2 * n)) (edge : MoveRowsCsr32.Pair) (member : edge ∈ callbacks book seed vertex) :
    ∃ parent : Fin (2 * n), VertexStack32.decode (2 * n) edge.1 = some parent ∧
      VertexStack32.encode parent = edge.1 ∧ parent.val = edge.1.toNat :=
  allowed_callback_safe fits book counts seed (fun _ _ => true) vertex edge member rfl

theorem callback_result_safe (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (vertex : Fin (2 * n)) (edge : MoveRowsCsr32.Pair) (member : edge ∈ callbacks book seed vertex)
    (result : Array UInt32) (size : result.size = 2 * n) :
    ∃ parent : Fin (2 * n), VertexStack32.decode (2 * n) edge.1 = some parent ∧ parent.val < result.size := by
  obtain ⟨parent, decoded, _, _⟩ := callback_safe fits book counts seed vertex edge member
  exact ⟨parent, decoded, by rw [size]; exact parent.isLt⟩

/-- callbackの元jも、その親の元指し手配列内にある。allow内での元手参照の入口条件。 -/
theorem callback_slot_safe (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (vertex : Fin (2 * n)) (edge : MoveRowsCsr32.Pair) (member : edge ∈ callbacks book seed vertex) :
    ∃ source : TurnEncoding.State n, TurnEncoding32.encode source = edge.1 ∧ edge.2.toNat < (book source.1).size := by
  rw [callbacks, MoveRowsCsr64.callbacks_exact fits book counts (MoveRowsCsr64.capacityFits_of_bounds fits book counts),
    MoveRowsCsr32.callbacks_exact fits book counts, MoveRows32.callbacks32] at member
  obtain ⟨original, _, same⟩ := List.mem_map.mp member
  have bound : original.2.val < (book original.1).size := by
    simpa only [MoveRows32.row_size] using original.2.isLt
  refine ⟨(original.1, !(TurnEncoding.decode vertex).2), ?_, ?_⟩
  · simpa only [TurnEncoding32.flipIndex_encode fits] using congrArg Prod.fst same
  · have index_same := congrArg Prod.snd same
    change UInt32.ofNat original.2.val = edge.2 at index_same
    rw [← index_same, UInt32.toNat_ofNat_of_lt' (Nat.lt_trans bound (counts original.1))]
    exact bound

theorem callbacks_seed_independent (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (first second : MoveRowsCsr32.Pair) (vertex : Fin (2 * n)) :
    callbacks book first vertex = callbacks book second vertex := by
  simp only [callbacks, MoveRowsCsr64.callbacks,
    MoveRowsCsr64.incoming_exact fits book counts (MoveRowsCsr64.capacityFits_of_bounds fits book counts)]
  rw [MoveRowsCsr32.seed_independent fits book counts first second]

theorem parents_transpose (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (child parent : Fin (2 * n)) :
    parent ∈ parents book seed allow child ↔
      ForwardDfs.Edge (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) parent child := by
  rw [parents_exact, MoveRowsCsr64.parents_exact fits book counts (MoveRowsCsr64.capacityFits_of_bounds fits book counts),
    MoveRowsCsr32.parents_exact fits book counts]
  have member : parent ∈ (MoveRowsScc.parents (MoveRows32.rows book) (MoveRowsCsr32.unpack seed)
      (MoveRows32.allowNat allow) (TurnEncoding.decode child)).map TurnEncoding.encode ↔
      TurnEncoding.decode parent ∈ MoveRowsScc.parents (MoveRows32.rows book) (MoveRowsCsr32.unpack seed)
        (MoveRows32.allowNat allow) (TurnEncoding.decode child) := by
    constructor
    · rintro present
      obtain ⟨source, present, same⟩ := List.mem_map.mp present
      have recovered := congrArg TurnEncoding.decode same
      rw [TurnEncoding.decode_encode] at recovered
      simpa only [← recovered] using present
    · intro present
      exact List.mem_map.mpr ⟨TurnEncoding.decode parent, present, TurnEncoding.encode_decode parent⟩
  rw [member, MoveRowsScc.parents_transpose, SccIndexedView.outgoing_correct,
    ← MoveRows32.relation_exact fits book valid allow, MachineFrameRows32.edge_exact fits book allow]

end PetaProof.MachineCsrParents64
