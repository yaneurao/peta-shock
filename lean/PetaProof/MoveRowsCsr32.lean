import PetaProof.CsrMap
import PetaProof.MoveRows32

/-!
CSRの格納先をArray (UInt32 × UInt32)へ具体化する。
offset/cursorはNatのまま。型付き逆辺へ戻してごまかさず、格納した二つのフィールドからcallbackする。
-/
namespace PetaProof.MoveRowsCsr32

open MoveRows32
variable {n : Nat}
abbrev Pair := UInt32 × UInt32
def unpack (edge : Pair) : IndexedMoveRows.Raw := (edge.1.toNat, edge.2.toNat)
def edges (book : Book n) : List Pair := (MoveRowsCsr.edges (rows book)).map (edge32 book)
def target (book : Book n) (edge : Pair) : Nat := MoveRowsCsr.target (rows book) (unpack edge)

theorem target_edge32 (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (edge : IndexedMoveRows.Edge (rows book)) :
    target book (edge32 book edge) = SccCsrView.target (IndexedMoveRows.view (rows book)) edge := by
  unfold target
  rw [show unpack (edge32 book edge) = IndexedMoveRows.encode (rows book) edge from edge32_decodes fits book counts edge]
  exact MoveRowsCsr.target_encode (rows book) edge

theorem unpacked_edges (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) :
    (edges book).map unpack = MoveRowsCsr.rawEdges (rows book) := by
  simp only [edges, List.map_map, MoveRowsCsr.rawEdges]
  apply List.map_congr_left
  intro edge _
  exact edge32_decodes fits book counts edge

theorem bounded (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) :
    ∀ edge ∈ edges book, target book edge < n := by
  intro edge member
  have present : unpack edge ∈ MoveRowsCsr.rawEdges (rows book) := by
    rw [← unpacked_edges fits book counts]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  exact MoveRowsCsr.bounded (rows book) _ present

def build (book : Book n) (seed : Pair) : CsrConstructArray.Built Pair :=
  CsrConstructArray.build n seed (target book) (edges book)

/-- 機械整数配列を構築してからunpackすると、自然数配列の構築結果全体と一致する。 -/
theorem build_refines (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) (seed : Pair) :
    CsrMap.mapBuilt unpack (build book seed) = CsrConstructArray.build n (unpack seed)
      (MoveRowsCsr.target (rows book)) (MoveRowsCsr.rawEdges (rows book)) := by
  unfold build
  rw [CsrMap.build_map unpack (target book) (MoveRowsCsr.target (rows book)) (fun _ => rfl),
    unpacked_edges fits book counts]

theorem construction_safe (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) (seed : Pair) :
    CsrConstructArray.Safe n seed (target book) (edges book) :=
  CsrConstructArray.build_safe n seed _ _ (bounded fits book counts)

theorem capacity (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) (seed : Pair) :
    (build book seed).state.memory.size = (MoveRowsCsr.edges (rows book)).length := by
  rw [build, CsrConstructArray.build_exact n seed _ _ (bounded fits book counts)]
  have size := (CsrPayloadArray.built_sizes n seed _ _ (bounded fits book counts)).2
  simpa [edges] using size

def incoming (book : Book n) (seed : Pair) (vertex : Fin n) : List Pair :=
  CsrConstructArray.row n seed (target book) (edges book) vertex.val

theorem incoming_refines (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (vertex : Fin n) :
    (incoming book seed vertex).map unpack = MoveRowsCsr.rawIncoming (rows book) (unpack seed) vertex := by
  unfold incoming MoveRowsCsr.rawIncoming
  rw [← CsrMap.row_map unpack (target book) (MoveRowsCsr.target (rows book)) (fun _ => rfl),
    unpacked_edges fits book counts]

/-- 完成区間は型付きの元辺をedge32に写した安定バケットそのものである。 -/
theorem incoming_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (vertex : Fin n) :
    incoming book seed vertex =
      (Csr.bucket (SccCsrView.target (IndexedMoveRows.view (rows book)))
        (MoveRowsCsr.edges (rows book)) vertex.val).map (edge32 book) := by
  rw [incoming, CsrConstructArray.row_exact n seed _ _ (bounded fits book counts) _ vertex.isLt]
  exact CsrMap.bucket_map (edge32 book) _ _ (target_edge32 fits book counts) _ _

theorem decoded_all (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (vertex : Fin n) :
    (incoming book seed vertex).map (fun edge => IndexedMoveRows.decode (rows book) (unpack edge)) =
      (Csr.bucket (SccCsrView.target (IndexedMoveRows.view (rows book)))
        (MoveRowsCsr.edges (rows book)) vertex.val).map some := by
  change (incoming book seed vertex).map (IndexedMoveRows.decode (rows book) ∘ unpack) = _
  rw [← List.map_map, incoming_refines fits book counts]
  exact MoveRowsCsr.decoded_all (rows book) (unpack seed) vertex

theorem seed_independent (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (first second : Pair) (vertex : Fin n) : incoming book first vertex = incoming book second vertex := by
  rw [incoming_exact fits book counts, incoming_exact fits book counts]

private theorem typed_bucket (book : Book n) (seed : IndexedMoveRows.Raw) (vertex : Fin n) :
    MoveRowsCsr.incoming (rows book) seed vertex =
      Csr.bucket (SccCsrView.target (IndexedMoveRows.view (rows book))) (MoveRowsCsr.edges (rows book)) vertex.val := by
  rw [MoveRowsCsr.incoming_exact, ← SccCsrView.incoming_exact, SccCsrView.incoming, Csr.row_exact]
  rfl

/-- 二つのUInt32フィールドを直接読み、親手番を補ってcallbackする。 -/
def callbacks (book : Book n) (seed : Pair) (state : TurnEncoding.State n) : List Pair :=
  (incoming book seed state.1).map (fun edge =>
    (TurnEncoding32.flipIndex edge.1 (TurnEncoding32.encode state), edge.2))

theorem callbacks_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (state : TurnEncoding.State n) :
    callbacks book seed state = MoveRows32.callbacks32 book (unpack seed) state := by
  unfold callbacks MoveRows32.callbacks32
  rw [incoming_exact fits book counts, typed_bucket, List.map_map]
  rfl

def parents32 (book : Book n) (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) : List UInt32 :=
  ((callbacks book seed state).filter (fun edge => allow edge.1 edge.2)).map Prod.fst

theorem parents32_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    parents32 book seed allow state = MoveRows32.parents32 book (unpack seed) allow state := by
  rw [parents32, callbacks_exact fits book counts]
  rfl

/-- DFSに渡す型付き親列。復号が落とす要素はないことを、先に全列の等式から導く。 -/
def parents (book : Book n) (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    List (TurnEncoding.State n) := (parents32 book seed allow state).filterMap (TurnEncoding32.decode n)

theorem parents_decoded_all (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    (parents32 book seed allow state).map (TurnEncoding32.decode n) =
      (MoveRowsScc.parents (rows book) (unpack seed) (allowNat allow) state).map some := by
  rw [parents32_exact fits book counts, MoveRows32.parents32_exact fits, List.map_map]
  apply List.map_congr_left
  intro parent _
  exact TurnEncoding32.decode_encode fits parent

theorem parents_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    parents book seed allow state = MoveRowsScc.parents (rows book) (unpack seed) (allowNat allow) state := by
  rw [parents, parents32_exact fits book counts, MoveRows32.parents32_exact fits, List.filterMap_map]
  have recovery : TurnEncoding32.decode n ∘ TurnEncoding32.encode = some := by
    funext vertex
    exact TurnEncoding32.decode_encode fits vertex
  rw [recovery, List.filterMap_some]

def component (book : Book n) (seed : Pair) (allow : UInt32 → UInt32 → Bool) : TurnEncoding.State n → Nat :=
  ComponentNumbering.component (TurnEncoding.vertices n)
    (ForwardDfs.order (TurnEncoding.vertices n) (TurnEncoding.vertices n)
      (SccIndexedView.outgoing (TurnSharedGraph.expanded (IndexedMoveRows.view (rows book)))
        (MoveRowsScc.allowAt (rows book) (allowNat allow)))) (parents book seed allow)

theorem component_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (seed : Pair) (allow : UInt32 → UInt32 → Bool) :
    component book seed allow = MoveRowsScc.component (rows book) (unpack seed) (allowNat allow) := by
  have same : parents book seed allow = MoveRowsScc.parents (rows book) (unpack seed) (allowNat allow) := by
    funext state
    exact parents_exact fits book counts seed allow state
  simp only [component, MoveRowsScc.component, same]

def core (book : Book n) (seed : Pair) (allow : UInt32 → UInt32 → Bool) : List (TurnEncoding.State n) :=
  CoreEnumeration.core (ComponentCycleFlags.keep (TurnEncoding.vertices n) (component book seed allow)
    (fun _ => false)) (TurnEncoding.vertices n)

theorem core_correct (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book) (counts : CountsFit book)
    (seed : Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    state ∈ core book seed allow ↔ CyclicVertex (MoveRows32.relation book allow) state := by
  have same : core book seed allow = MoveRows32.core book (unpack seed) allow := by
    simp only [core, component_exact fits book counts, MoveRows32.core, MoveRowsScc.core]
  rw [same]
  exact MoveRows32.core_correct fits book valid (unpack seed) allow state

end PetaProof.MoveRowsCsr32
