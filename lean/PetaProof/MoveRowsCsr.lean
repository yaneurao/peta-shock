import PetaProof.IndexedMoveRows

/-!
逆辺の格納値を実際の自然数対(v,j)へ具体化する。
初期値は型付き辺でなく生の数値対なので、空の指し手配列・空グラフにも対応する。
範囲外IDは構築入力には現れず、完成区間の読出しにも現れない。
-/
namespace PetaProof.MoveRowsCsr

open IndexedMoveRows
variable {n : Nat}

def edges (rows : Rows n) : List (Edge rows) := SccCsrView.edges (view rows)
def rawEdges (rows : Rows n) : List Raw := (edges rows).map (encode rows)

/-- 範囲外IDの便宜的な0は未使用。実際の入力辺では常にdecodeが成功する。 -/
def target (rows : Rows n) (raw : Raw) : Nat :=
  ((decode rows raw).map (SccCsrView.target (view rows))).getD 0

theorem target_encode (rows : Rows n) (edge : Edge rows) :
    target rows (encode rows edge) = SccCsrView.target (view rows) edge := by
  simp [target, decode_encode]

theorem bounded (rows : Rows n) : ∀ raw ∈ rawEdges rows, target rows raw < n := by
  intro raw member
  obtain ⟨edge, _, same⟩ := List.mem_map.mp member
  subst raw
  rw [target_encode]
  exact (SccIndexedView.target (view rows) edge).isLt

def rawIncoming (rows : Rows n) (seed : Raw) (vertex : Fin n) : List Raw :=
  CsrConstructArray.row n seed (target rows) (rawEdges rows) vertex.val

/-- 生の番号対を格納した区間は、型付き辺の安定バケットをencodeした列と一致する。 -/
theorem rawIncoming_exact (rows : Rows n) (seed : Raw) (vertex : Fin n) :
    rawIncoming rows seed vertex =
      (Csr.bucket (SccCsrView.target (view rows)) (edges rows) vertex.val).map (encode rows) := by
  rw [rawIncoming, CsrConstructArray.row_exact n seed _ _ (bounded rows) _ vertex.isLt]
  unfold Csr.bucket rawEdges
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro edge _
  simp [target_encode]

/-- filterMapで不正IDを捨てて結果を合わせるのでなく、全要素の復号成功を先に示す。 -/
theorem decoded_all (rows : Rows n) (seed : Raw) (vertex : Fin n) :
    (rawIncoming rows seed vertex).map (decode rows) =
      (Csr.bucket (SccCsrView.target (view rows)) (edges rows) vertex.val).map some := by
  rw [rawIncoming_exact, List.map_map]
  apply List.map_congr_left
  intro edge _
  exact decode_encode rows edge

def incoming (rows : Rows n) (seed : Raw) (vertex : Fin n) : List (Edge rows) :=
  (rawIncoming rows seed vertex).filterMap (decode rows)

theorem incoming_exact (rows : Rows n) (seed : Raw) (vertex : Fin n) :
    incoming rows seed vertex = SccIndexedView.incoming (view rows) (List.finRange n) vertex := by
  unfold incoming
  rw [rawIncoming_exact, List.filterMap_map]
  have recovery : decode rows ∘ encode rows = some := by
    funext edge
    exact decode_encode rows edge
  rw [recovery, List.filterMap_some]
  exact (Csr.row_exact _ _ _).symm.trans (SccCsrView.incoming_exact (view rows) vertex)

theorem incoming_member (rows : Rows n) (seed : Raw) (vertex : Fin n) (edge : Edge rows) :
    edge ∈ incoming rows seed vertex ↔ (view rows).child edge = some vertex := by
  rw [incoming_exact]
  exact SccIndexedView.incoming_member (view rows) _ (CoreEnumeration.finRange_covers n) vertex edge

theorem construction_safe (rows : Rows n) (seed : Raw) :
    CsrConstructArray.Safe n seed (target rows) (rawEdges rows) :=
  CsrConstructArray.build_safe n seed _ _ (bounded rows)

theorem storage_capacity (rows : Rows n) (seed : Raw) :
    (CsrConstructArray.build n seed (target rows) (rawEdges rows)).state.memory.size = (edges rows).length := by
  rw [CsrConstructArray.build_exact n seed _ _ (bounded rows)]
  have size := (CsrPayloadArray.built_sizes n seed _ _ (bounded rows)).2
  simpa [rawEdges] using size

/-- 初期値が実在する辺を指すかどうかに関係なく、完成区間の読出しは同じ。 -/
theorem seed_independent (rows : Rows n) (a b : Raw) (vertex : Fin n) :
    rawIncoming rows a vertex = rawIncoming rows b vertex := by
  rw [rawIncoming_exact, rawIncoming_exact]

end PetaProof.MoveRowsCsr
