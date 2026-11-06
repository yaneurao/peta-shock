import PetaProof.SelectiveRankCapture

/-! 頂点を一回だけ走査し、取得先番号の要求バケットへ先頭登録する。
全phaseごとの頂点filterは参照仕様だけに現れ、構築ループでは実行しない。 -/
namespace PetaProof.RankRequestBuckets

variable {n b : Nat}

def row (buckets : Array (List (Fin n))) (key : Fin b) : List (Fin n) := (buckets[key.val]?).getD []

def put (route : Fin n → Option (Fin b)) (buckets : Array (List (Fin n))) (vertex : Fin n) : Array (List (Fin n)) :=
  match route vertex with
  | none => buckets
  | some key => buckets.setIfInBounds key.val (vertex :: row buckets key)

theorem put_size (route : Fin n → Option (Fin b)) (buckets : Array (List (Fin n))) (vertex : Fin n) :
    (put route buckets vertex).size = buckets.size := by
  cases found : route vertex <;> simp [put, found]

theorem put_row (route : Fin n → Option (Fin b)) (buckets : Array (List (Fin n)))
    (space : buckets.size = b) (vertex : Fin n) (key : Fin b) :
    row (put route buckets vertex) key = if route vertex = some key then vertex :: row buckets key else row buckets key := by
  cases found : route vertex with
  | none => simp [put, found]
  | some actual =>
    by_cases same : actual = key
    · subst actual
      have valid : key.val < buckets.size := by omega
      simp [put, found, row, Array.getElem?_setIfInBounds, valid]
    · have different : actual.val ≠ key.val := fun equal => same (Fin.ext equal)
      simp [put, found, row, same, Array.getElem?_setIfInBounds, different, Ne.symm different]

def distribute (route : Fin n → Option (Fin b)) : List (Fin n) → Array (List (Fin n)) → Array (List (Fin n))
  | [], buckets => buckets
  | vertex :: rest, buckets => distribute route rest (put route buckets vertex)

theorem distribute_size (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) (buckets : Array (List (Fin n))) :
    (distribute route vertices buckets).size = buckets.size := by
  induction vertices generalizing buckets with
  | nil => rfl
  | cons vertex rest ih => simp only [distribute, ih, put_size]

theorem distribute_row (route : Fin n → Option (Fin b)) (vertices : List (Fin n))
    (buckets : Array (List (Fin n))) (space : buckets.size = b) (key : Fin b) :
    row (distribute route vertices buckets) key =
      vertices.reverse.filter (fun vertex => decide (route vertex = some key)) ++ row buckets key := by
  induction vertices generalizing buckets with
  | nil => simp [distribute]
  | cons vertex rest ih =>
    rw [distribute, ih _ (by simpa only [put_size] using space), put_row route buckets space vertex key]
    by_cases hit : route vertex = some key <;> simp [List.reverse_cons, List.filter_append, hit, List.append_assoc]

def build (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) : Array (List (Fin n)) :=
  distribute route vertices (Array.replicate b [])

theorem build_size (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) :
    (build route vertices).size = b := by simp [build, distribute_size]

theorem build_row (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) (key : Fin b) :
    row (build route vertices) key = vertices.reverse.filter (fun vertex => decide (route vertex = some key)) := by
  rw [build, distribute_row route vertices _ (by simp)]
  have valid : key.val < b := key.isLt
  simp [row, Array.getElem?_eq_getElem, valid]

theorem build_member (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) (key : Fin b) (vertex : Fin n) :
    vertex ∈ row (build route vertices) key ↔ vertex ∈ vertices ∧ route vertex = some key := by
  simp only [build_row, List.mem_filter, List.mem_reverse, decide_eq_true_eq]

theorem row_unique (route : Fin n → Option (Fin b)) (vertices : List (Fin n)) (unique : vertices.Nodup) (key : Fin b) :
    (row (build route vertices) key).Nodup := by
  rw [build_row]
  have reversed : vertices.reverse.Nodup := by
    change List.Pairwise (fun first second => first ≠ second) vertices.reverse
    rw [List.pairwise_reverse]
    exact unique.imp (fun different => Ne.symm different)
  exact reversed.filter _

end PetaProof.RankRequestBuckets
