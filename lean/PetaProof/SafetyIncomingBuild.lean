import PetaProof.SafetyClassification

namespace PetaProof.SafetyClassification

universe u v w
variable {V : Type u} {E : Type v} {A : Type w} [DecidableEq V]

/-- 子のバケットへ一件appendする。本番は辺IDでなく親IDを保存するが、重複は除去しない。 -/
def appendBucket (target : E → V) (label : E → A) (buckets : V → List A) (edge : E) : V → List A :=
  fun vertex => if vertex = target edge then buckets vertex ++ [label edge] else buckets vertex

def buildBuckets (target : E → V) (label : E → A) : List E → (V → List A) → (V → List A)
  | [], buckets => buckets
  | edge :: rest, buckets => buildBuckets target label rest (appendBucket target label buckets edge)

/-- 子ごとの逐次appendは、元の順序を保つfilter/mapと一致する。 -/
theorem buildBuckets_spec (target : E → V) (label : E → A) (edges : List E)
    (buckets : V → List A) (vertex : V) :
    buildBuckets target label edges buckets vertex = buckets vertex ++
      ((edges.filter (fun edge => target edge == vertex)).map label) := by
  induction edges generalizing buckets with
  | nil => simp [buildBuckets]
  | cons edge rest ih =>
    rw [buildBuckets, ih]
    by_cases same : vertex = target edge
    · simp [appendBucket, same, List.append_assoc]
    · have different : target edge ≠ vertex := Ne.symm same
      simp [appendBucket, same, different]

variable {G : ThresholdGame V} [DecidableEq E]

omit [DecidableEq E] in
theorem built_incoming_edges (input : Input G E) (vertices : List V) (vertex : V) :
    buildBuckets (target input) id (allInternal input vertices) (fun _ => []) vertex =
      incoming input vertices vertex := by
  rw [buildBuckets_spec]
  simp [incoming]

omit [DecidableEq E] in
/-- 実装の親IDリストは、証明用辺IDリストをsourceで写したもの。同じ親の複数出辺を保持する。 -/
theorem built_incoming_parents (input : Input G E) (vertices : List V) (vertex : V) :
    buildBuckets (target input) input.indexed.source (allInternal input vertices) (fun _ => []) vertex =
      (incoming input vertices vertex).map input.indexed.source := by
  rw [buildBuckets_spec]
  simp [incoming]

end PetaProof.SafetyClassification
