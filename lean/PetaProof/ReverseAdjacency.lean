import PetaProof.GeneratedThresholds

/-! 元辺を一度prependし、各行を一度reverseして安定な逆辺一覧を作る。 -/
namespace PetaProof.ReverseAdjacency

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

def targets (move : E → Move V) (vertex : V) (edge : E) : Bool := match move edge with
  | .leaf _ => false
  | .node child => decide (child = vertex)

def internal (move : E → Move V) (edge : E) : Bool := match move edge with
  | .leaf _ => false
  | .node _ => true

theorem targets_spec (move : E → Move V) (vertex : V) (edge : E) :
    targets move vertex edge = true ↔ move edge = .node vertex := by
  cases found : move edge <;> simp [targets, found]

def prependOne (move : E → Move V) (rows : V → List E) (edge : E) : V → List E :=
  match move edge with
  | .leaf _ => rows
  | .node child => fun vertex => if vertex = child then edge :: rows vertex else rows vertex

def scan (move : E → Move V) : List E → (V → List E) → (V → List E)
  | [], rows => rows
  | edge :: rest, rows => scan move rest (prependOne move rows edge)

theorem scan_row (move : E → Move V) (edges : List E) (rows : V → List E) (vertex : V) :
    scan move edges rows vertex = (edges.filter (targets move vertex)).reverse ++ rows vertex := by
  induction edges generalizing rows with
  | nil => simp [scan]
  | cons edge rest ih =>
    rw [scan, ih]
    cases found : move edge with
    | leaf score => simp [prependOne, found, targets]
    | node child =>
      by_cases same : vertex = child
      · subst child
        simp [prependOne, found, targets, List.reverse_cons, List.append_assoc]
      · have different := Ne.symm same
        simp [prependOne, found, targets, same, different]

/-- 各行のreverseは構築時に一度だけ行い、probe時に計算し直さない。 -/
def finish : List V → (V → List E) → (V → List E) → (V → List E)
  | [], _, result => result
  | vertex :: rest, raw, result =>
    let row := (raw vertex).reverse
    finish rest raw (fun other => if other = vertex then row else result other)

theorem finish_row (vertices : List V) (raw result : V → List E) (vertex : V) :
    finish vertices raw result vertex = if vertex ∈ vertices then (raw vertex).reverse else result vertex := by
  induction vertices generalizing result with
  | nil => simp [finish]
  | cons head rest ih =>
    rw [finish, ih]
    by_cases same : vertex = head <;> by_cases member : vertex ∈ rest <;> simp [same, member]

def build (move : E → Move V) (vertices : List V) (edges : List E) : V → List E :=
  let raw := scan move edges (fun _ => [])
  finish vertices raw (fun _ => [])

theorem build_row (move : E → Move V) (vertices : List V) (edges : List E) (vertex : V)
    (member : vertex ∈ vertices) :
    build move vertices edges vertex = edges.filter (targets move vertex) := by
  simp only [build, finish_row, if_pos member, scan_row, List.append_nil, List.reverse_reverse]

theorem raw_row_length (move : E → Move V) (edges : List E) (vertex : V) :
    (scan move edges (fun _ => []) vertex).length = (edges.filter (targets move vertex)).length := by
  simp only [scan_row, List.append_nil, List.length_reverse]

theorem rows_unique (move : E → Move V) (vertices : List V) (unique : vertices.Nodup)
    (edges : List E) (edgesUnique : edges.Nodup) : (vertices.flatMap (build move vertices edges)).Nodup := by
  have generic : ∀ (selected : List V), selected.Nodup →
      (selected.flatMap (fun vertex => edges.filter (targets move vertex))).Nodup := by
    intro selected selectedUnique
    induction selected with
    | nil => exact List.nodup_nil
    | cons vertex rest ih =>
      have parts := List.nodup_cons.mp selectedUnique
      apply List.pairwise_append.mpr
      refine ⟨edgesUnique.filter _, ih parts.2, ?_⟩
      intro a first b second equal
      obtain ⟨other, member, present⟩ := List.mem_flatMap.mp second
      have firstMove := (targets_spec move vertex a).mp (List.mem_filter.mp first).2
      have secondMove := (targets_spec move other b).mp (List.mem_filter.mp present).2
      have same := Move.node.inj (firstMove.symm.trans ((congrArg move equal).trans secondMove))
      exact parts.1 (same ▸ member)
  have rows : vertices.flatMap (build move vertices edges) =
      vertices.flatMap (fun vertex => edges.filter (targets move vertex)) := by
    exact congrArg List.flatten (List.map_congr_left (fun vertex member =>
      build_row move vertices edges vertex member))
  rw [rows]
  exact generic vertices unique

theorem rows_within (move : E → Move V) (vertices : List V) (edges : List E) (edge : E)
    (member : edge ∈ vertices.flatMap (build move vertices edges)) : edge ∈ edges.filter (internal move) := by
  obtain ⟨vertex, present, inside⟩ := List.mem_flatMap.mp member
  rw [build_row move vertices edges vertex present] at inside
  have parts := List.mem_filter.mp inside
  have target := (targets_spec move vertex edge).mp parts.2
  exact List.mem_filter.mpr ⟨parts.1, by simp [internal, target]⟩

variable [DecidableEq E]

/-- 各行を一度だけ反転する際に訪れる要素数。経路の数ではなく内部辺数で抑える。 -/
def reversalWork (move : E → Move V) (vertices : List V) (edges : List E) : Nat :=
  (vertices.map (fun vertex => (scan move edges (fun _ => []) vertex).length)).sum

omit [DecidableEq E] in
theorem reversalWork_eq (move : E → Move V) (vertices : List V) (edges : List E) :
    reversalWork move vertices edges = (vertices.flatMap (build move vertices edges)).length := by
  rw [List.length_flatMap]
  unfold reversalWork
  congr 1
  apply List.map_congr_left
  intro vertex member
  rw [build_row move vertices edges vertex member, raw_row_length]

theorem reversalWork_bound (move : E → Move V) (vertices : List V) (unique : vertices.Nodup)
    (edges : List E) (edgesUnique : edges.Nodup) :
    reversalWork move vertices edges ≤ (edges.filter (internal move)).length := by
  rw [reversalWork_eq]
  exact DistinctWork.length_le _ _ (rows_unique move vertices unique edges edgesUnique)
    (fun edge member => rows_within move vertices edges edge member)

/-- 行・元辺一覧の準備、入力走査、内部辺のprepend、行ごとのreverseを数える。 -/
def constructionWork (move : E → Move V) (vertices : List V) (edges : List E) : Nat :=
  4 * vertices.length + 2 * edges.length + (edges.filter (internal move)).length + reversalWork move vertices edges

theorem constructionWork_bound (move : E → Move V) (vertices : List V) (unique : vertices.Nodup)
    (edges : List E) (edgesUnique : edges.Nodup) :
    constructionWork move vertices edges ≤ 4 * vertices.length + 4 * edges.length := by
  have reversal := reversalWork_bound move vertices unique edges edgesUnique
  have internalEdges := List.length_filter_le (internal move) edges
  unfold constructionWork
  omega

end PetaProof.ReverseAdjacency
