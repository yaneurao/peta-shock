import PetaProof.SafetyIncomingBuild

namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

structure InitRow (V : Type u) (E : Type v) where
  count : Nat
  bad : Bool
  incoming : V → List E

omit [DecidableEq V] [DecidableEq E] in
theorem InitRow.ext {left right : InitRow V E} (count : left.count = right.count)
    (bad : left.bad = right.bad) (incoming : left.incoming = right.incoming) : left = right := by
  cases left
  cases right
  simp_all

/-- 初期化の一辺処理。goodを最初に判定し、badは相手番でだけ立てる。 -/
def initEdge (input : Input G E) (vertex : V) (row : InitRow V E) (edge : E) : InitRow V E :=
  if goodFlag input edge then { row with count := row.count + 1 }
  else if internalFlag input vertex edge then {
    row with count := row.count + 1
             incoming := appendBucket (target input) id row.incoming edge
  }
  else if G.owner vertex ≠ G.player then { row with bad := true } else row

def initRow (input : Input G E) (vertex : V) : List E → InitRow V E → InitRow V E
  | [], row => row
  | edge :: rest, row => initRow input vertex rest (initEdge input vertex row edge)

omit [DecidableEq E] in
theorem initRow_count (input : Input G E) (vertex : V) (edges : List E) (row : InitRow V E) :
    (initRow input vertex edges row).count = row.count +
      (edges.filter (goodFlag input)).length + (edges.filter (internalFlag input vertex)).length := by
  induction edges generalizing row with
  | nil => simp [initRow]
  | cons edge rest ih =>
    cases good : goodFlag input edge with
    | true =>
      have internal : internalFlag input vertex edge = false := by simp [internalFlag, good]
      simp [initRow, ih, initEdge, good, internal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | false =>
      cases internal : internalFlag input vertex edge <;>
        by_cases own : G.owner vertex = G.player <;>
        simp [initRow, ih, initEdge, good, internal, own, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq E] in
theorem initRow_bad (input : Input G E) (vertex : V) (edges : List E) (row : InitRow V E) :
    (initRow input vertex edges row).bad = (row.bad ||
      (decide (G.owner vertex ≠ G.player) && edges.any (fun edge => !goodFlag input edge && !internalFlag input vertex edge))) := by
  induction edges generalizing row with
  | nil => simp [initRow]
  | cons edge rest ih =>
    cases good : goodFlag input edge with
    | true => simp [initRow, ih, initEdge, good]
    | false =>
      cases internal : internalFlag input vertex edge <;>
        by_cases own : G.owner vertex = G.player <;>
        simp [initRow, ih, initEdge, good, internal, own]

omit [DecidableEq E] in
theorem initRow_incoming (input : Input G E) (vertex : V) (edges : List E) (row : InitRow V E) :
    (initRow input vertex edges row).incoming =
      buildBuckets (target input) id (edges.filter (internalFlag input vertex)) row.incoming := by
  induction edges generalizing row with
  | nil => rfl
  | cons edge rest ih =>
    cases good : goodFlag input edge with
    | true =>
      have internal : internalFlag input vertex edge = false := by simp [internalFlag, good]
      simp [initRow, ih, initEdge, good, internal]
    | false =>
      cases internal : internalFlag input vertex edge <;>
        by_cases own : G.owner vertex = G.player <;>
        simp [initRow, ih, initEdge, good, internal, own, buildBuckets]

omit [DecidableEq E] in
/-- 初期化中のcountは走査辺数を超えて増えない。固定幅整数への対応には別途値域条件が必要。 -/
theorem initRow_count_bound (input : Input G E) (vertex : V) (edges : List E) (row : InitRow V E) :
    (initRow input vertex edges row).count ≤ row.count + edges.length := by
  induction edges generalizing row with
  | nil => exact Nat.le_refl _
  | cons edge rest ih =>
    have bound := ih (initEdge input vertex row edge)
    have growth : (initEdge input vertex row edge).count ≤ row.count + 1 := by
      cases good : goodFlag input edge <;> cases internal : internalFlag input vertex edge <;>
        by_cases own : G.owner vertex = G.player <;> simp [initEdge, good, internal, own]
    simp only [initRow, List.length_cons]
    omega

def initBad (input : Input G E) (vertex : V) : Bool :=
  decide (G.owner vertex ≠ G.player) && !(badEdges input vertex).isEmpty

def initCount (input : Input G E) (vertex : V) : Nat :=
  (goodEdges input vertex).length + (internalEdges input vertex).length

omit [DecidableEq V] [DecidableEq E] in
theorem bad_any_iff (input : Input G E) (vertex : V) (active : eligible input vertex = true) :
    (input.indexed.outgoing vertex).any (fun edge => !goodFlag input edge && !internalFlag input vertex edge) =
      !(badEdges input vertex).isEmpty := by
  have fact : ∀ (edges : List E) (predicate : E → Bool), edges.any predicate = !(edges.filter predicate).isEmpty := by
    intro edges predicate
    induction edges with
    | nil => rfl
    | cons edge rest ih => cases flag : predicate edge <;> simp [flag, ih]
  simp only [badEdges, active, ite_true]
  exact fact _ _

omit [DecidableEq E] in
/-- 一親の走査完了時にcount/bad/incomingが同時に分類仕様と一致する。 -/
theorem initRow_zero (input : Input G E) (vertex : V) (active : eligible input vertex = true)
    (buckets : V → List E) :
    initRow input vertex (input.indexed.outgoing vertex) ⟨0, false, buckets⟩ =
      ⟨initCount input vertex, initBad input vertex,
        buildBuckets (target input) id (internalEdges input vertex) buckets⟩ := by
  apply InitRow.ext
  · rw [initRow_count]
    simp [initCount, goodEdges, internalEdges, active]
  · rw [initRow_bad, bad_any_iff input vertex active]
    simp [initBad]
  · rw [initRow_incoming]
    simp [internalEdges, active]

structure InitArrays (V : Type u) (E : Type v) where
  count : V → Nat
  bad : V → Bool
  incoming : V → List E
  pending : List V

def initSeed (input : Input G E) (vertex : V) : Bool :=
  eligible input vertex && if G.owner vertex = G.player then initCount input vertex == 0
    else !(badEdges input vertex).isEmpty

/-- 配列の現在値を引き継ぐ。各親を一回ずつ処理するなら、未処理親のcount/badは初期値である。 -/
def initVertex (input : Input G E) (arrays : InitArrays V E) (vertex : V) : InitArrays V E :=
  if eligible input vertex then
    let row := initRow input vertex (input.indexed.outgoing vertex)
      ⟨arrays.count vertex, arrays.bad vertex, arrays.incoming⟩
    { count := fun other => if other = vertex then row.count else arrays.count other
      bad := fun other => if other = vertex then row.bad else arrays.bad other
      incoming := row.incoming
      pending := if (decide (G.owner vertex = G.player) && row.count == 0) || row.bad then
        arrays.pending ++ [vertex] else arrays.pending }
  else arrays

def initializeRows (input : Input G E) : List V → InitArrays V E → InitArrays V E
  | [], arrays => arrays
  | vertex :: rest, arrays => initializeRows input rest (initVertex input arrays vertex)

def emptyArrays : InitArrays V E := ⟨fun _ => 0, fun _ => false, fun _ => [], []⟩

/-- 初期化の途中における、処理済みの親列と配列の対応。 -/
structure Processed (input : Input G E) (vertices : List V) (arrays : InitArrays V E) : Prop where
  count : ∀ vertex, arrays.count vertex = if vertex ∈ vertices then initCount input vertex else 0
  bad : ∀ vertex, arrays.bad vertex = if vertex ∈ vertices then initBad input vertex else false
  incoming : ∀ vertex, arrays.incoming vertex = incoming input vertices vertex
  pending : arrays.pending = vertices.filter (initSeed input)

omit [DecidableEq V] [DecidableEq E] in
theorem initSeed_active (input : Input G E) (vertex : V) (active : eligible input vertex = true) :
    ((decide (G.owner vertex = G.player) && initCount input vertex == 0) || initBad input vertex) = initSeed input vertex := by
  by_cases own : G.owner vertex = G.player <;> simp [initSeed, active, initBad, own]

omit [DecidableEq V] [DecidableEq E] in
theorem inactive_summaries (input : Input G E) (vertex : V) (inactive : eligible input vertex = false) :
    initCount input vertex = 0 ∧ initBad input vertex = false ∧ internalEdges input vertex = [] ∧ initSeed input vertex = false := by
  simp [initCount, goodEdges, internalEdges, initBad, badEdges, initSeed, inactive]

omit [DecidableEq E] in
theorem empty_processed (input : Input G E) : Processed input [] (emptyArrays (V := V) (E := E)) := by
  constructor <;> simp [emptyArrays, incoming, allInternal]

omit [DecidableEq E] in
theorem initVertex_preserves (input : Input G E) (prior : List V) (arrays : InitArrays V E)
    (processed : Processed input prior arrays) (vertex : V) (fresh : vertex ∉ prior) :
    Processed input (prior ++ [vertex]) (initVertex input arrays vertex) := by
  have zero_count : arrays.count vertex = 0 := by rw [processed.count]; simp [fresh]
  have zero_bad : arrays.bad vertex = false := by rw [processed.bad]; simp [fresh]
  cases active : eligible input vertex with
  | false =>
    have summaries := inactive_summaries input vertex active
    simp only [initVertex, active, Bool.false_eq_true, ite_false]
    constructor
    · intro other
      by_cases same : other = vertex
      · subst other; simp [zero_count, summaries.1]
      · rw [processed.count]; simp [same]
    · intro other
      by_cases same : other = vertex
      · subst other; simp [zero_bad, summaries.2.1]
      · rw [processed.bad]; simp [same]
    · intro other
      rw [processed.incoming]
      simp [incoming, allInternal, List.flatMap_append, summaries.2.2.1]
    · rw [processed.pending]
      simp [List.filter_append, summaries.2.2.2]
  | true =>
    have summary := initRow_zero input vertex active arrays.incoming
    simp only [initVertex, active, ite_true, zero_count, zero_bad, summary]
    constructor
    · intro other
      by_cases same : other = vertex
      · subst other; simp
      · simp only [if_neg same, processed.count]
        simp [same]
    · intro other
      by_cases same : other = vertex
      · subst other; simp
      · simp only [if_neg same, processed.bad]
        simp [same]
    · intro other
      dsimp only
      rw [buildBuckets_spec, processed.incoming]
      simp [incoming, allInternal, List.flatMap_append, List.filter_append]
    · rw [initSeed_active input vertex active, processed.pending]
      cases flag : initSeed input vertex <;> simp [List.filter_append, flag]

omit [DecidableEq E] in
theorem initialize_processed (input : Input G E) (prior rest : List V) (arrays : InitArrays V E)
    (processed : Processed input prior arrays) (unique : rest.Nodup)
    (fresh : ∀ vertex ∈ rest, vertex ∉ prior) :
    Processed input (prior ++ rest) (initializeRows input rest arrays) := by
  induction rest generalizing prior arrays with
  | nil => simpa [initializeRows] using processed
  | cons vertex tail ih =>
    have nodup := List.nodup_cons.mp unique
    have next := initVertex_preserves input prior arrays processed vertex (fresh vertex (by simp))
    have tail_fresh : ∀ other ∈ tail, other ∉ prior ++ [vertex] := by
      intro other member old
      rcases List.mem_append.mp old with earlier | same
      · exact fresh other (by simp [member]) earlier
      · have equal : other = vertex := by simpa using same
        exact nodup.1 (by simpa only [equal] using member)
    have result := ih (prior ++ [vertex]) (initVertex input arrays vertex) next nodup.2 tail_fresh
    simpa only [initializeRows, List.append_assoc, List.singleton_append] using result

omit [DecidableEq E] in
theorem initialize_spec (input : Input G E) (vertices : List V) (unique : vertices.Nodup) :
    Processed input vertices (initializeRows input vertices emptyArrays) := by
  simpa only [List.nil_append] using initialize_processed input [] vertices emptyArrays
    (empty_processed input) unique (by simp)

omit [DecidableEq E] in
theorem initCount_bound (input : Input G E) (vertex : V) :
    initCount input vertex ≤ (input.indexed.outgoing vertex).length := by
  cases active : eligible input vertex with
  | false => simp [(inactive_summaries input vertex active).1]
  | true =>
    have bound := initRow_count_bound input vertex (input.indexed.outgoing vertex)
      (⟨0, false, fun _ => []⟩ : InitRow V E)
    rw [initRow_zero input vertex active] at bound
    simpa only [Nat.zero_add] using bound

/-- 走査済み親の配列から、削除キューを開始する証明用状態へ移す。 -/
def executionOf (input : Input G E) (arrays : InitArrays V E) : SafetyExecution.State V E := {
  deleted := fun vertex => !(eligible input vertex)
  counters := fun vertex => ⟨fun _ => false, arrays.count vertex⟩
  pending := arrays.pending
  work := []
  handled := fun _ => false
}

omit [DecidableEq E] in
theorem initialize_state_eq (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    executionOf input (initializeRows input vertices emptyArrays) =
      SafetyExecution.initial (graph input vertices unique covered) vertices := by
  have spec := initialize_spec input vertices unique
  have counts : (initializeRows input vertices emptyArrays).count = initCount input := by
    funext vertex
    rw [spec.count]
    simp [covered vertex]
  have seeds : (initializeRows input vertices emptyArrays).pending =
      vertices.filter (fun vertex => eligible input vertex && SafetyExecution.initialReject
        (graph input vertices unique covered) vertex) := by
    rw [spec.pending]
    congr 1
    funext vertex
    simp [initSeed, SafetyExecution.initialReject, graph, view, initCount]
  simp only [executionOf, counts, seeds]
  rfl

omit [DecidableEq E] in
theorem initialized_invariant (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    SafetyExecution.Invariant (graph input vertices unique covered)
      (executionOf input (initializeRows input vertices emptyArrays)) := by
  rw [initialize_state_eq input vertices unique covered]
  exact SafetyExecution.initial_invariant _ vertices covered

omit [DecidableEq E] in
theorem initialize_incoming_eq (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    (initializeRows input vertices emptyArrays).incoming = (graph input vertices unique covered).incoming := by
  funext vertex
  exact (initialize_spec input vertices unique).incoming vertex

/-- 削除時に使う逆辺は、分類から再生成せず、実際の初期走査で構築した配列を受け取る。 -/
def initializedGraph (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) : SafetyExecution.Graph V E := {
  graph input vertices unique covered with
  incoming := (initializeRows input vertices emptyArrays).incoming
  incoming_unique := by
    rw [initialize_incoming_eq input vertices unique covered]
    exact (graph input vertices unique covered).incoming_unique
  incoming_spec := by
    rw [initialize_incoming_eq input vertices unique covered]
    exact (graph input vertices unique covered).incoming_spec
}

omit [DecidableEq E] in
theorem initializedGraph_eq (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) : initializedGraph input vertices unique covered =
      graph input vertices unique covered := by
  unfold initializedGraph
  simp only [initialize_incoming_eq input vertices unique covered]

end PetaProof.SafetyClassification
