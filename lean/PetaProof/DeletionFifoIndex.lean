import PetaProof.DeletionFifoRanks
import PetaProof.CsrConstructArray
import PetaProof.CoreEnumeration

/-! 有限出辺の各出現に固有IDを与え、構築済みCSRを共有するFIFO索引へ接続する。 -/
namespace PetaProof

namespace PrebuiltCsr

universe u
variable {E : Type u}

/-- 構築結果を引数として受け取り、頂点を読むたびにCSRを作り直さない。 -/
def read (seed : E) (book : CsrConstructArray.Built E) (vertex : Nat) : List E :=
  let first := book.positions[vertex]?.getD 0
  let last := book.positions[vertex + 1]?.getD 0
  CsrPayloadArray.read seed book.state first (last - first)

theorem read_built (m : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ e ∈ edges, target e < m) (v : Nat) (inside : v < m) :
    read seed (CsrConstructArray.build m seed target edges) v = Csr.bucket target edges v :=
  CsrConstructArray.row_exact m seed target edges bounded v inside

end PrebuiltCsr

namespace HistoryArena.DeletionInput

variable {n : Nat} {A : HistoryArena (Fin n)} (input : DeletionInput A)

/-- 同じ子への重複辺も、出辺一覧の異なる位置として区別する。 -/
abbrev ReachEdge := (v : Option (Fin n)) × Fin ((input.reachNext v).length)

/-- 依存型の長さ証明は比較せず、頂点と位置の二つの有限IDだけを比較する。 -/
instance reachEdgeDecidableEq : DecidableEq input.ReachEdge := by
  intro a b
  rcases a with ⟨v, i⟩
  rcases b with ⟨w, j⟩
  by_cases same : v = w
  · subst w
    by_cases index : i = j
    · exact isTrue (by cases index; rfl)
    · exact isFalse (fun equal => index (Fin.ext (congrArg (fun e : input.ReachEdge => e.2.val) equal)))
  · exact isFalse (fun equal => same (congrArg (fun e : input.ReachEdge => e.1) equal))

def edgeSource (e : input.ReachEdge) : Option (Fin n) := e.1
def edgeChild (e : input.ReachEdge) : Option (Fin n) := (input.reachNext e.1).get e.2

def edgeOutgoing (v : Option (Fin n)) : List input.ReachEdge :=
  (List.finRange (input.reachNext v).length).map (fun j => ⟨v, j⟩)

theorem outgoing_member (v : Option (Fin n)) (e : input.ReachEdge) :
    e ∈ input.edgeOutgoing v ↔ input.edgeSource e = v := by
  constructor
  · intro member
    obtain ⟨j, _, same⟩ := List.mem_map.mp member
    exact (congrArg (input.edgeSource) same).symm
  · intro same
    rcases e with ⟨source, j⟩
    change source = v at same
    subst source
    exact List.mem_map.mpr ⟨j, CoreEnumeration.finRange_covers _ j, rfl⟩

theorem outgoing_unique (v : Option (Fin n)) : (input.edgeOutgoing v).Nodup := by
  apply (CoreEnumeration.finRange_unique _).map
  intro a b different same
  have eqval := congrArg (fun e : input.ReachEdge => e.2.val) same
  exact different (Fin.ext eqval)

theorem outgoing_length (v : Option (Fin n)) :
    (input.edgeOutgoing v).length = (input.reachNext v).length := by simp [edgeOutgoing]

theorem outgoing_nonempty (v : Option (Fin n)) : 0 < (input.edgeOutgoing v).length := by
  rw [input.outgoing_length]
  obtain ⟨w, legal⟩ := input.reachArena.moves_exist v
  change w ∈ input.reachNext v at legal
  cases shape : input.reachNext v with
  | nil => simp [shape] at legal
  | cons first rest => simp

def reachEdges : List input.ReachEdge := (reachVertices (n := n)).flatMap input.edgeOutgoing

theorem edges_cover (e : input.ReachEdge) : e ∈ input.reachEdges := by
  exact List.mem_flatMap.mpr ⟨e.1, reachVertices_cover _, (input.outgoing_member e.1 e).mpr rfl⟩

theorem vertices_unique : (reachVertices (n := n)).Nodup := by
  rw [reachVertices, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp
  · exact (CoreEnumeration.finRange_unique n).map some
      (fun _ _ different same => different (Option.some.inj same))

theorem edges_unique : input.reachEdges.Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun v _ => input.outgoing_unique v, ?_⟩
  apply List.Pairwise.imp ?_ (vertices_unique (n := n))
  intro first second different e left f right same
  have a := (input.outgoing_member first e).mp left
  have b := (input.outgoing_member second f).mp right
  subst f
  exact different (a.symm.trans b)

theorem edges_length : input.reachEdges.length =
    1 + ((List.finRange n).map (fun v => (input.next v).length)).sum := by
  rw [reachEdges, List.length_flatMap]
  have same : (reachVertices (n := n)).map (fun v => (input.edgeOutgoing v).length) =
      (reachVertices (n := n)).map (fun v => (input.reachNext v).length) := by
    apply List.map_congr_left
    intro v _
    exact input.outgoing_length v
  rw [same]
  exact input.reach_edges_count

def vertexIndex : Option (Fin n) → Nat
  | none => n
  | some v => v.val

theorem vertexIndex_bound (v : Option (Fin n)) : vertexIndex v < n + 1 := by
  cases v with
  | none => simp [vertexIndex]
  | some v => have := v.isLt; simp only [vertexIndex]; omega

theorem vertexIndex_injective (v w : Option (Fin n)) (same : vertexIndex v = vertexIndex w) : v = w := by
  cases v with
  | none =>
    cases w with
    | none => rfl
    | some w => have := w.isLt; simp only [vertexIndex] at same; omega
  | some v =>
    cases w with
    | none => have := v.isLt; simp only [vertexIndex] at same; omega
    | some w => exact congrArg some (Fin.ext same)

def edgeTarget (e : input.ReachEdge) : Nat := vertexIndex (input.edgeChild e)

def edgeSeed : input.ReachEdge := ⟨none, ⟨0, by simp [reachNext]⟩⟩

def reverseStorage : CsrConstructArray.Built input.ReachEdge :=
  CsrConstructArray.build (n + 1) input.edgeSeed input.edgeTarget input.reachEdges

theorem target_bounded : ∀ e ∈ input.reachEdges, input.edgeTarget e < n + 1 :=
  fun e _ => vertexIndex_bound (input.edgeChild e)

theorem incoming_exact (v : Option (Fin n)) :
    PrebuiltCsr.read input.edgeSeed input.reverseStorage (vertexIndex v) =
      Csr.bucket input.edgeTarget input.reachEdges (vertexIndex v) :=
  PrebuiltCsr.read_built _ _ _ _ input.target_bounded _ (vertexIndex_bound v)

theorem incoming_member (v : Option (Fin n)) (e : input.ReachEdge) :
    e ∈ PrebuiltCsr.read input.edgeSeed input.reverseStorage (vertexIndex v) ↔ input.edgeChild e = v := by
  rw [input.incoming_exact]
  simp only [Csr.bucket, List.mem_filter, beq_iff_eq]
  constructor
  · intro member
    exact vertexIndex_injective _ _ member.2
  · intro same
    exact ⟨input.edges_cover e, congrArg vertexIndex same⟩

theorem incoming_unique (v : Option (Fin n)) :
    (PrebuiltCsr.read input.edgeSeed input.reverseStorage (vertexIndex v)).Nodup := by
  rw [input.incoming_exact]
  exact input.edges_unique.filter _

/-- CSRは一回構築して閉包で共有する。各逆辺参照は区間を読むだけである。 -/
def builtIndex : EscapePropagation.Input (Option (Fin n)) input.ReachEdge :=
  let book := input.reverseStorage
  { child := input.edgeChild
    source := input.edgeSource
    outgoing := input.edgeOutgoing
    outgoing_correct := input.outgoing_member
    outgoing_unique := input.outgoing_unique
    outgoing_nonempty := input.outgoing_nonempty
    incoming := fun v => PrebuiltCsr.read input.edgeSeed book (vertexIndex v)
    incoming_correct := input.incoming_member
    incoming_unique := input.incoming_unique
    own := fun v => decide (input.reachArena.owner v = input.reachArena.player) }

theorem builtIndex_matches : EscapePropagation.ArenaMatch input.builtIndex input.reachArena := by
  constructor
  · intro v w
    change w ∈ input.reachNext v ↔ ∃ e ∈ input.edgeOutgoing v, input.edgeChild e = w
    constructor
    · intro member
      obtain ⟨j, same⟩ := List.mem_iff_get.mp member
      exact ⟨⟨v, j⟩, (input.outgoing_member v _).mpr rfl, same⟩
    · rintro ⟨⟨source, j⟩, member, same⟩
      have equal := (input.outgoing_member v _).mp member
      change source = v at equal
      subst source
      rw [← same]
      exact List.get_mem _ _
  · intro v
    change decide (input.reachArena.owner v = input.reachArena.player) = true ↔
      input.reachArena.owner v = input.reachArena.player
    simp

theorem reverse_construction_safe :
    CsrConstructArray.Safe (n + 1) input.edgeSeed input.edgeTarget input.reachEdges :=
  CsrConstructArray.build_safe _ _ _ _ input.target_bounded

theorem reverse_capacity : input.reverseStorage.state.memory.size = input.reachEdges.length := by
  rw [reverseStorage, CsrConstructArray.build_exact _ _ _ _ input.target_bounded]
  exact (CsrPayloadArray.built_sizes _ _ _ _ input.target_bounded).2

/-- 位置表・cursor・辺ID格納表の長さを、入力だけから求める。 -/
theorem reverse_sizes : input.reverseStorage.positions.size = n + 2 ∧
    input.reverseStorage.state.cursor.size = n + 2 ∧
    input.reverseStorage.state.memory.size =
      1 + ((List.finRange n).map (fun v => (input.next v).length)).sum := by
  have sizes := CsrPayloadArray.built_sizes (n + 1) input.edgeSeed input.edgeTarget
    input.reachEdges input.target_bounded
  refine ⟨?_, ?_, input.reverse_capacity.trans input.edges_length⟩
  · rw [reverseStorage, CsrConstructArray.build_exact _ _ _ _ input.target_bounded]
    simp [CsrArray.offsets, Nat.add_assoc]
  · rw [reverseStorage, CsrConstructArray.build_exact _ _ _ _ input.target_bounded]
    simpa only [Nat.add_assoc] using sizes.1

theorem reverse_reads_safe (v : Option (Fin n)) :
    vertexIndex v < input.reverseStorage.positions.size ∧
    vertexIndex v + 1 < input.reverseStorage.positions.size ∧
    input.reverseStorage.positions[vertexIndex v]?.getD 0 ≤
      input.reverseStorage.positions[vertexIndex v + 1]?.getD 0 ∧
    input.reverseStorage.positions[vertexIndex v + 1]?.getD 0 ≤ input.reverseStorage.state.memory.size :=
  CsrConstructArray.row_accesses_safe _ _ _ _ input.target_bounded _ (vertexIndex_bound v)

/-- 索引・辺数・対応証拠も有限出辺入力から構築し、外部へ要求しない。 -/
def builtCounter : Option A.Counterstrategy :=
  input.fifoCheckedCounter input.builtIndex input.builtIndex_matches

theorem builtCounter_iff : input.builtCounter.isSome = true ↔ ∀ v, ¬ A.HistoryWinning v :=
  input.fifoCheckedCounter_iff input.builtIndex input.builtIndex_matches

theorem builtCounter_agrees : input.builtCounter.isSome = input.checkedCounter.isSome :=
  input.fifoCheckedCounter_agrees input.builtIndex input.builtIndex_matches

theorem built_labels_exact (horizon : Nat) (empty : ∀ v, ¬ A.goodIter horizon v) (v : Fin n) :
    (fifoTable input.builtIndex)[v.val]? = some (some (A.deletionTime horizon empty v)) :=
  input.fifoTable_exact input.builtIndex input.builtIndex_matches horizon empty v

/-- 一回の実行に対する投入と通知の上界も、構築したID一覧で充足する。 -/
theorem built_events_bound
    (state : EscapePropagation.State (Option (Fin n)) input.ReachEdge)
    (started : EscapePropagation.State.start input.builtIndex [none] = some state) :
    let final := EscapePropagation.State.run input.builtIndex (n + 1) state
    final.frame.queue.total.length ≤ n + 1 ∧
      (input.builtIndex.toInput.notifications (final.frame.queue.popped.map Prod.fst)).length ≤
        1 + ((List.finRange n).map (fun v => (input.next v).length)).sum :=
  input.fifo_events_input_bound input.builtIndex input.reachEdges input.edges_cover input.edges_length state started

end HistoryArena.DeletionInput
end PetaProof
