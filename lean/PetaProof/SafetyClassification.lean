import PetaProof.SafetyExecutionGame

namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
variable {G : ThresholdGame V}

/-- 出辺列挙と既確定フラグ、core、王手判定だけを入力する。good/internalや逆辺は入力しない。 -/
structure Input (G : ThresholdGame V) (E : Type v) where
  indexed : G.IndexedMoves E
  won : V → Bool
  core : V → Bool
  checked : V → V → Bool
  check_correct : ∀ vertex child, checked vertex child = true ↔ G.check vertex child

def eligible (input : Input G E) (vertex : V) : Bool := input.core vertex && !input.won vertex

def goodFlag (input : Input G E) (edge : E) : Bool :=
  match input.indexed.move edge with
  | .leaf score => decide (G.threshold ≤ score)
  | .node child => input.won child

def internalFlag (input : Input G E) (vertex : V) (edge : E) : Bool :=
  !goodFlag input edge && match input.indexed.move edge with
  | .leaf _ => false
  | .node child => eligible input child &&
      (decide (G.owner vertex = G.player) || input.checked vertex child)

/-- 非内部辺のtargetは参照しないため、leafには親IDを仮に返す。 -/
def target (input : Input G E) (edge : E) : V :=
  match input.indexed.move edge with
  | .node child => child
  | .leaf _ => input.indexed.source edge

def goodEdges (input : Input G E) (vertex : V) : List E :=
  if eligible input vertex then (input.indexed.outgoing vertex).filter (goodFlag input) else []

def internalEdges (input : Input G E) (vertex : V) : List E :=
  if eligible input vertex then (input.indexed.outgoing vertex).filter (internalFlag input vertex) else []

def badEdges (input : Input G E) (vertex : V) : List E :=
  if eligible input vertex then (input.indexed.outgoing vertex).filter
    (fun edge => !goodFlag input edge && !internalFlag input vertex edge) else []

omit [DecidableEq V] [DecidableEq E] in
theorem mem_good (input : Input G E) (vertex : V) (edge : E) :
    edge ∈ goodEdges input vertex ↔ eligible input vertex = true ∧
      edge ∈ input.indexed.outgoing vertex ∧ goodFlag input edge = true := by
  cases active : eligible input vertex <;> simp [goodEdges, active]

omit [DecidableEq V] [DecidableEq E] in
theorem mem_internal (input : Input G E) (vertex : V) (edge : E) :
    edge ∈ internalEdges input vertex ↔ eligible input vertex = true ∧
      edge ∈ input.indexed.outgoing vertex ∧ internalFlag input vertex edge = true := by
  cases active : eligible input vertex <;> simp [internalEdges, active]

omit [DecidableEq V] [DecidableEq E] in
theorem mem_bad (input : Input G E) (vertex : V) (edge : E) :
    edge ∈ badEdges input vertex ↔ eligible input vertex = true ∧ edge ∈ input.indexed.outgoing vertex ∧
      goodFlag input edge = false ∧ internalFlag input vertex edge = false := by
  cases active : eligible input vertex <;> simp [badEdges, active]

omit [DecidableEq V] [DecidableEq E] in
theorem internal_not_good (input : Input G E) (vertex : V) (edge : E)
    (inside : internalFlag input vertex edge = true) : goodFlag input edge = false := by
  cases good : goodFlag input edge with
  | false => rfl
  | true => simp [internalFlag, good] at inside

def view (input : Input G E) (vertex : V) : SafetyCounter.View E := {
  good := goodEdges input vertex
  internal := internalEdges input vertex
  bad := badEdges input vertex
  internal_unique := by
    cases active : eligible input vertex
    · simp [internalEdges, active]
    · simp only [internalEdges, active, ite_true]
      exact (input.indexed.unique vertex).filter _
  internal_not_good := by
    intro edge inside exit
    have no_good := internal_not_good input vertex edge ((mem_internal input vertex edge).mp inside).2.2
    have good := ((mem_good input vertex edge).mp exit).2.2
    rw [good] at no_good
    cases no_good
  bad_disjoint := by
    intro edge bad
    have h := (mem_bad input vertex edge).mp bad
    constructor
    · intro good
      have flag := ((mem_good input vertex edge).mp good).2.2
      rw [flag] at h
      cases h.2.2.1
    · intro inside
      have flag := ((mem_internal input vertex edge).mp inside).2.2
      rw [flag] at h
      cases h.2.2.2
}

omit [DecidableEq V] [DecidableEq E] in
theorem source_of_mem (input : Input G E) (vertex : V) (edge : E)
    (member : edge ∈ internalEdges input vertex) : input.indexed.source edge = vertex :=
  input.indexed.source_of_mem vertex edge ((mem_internal input vertex edge).mp member).2.1

omit [DecidableEq V] [DecidableEq E] in
theorem internal_child (input : Input G E) (vertex : V) (edge : E)
    (member : edge ∈ internalEdges input vertex) :
    input.indexed.move edge = .node (target input edge) ∧ eligible input (target input edge) = true := by
  have flag := ((mem_internal input vertex edge).mp member).2.2
  cases move : input.indexed.move edge with
  | leaf score => simp [internalFlag, move] at flag
  | node child =>
    have active : eligible input child = true := by
      have conjunction : goodFlag input edge = false ∧ eligible input child = true ∧
          (G.owner vertex = G.player ∨ input.checked vertex child = true) := by
        simpa only [internalFlag, move, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq] using flag
      exact conjunction.2.1
    exact ⟨by simp [target, move], by simpa only [target, move] using active⟩

omit [DecidableEq V] [DecidableEq E] in
theorem outgoing_partition (input : Input G E) (vertex : V) (active : eligible input vertex = true) (edge : E) :
    edge ∈ (view input vertex).outgoing ↔ edge ∈ input.indexed.outgoing vertex := by
  simp only [view, SafetyCounter.View.outgoing, List.mem_append, mem_good, mem_internal, mem_bad, active,
    true_and]
  cases g : goodFlag input edge <;> cases i : internalFlag input vertex edge <;> simp [g, i]

def allInternal (input : Input G E) (vertices : List V) : List E :=
  vertices.flatMap (internalEdges input)

omit [DecidableEq V] [DecidableEq E] in
theorem mem_allInternal (input : Input G E) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices) (edge : E) :
    edge ∈ allInternal input vertices ↔ edge ∈ internalEdges input (input.indexed.source edge) := by
  simp only [allInternal, List.mem_flatMap]
  constructor
  · rintro ⟨vertex, _, member⟩
    simpa only [source_of_mem input vertex edge member] using member
  · intro member
    exact ⟨input.indexed.source edge, covered _, member⟩

omit [DecidableEq V] [DecidableEq E] in
/-- 辺IDの親が一意なので、異なる親の内部辺列は互いに素である。 -/
theorem allInternal_unique (input : Input G E) (vertices : List V) (unique : vertices.Nodup) :
    (allInternal input vertices).Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons vertex rest ih =>
    have nodup := List.nodup_cons.mp unique
    change (internalEdges input vertex ++ allInternal input rest).Nodup
    apply List.pairwise_append.mpr
    refine ⟨(view input vertex).internal_unique, ih nodup.2, ?_⟩
    intro a first b second same
    obtain ⟨other, member, internal⟩ := List.mem_flatMap.mp second
    have source_a := source_of_mem input vertex a first
    have source_b := source_of_mem input other b internal
    have equal : vertex = other := source_a.symm.trans ((congrArg input.indexed.source same).trans source_b)
    exact nodup.1 (by simpa only [equal] using member)

def incoming (input : Input G E) (vertices : List V) (vertex : V) : List E :=
  (allInternal input vertices).filter (fun edge => target input edge == vertex)

def graph (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) : SafetyExecution.Graph V E := {
  view := view input
  own := fun vertex => decide (G.owner vertex = G.player)
  eligible := eligible input
  source := input.indexed.source
  target := target input
  source_of_mem := source_of_mem input
  source_eligible := fun vertex edge member => ((mem_internal input vertex edge).mp member).1
  target_eligible := fun vertex edge member => (internal_child input vertex edge member).2
  incoming := incoming input vertices
  incoming_unique := fun _ => (allInternal_unique input vertices unique).filter _
  incoming_spec := by
    intro vertex edge
    simp only [incoming, List.mem_filter, mem_allInternal input vertices covered, beq_iff_eq]
    rfl
}

omit [DecidableEq V] [DecidableEq E] in
theorem goodFlag_correct (input : Input G E) (edge : E) :
    goodFlag input edge = true ↔ G.GoodExit (fun vertex => input.won vertex = true) (input.indexed.move edge) := by
  cases move : input.indexed.move edge <;> simp [goodFlag, move, ThresholdGame.GoodExit]

omit [DecidableEq V] [DecidableEq E] in
theorem internalFlag_correct (input : Input G E) (vertex : V) (edge : E) :
    internalFlag input vertex edge = true ↔ ∃ child, input.indexed.move edge = .node child ∧
      ¬ input.won child = true ∧ eligible input child = true ∧
      (G.owner vertex = G.player ∨ G.check vertex child) := by
  cases move : input.indexed.move edge with
  | leaf score => simp [internalFlag, move]
  | node child =>
    cases won : input.won child <;>
      simp [internalFlag, goodFlag, move, won, input.check_correct]

/-- 初期分類からGameModelの全条件を導く。呼出し側にgood/internalの意味を仮定させない。 -/
def gameModel (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    SafetyExecution.GameModel (graph input vertices unique covered) input.indexed (fun vertex => input.won vertex = true) := {
  own := fun _ => rfl
  outgoing := outgoing_partition input
  good := by
    intro vertex active edge member
    have active' : eligible input vertex = true := active
    have legal := (outgoing_partition input vertex active edge).mp member
    change edge ∈ goodEdges input vertex ↔ _
    rw [mem_good]
    simp only [active', legal, true_and]
    exact goodFlag_correct input edge
  internal := by
    intro vertex active edge member
    have active' : eligible input vertex = true := active
    have legal := (outgoing_partition input vertex active edge).mp member
    change edge ∈ internalEdges input vertex ↔ _
    rw [mem_internal]
    simp only [active', legal, true_and]
    exact internalFlag_correct input vertex edge
  target := fun vertex edge member => (internal_child input vertex edge member).1
}

omit [DecidableEq V] [DecidableEq E] in
theorem eligible_fresh (input : Input G E) (vertex : V) (active : eligible input vertex = true) :
    ¬ input.won vertex = true := by
  cases won : input.won vertex <;> simp_all [eligible]

end PetaProof.SafetyClassification
