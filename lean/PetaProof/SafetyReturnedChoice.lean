import PetaProof.SafetyClassification

namespace PetaProof.SafetyClassification

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] {G : ThresholdGame V}

/-- 返却時のinternal判定。C++と同じく、goodを除外する条件は付けない。 -/
def liveInternal (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) (edge : E) : Bool :=
  match input.indexed.move edge with
  | .leaf _ => false
  | .node child => !state.deleted child &&
      (decide (G.owner vertex = G.player) || input.checked vertex child)

/-- goodを全出辺から先に探し、見つからないときだけ残存内部辺を探す二回の走査。 -/
def returnedChoice (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) : Option E :=
  match (input.indexed.outgoing vertex).find? (goodFlag input) with
  | some edge => some edge
  | none => (input.indexed.outgoing vertex).find? (liveInternal input state vertex)

omit [DecidableEq V] [DecidableEq E] in
theorem returned_choice_good_priority (input : Input G E) (state : SafetyExecution.State V E)
    (vertex : V) (edge : E) (good : (input.indexed.outgoing vertex).find? (goodFlag input) = some edge) :
    returnedChoice input state vertex = some edge := by simp [returnedChoice, good]

omit [DecidableEq V] [DecidableEq E] in
theorem returned_choice_safe (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) (edge : E)
    (selected : returnedChoice input state vertex = some edge) :
    G.legal vertex (input.indexed.move edge) ∧
      G.SafeMove (fun vertex => input.won vertex = true) (SafetyExecution.alive state) vertex (input.indexed.move edge) := by
  unfold returnedChoice at selected
  cases found : (input.indexed.outgoing vertex).find? (goodFlag input) with
  | some candidate =>
    rw [found] at selected
    have same : candidate = edge := Option.some.inj selected
    subst candidate
    have legal := input.indexed.legal vertex edge (List.mem_of_find?_eq_some found)
    have good := (goodFlag_correct input edge).mp (List.find?_some found)
    refine ⟨legal, ?_⟩
    cases move : input.indexed.move edge with
    | leaf score => simpa only [move, ThresholdGame.GoodExit, ThresholdGame.SafeMove] using good
    | node child => exact Or.inl (by simpa only [move, ThresholdGame.GoodExit] using good)
  | none =>
    rw [found] at selected
    have legal := input.indexed.legal vertex edge (List.mem_of_find?_eq_some selected)
    have internal := List.find?_some selected
    refine ⟨legal, ?_⟩
    cases move : input.indexed.move edge with
    | leaf score => simp [liveInternal, move] at internal
    | node child =>
      have supported : state.deleted child = false ∧ (G.owner vertex = G.player ∨ G.check vertex child) := by
        simpa only [liveInternal, move, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
          decide_eq_true_eq, input.check_correct] using internal
      exact Or.inr supported

/-- 生存するOR頂点ではNoneを返さない。goodがなければ、生存内部辺を必ず発見する。 -/
theorem returned_choice_exists (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) {state : SafetyExecution.State V E} {n : Nat}
    (run : SafetyExecution.Run (graph input vertices unique covered)
      (SafetyExecution.initial (graph input vertices unique covered) vertices) n state)
    (stopped : SafetyExecution.Stopped state) (vertex : V) (live : SafetyExecution.alive state vertex)
    (own : G.owner vertex = G.player) : ∃ edge, returnedChoice input state vertex = some edge := by
  have result := SafetyExecution.greatest_at_halt (graph input vertices unique covered) vertices covered
    run stopped.1 stopped.2
  have stay := (result.1 vertex live).1 (by simpa only [graph, decide_eq_true_eq] using own)
  cases found : (input.indexed.outgoing vertex).find? (goodFlag input) with
  | some edge => exact ⟨edge, returned_choice_good_priority input state vertex edge found⟩
  | none =>
    obtain ⟨edge, _, support⟩ := stay
    have witness : ∃ edge, edge ∈ input.indexed.outgoing vertex ∧ liveInternal input state vertex edge = true := by
      rcases support with good | ⟨internal, child_live⟩
      · have member := (mem_good input vertex edge).mp good
        have absent := (List.find?_eq_none.mp found) edge member.2.1
        exact False.elim (absent member.2.2)
      · have member := (mem_internal input vertex edge).mp internal
        have move := (internal_child input vertex edge internal).1
        refine ⟨edge, member.2.1, ?_⟩
        simp only [liveInternal, move, own, decide_true, Bool.true_or, Bool.and_true, Bool.not_eq_true']
        exact child_live
    have nonempty : ((input.indexed.outgoing vertex).find? (liveInternal input state vertex)).isSome :=
      List.find?_isSome.mpr witness
    cases selected : (input.indexed.outgoing vertex).find? (liveInternal input state vertex) with
    | none => simp [selected] at nonempty
    | some candidate => exact ⟨candidate, by simp [returnedChoice, found, selected]⟩

/-- C++のchoice欄に対応する。相手番には指し手を指定せずNoneを返す。 -/
def returnedIndex (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) : Option E :=
  if G.owner vertex = G.player then returnedChoice input state vertex else none

omit [DecidableEq V] [DecidableEq E] in
theorem opponent_choice_none (input : Input G E) (state : SafetyExecution.State V E) (vertex : V)
    (opponent : G.owner vertex ≠ G.player) : returnedIndex input state vertex = none := by
  simp [returnedIndex, opponent]

theorem returned_index_exists (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) {state : SafetyExecution.State V E} {n : Nat}
    (run : SafetyExecution.Run (graph input vertices unique covered)
      (SafetyExecution.initial (graph input vertices unique covered) vertices) n state)
    (stopped : SafetyExecution.Stopped state) (vertex : V) (live : SafetyExecution.alive state vertex)
    (own : G.owner vertex = G.player) : ∃ edge, returnedIndex input state vertex = some edge := by
  simpa only [returnedIndex, own, ite_true] using
    returned_choice_exists input vertices unique covered run stopped vertex live own

omit [DecidableEq V] [DecidableEq E] in
theorem returned_index_safe (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) (edge : E)
    (selected : returnedIndex input state vertex = some edge) :
    G.legal vertex (input.indexed.move edge) ∧
      G.SafeMove (fun vertex => input.won vertex = true) (SafetyExecution.alive state) vertex (input.indexed.move edge) := by
  by_cases own : G.owner vertex = G.player
  · apply returned_choice_safe input state vertex edge
    simpa only [returnedIndex, own, ite_true] using selected
  · simp [returnedIndex, own] at selected

def returnedMove (input : Input G E) (state : SafetyExecution.State V E) (vertex : V) : Move V :=
  match returnedIndex input state vertex with
  | some edge => input.indexed.move edge
  | none => .leaf 0

/-- 存在的なchoiceではなく、二回の先頭走査で実際に選んだ手を使う保証バッチ。 -/
def returnedBatch (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) {state : SafetyExecution.State V E} {n : Nat}
    (run : SafetyExecution.Run (graph input vertices unique covered)
      (SafetyExecution.initial (graph input vertices unique covered) vertices) n state)
    (stopped : SafetyExecution.Stopped state) :
    G.SafeBatch (fun vertex => input.won vertex = true) (SafetyExecution.alive state) := by
  have result := SafetyExecution.greatest_at_halt (graph input vertices unique covered) vertices covered
    run stopped.1 stopped.2
  have safeSet := ((gameModel input vertices unique covered).safeSet_iff
    (graph input vertices unique covered) input.indexed (fun vertex => input.won vertex = true)
    (SafetyExecution.alive state) result.2.1).mp result.1
  apply ThresholdGame.SafeBatch.ofOrAnd (choice := returnedMove input state)
  · intro vertex live
    exact eligible_fresh input vertex (result.2.1 vertex live)
  · intro vertex live own
    obtain ⟨edge, selected⟩ := returned_index_exists input vertices unique covered run stopped vertex live own
    simpa only [returnedMove, selected] using (returned_index_safe input state vertex edge selected).1
  · intro vertex live own
    obtain ⟨edge, selected⟩ := returned_index_exists input vertices unique covered run stopped vertex live own
    simpa only [returnedMove, selected] using (returned_index_safe input state vertex edge selected).2
  · intro vertex live opponent move legal
    exact (safeSet vertex live).2 opponent move legal

theorem returnedBatch_choice (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) {state : SafetyExecution.State V E} {n : Nat}
    (run : SafetyExecution.Run (graph input vertices unique covered)
      (SafetyExecution.initial (graph input vertices unique covered) vertices) n state)
    (stopped : SafetyExecution.Stopped state) (vertex : V) :
    (returnedBatch input vertices unique covered run stopped).choice vertex = returnedMove input state vertex := rfl

/-- 初期分類、有限停止、実際の返却手によるバッチを一つの定理にまとめる。 -/
theorem classified_solves (input : Input G E) (vertices : List V) (unique : vertices.Nodup)
    (covered : ∀ vertex, vertex ∈ vertices) :
    ∃ n state, SafetyExecution.Run (graph input vertices unique covered)
      (SafetyExecution.initial (graph input vertices unique covered) vertices) n state ∧
      SafetyExecution.Stopped state ∧
      Nonempty (G.SafeBatch (fun vertex => input.won vertex = true) (SafetyExecution.alive state)) ∧
      (∀ vertex, SafetyExecution.alive state vertex → G.owner vertex = G.player →
        ∃ edge, returnedIndex input state vertex = some edge) ∧
      ∀ kept, G.SafeSet (fun vertex => input.won vertex = true) kept →
        (∀ vertex, kept vertex → eligible input vertex = true) →
          ∀ vertex, kept vertex → SafetyExecution.alive state vertex := by
  obtain ⟨n, state, run, stopped, _⟩ := SafetyExecution.halts (graph input vertices unique covered) vertices
    unique covered (SafetyExecution.initial (graph input vertices unique covered) vertices)
  refine ⟨n, state, run, stopped, ⟨returnedBatch input vertices unique covered run stopped⟩,
    returned_index_exists input vertices unique covered run stopped, ?_⟩
  have result := SafetyExecution.greatest_at_halt (graph input vertices unique covered) vertices covered
    run stopped.1 stopped.2
  intro kept safe subset
  exact result.2.2 kept (((gameModel input vertices unique covered).safeSet_iff
    (graph input vertices unique covered) input.indexed (fun vertex => input.won vertex = true) kept subset).mpr safe) subset

end PetaProof.SafetyClassification
