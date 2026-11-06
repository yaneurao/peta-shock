import PetaProof.ForwardDfsForest

/-!
出辺カーソルの意味と、終了済み頂点の出辺の走査完了。
priorは証明用のprefixであり、実行時に走査履歴を記録しない。
-/
namespace PetaProof.ForwardDfs

universe u
variable {V : Type u} [DecidableEq V]

def Edge (outgoing : V → List (Option V)) (source target : V) : Prop :=
  some target ∈ outgoing source

def Reach (outgoing : V → List (Option V)) (source target : V) : Prop :=
  Nonempty (Walk (Edge outgoing) source target)

theorem discover_finished (outgoing : V → List (Option V)) (state : State V) (vertex : V) :
    (discover outgoing state vertex).finished = state.finished := by
  cases visited : state.seen vertex <;> simp [discover, visited]

omit [DecidableEq V] in
theorem trim_finished (state : State V) : (trim state).finished = state.finished := by
  cases stack : state.stack <;> simp [trim, stack]

def Scanned (outgoing : V → List (Option V)) (seen : V → Bool) (frame : Frame V) : Prop :=
  ∃ prior, outgoing frame.vertex = prior ++ frame.todo ∧
    ∀ child, some child ∈ prior → seen child = true

structure ScanInvariant (outgoing : V → List (Option V)) (state : State V) : Prop where
  base : Invariant state
  cursor : ∀ frame ∈ state.stack, Scanned outgoing state.seen frame
  closed : ∀ vertex ∈ state.finished, ∀ child, Edge outgoing vertex child → state.seen child = true

omit [DecidableEq V] in
theorem scanned_mono (outgoing : V → List (Option V)) (before after : V → Bool)
    (mono : ∀ vertex, before vertex = true → after vertex = true) (frame : Frame V)
    (valid : Scanned outgoing before frame) : Scanned outgoing after frame := by
  obtain ⟨prior, same, visited⟩ := valid
  exact ⟨prior, same, fun child member => mono child (visited child member)⟩

omit [DecidableEq V] in
theorem scanned_edge (outgoing : V → List (Option V)) (seen : V → Bool) (frame : Frame V)
    (valid : Scanned outgoing seen frame) (child : V) (member : some child ∈ frame.todo) :
    Edge outgoing frame.vertex child := by
  obtain ⟨prior, same, _⟩ := valid
  rw [Edge, same]
  exact List.mem_append_right prior member

omit [DecidableEq V] in
theorem initial_scanned (outgoing : V → List (Option V)) : ScanInvariant outgoing (initial : State V) := by
  refine ⟨initial_invariant, ?_, ?_⟩ <;> simp [initial]

theorem discover_scanned (outgoing : V → List (Option V)) (state : State V)
    (valid : ScanInvariant outgoing state) (vertex : V) :
    ScanInvariant outgoing (discover outgoing state vertex) := by
  cases visited : state.seen vertex with
  | true => simpa [discover, visited] using valid
  | false =>
    refine ⟨discover_preserves outgoing state valid.base vertex, ?_, ?_⟩
    · intro frame member
      change frame ∈ (discover outgoing state vertex).stack at member
      simp only [discover, visited, Bool.false_eq_true, ite_false, List.mem_cons] at member
      rcases member with same | old
      · subst frame
        exact ⟨[], by simp, by simp⟩
      · exact scanned_mono outgoing state.seen _
          (fun child seen => discover_seen_stable outgoing state vertex child seen) frame (valid.cursor frame old)
    · intro parent member child edge
      have old : parent ∈ state.finished := by simpa [discover, visited] using member
      exact discover_seen_stable outgoing state vertex child (valid.closed parent old child edge)

omit [DecidableEq V] in
/-- 一枠消費した後に、その枠の内部辺の子が訪問済みならprefixを延ばせる。 -/
theorem scanned_consume (outgoing : V → List (Option V)) (before after : V → Bool)
    (mono : ∀ vertex, before vertex = true → after vertex = true)
    (frame : Frame V) (target : Option V) (rest : List (Option V))
    (todo : frame.todo = target :: rest) (valid : Scanned outgoing before frame)
    (head_seen : ∀ child, target = some child → after child = true) :
    Scanned outgoing after { frame with todo := rest } := by
  obtain ⟨prior, same, visited⟩ := valid
  refine ⟨prior ++ [target], ?_, ?_⟩
  · simpa [todo, List.append_assoc] using same
  · intro child member
    rcases List.mem_append.mp member with old | last
    · exact mono child (visited child old)
    · exact head_seen child (by simpa using (List.mem_singleton.mp last).symm)

theorem tick_scanned (outgoing : V → List (Option V)) (state : State V)
    (valid : ScanInvariant outgoing state) : ScanInvariant outgoing (tick outgoing state) := by
  cases stack : state.stack with
  | nil => simpa [tick, stack] using valid
  | cons frame rest =>
    have cursor := valid.cursor frame (by simp [stack])
    cases todo : frame.todo with
    | nil =>
      refine ⟨tick_preserves outgoing state valid.base, ?_, ?_⟩
      · intro other member
        have old : other ∈ rest := by simpa [tick, stack, todo, retire] using member
        have scan := valid.cursor other (by simp [stack, old])
        simpa [tick, stack, todo, retire] using scan
      · intro vertex member child edge
        have cases_member : vertex ∈ state.finished ∨ vertex = frame.vertex := by
          simpa [tick, stack, todo, retire] using member
        have seen : state.seen child = true := by
          rcases cases_member with old | same
          · exact valid.closed vertex old child edge
          · obtain ⟨prior, same_out, visited⟩ := cursor
            apply visited child
            simpa [Edge, same, same_out, todo] using edge
        simpa [tick, stack, todo, retire] using seen
    | cons target remaining =>
      have after_mono := fun vertex seen => tick_seen_stable outgoing state vertex seen
      have head_seen : ∀ child, target = some child → (tick outgoing state).seen child = true := by
        intro child same
        subst target
        simpa [tick, stack, todo] using discover_seen_at outgoing (trim state) child
      have consumed := scanned_consume outgoing state.seen (tick outgoing state).seen
        after_mono frame target remaining todo cursor head_seen
      have trimmed_cursor : ∀ other ∈ (trim state).stack,
          Scanned outgoing (tick outgoing state).seen other := by
        intro other member
        have cases_member : other = { frame with todo := remaining } ∨ other ∈ rest := by
          simpa [trim, stack, todo] using member
        rcases cases_member with rfl | old
        · exact consumed
        · exact scanned_mono outgoing state.seen _ after_mono other (valid.cursor other (by simp [stack, old]))
      have closed : ∀ vertex ∈ state.finished, ∀ child, Edge outgoing vertex child →
          (tick outgoing state).seen child = true := by
        intro vertex member child edge
        exact after_mono child (valid.closed vertex member child edge)
      refine ⟨tick_preserves outgoing state valid.base, ?_, ?_⟩
      · intro other member
        cases target with
        | none =>
          have old : other ∈ (trim state).stack := by simpa [tick, stack, todo] using member
          exact trimmed_cursor other old
        | some child =>
          cases visited : (trim state).seen child with
          | true =>
            have old : other ∈ (trim state).stack := by simpa [tick, stack, todo, discover, visited] using member
            exact trimmed_cursor other old
          | false =>
            have cases_member : other = ⟨child, outgoing child⟩ ∨ other ∈ (trim state).stack := by
              simpa [tick, stack, todo, discover, visited] using member
            rcases cases_member with rfl | old
            · exact ⟨[], by simp, by simp⟩
            · exact trimmed_cursor other old
      · intro vertex member child edge
        have old : vertex ∈ state.finished := by
          cases target with
          | none => simpa [tick, stack, todo, trim] using member
          | some target =>
            simpa [tick, stack, todo, discover_finished, trim_finished] using member
        exact closed vertex old child edge

theorem walk_scanned (outgoing : V → List (Option V)) (fuel : Nat) (state : State V)
    (valid : ScanInvariant outgoing state) : ScanInvariant outgoing (walk outgoing fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases stack : state.stack with
    | nil => simpa [walk, stack] using valid
    | cons frame rest => simpa only [walk, stack] using ih _ (tick_scanned outgoing state valid)

omit [DecidableEq V] in
/-- 活動中フレームがない時点では、訪問済み集合は元の内部辺に関して閉じる。 -/
theorem seen_closed (outgoing : V → List (Option V)) (state : State V)
    (valid : ScanInvariant outgoing state) (empty : state.stack = [])
    (source target : V) (seen : state.seen source = true) (edge : Edge outgoing source target) :
    state.seen target = true := by
  have member := (valid.base.covers source).mp seen
  have finished : source ∈ state.finished := by simpa [State.total, State.active, empty] using member
  exact valid.closed source finished target edge

omit [DecidableEq V] in
theorem seen_reachable (outgoing : V → List (Option V)) (state : State V)
    (valid : ScanInvariant outgoing state) (empty : state.stack = [])
    {source target : V} (walk : Walk (Edge outgoing) source target) :
    state.seen source = true → state.seen target = true := by
  induction walk with
  | nil => exact id
  | cons edge _ ih =>
    intro seen
    exact ih (seen_closed outgoing state valid empty _ _ seen edge)

end PetaProof.ForwardDfs
