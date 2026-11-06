import PetaProof.EscapeStopped

/-! 目標0とnone側の二条件だけで、未確定結果に有限手数の脱出保証がないと分かる。 -/
namespace PetaProof.HistoryArena

universe u
variable {V : Type u} {A : HistoryArena V} {target : V → Prop}

structure EscapeNoneCertificate (A : HistoryArena V) (target : V → Prop) (labels : V → Option Nat) : Prop where
  goals : ∀ vertex, target vertex → labels vertex ≠ none
  own : ∀ vertex, A.owner vertex = A.player → labels vertex = none →
    ∀ child, A.edge vertex child → labels child = none
  other : ∀ vertex, A.owner vertex ≠ A.player → labels vertex = none →
    ∃ child, A.edge vertex child ∧ labels child = none

namespace EscapeNoneCertificate
variable {labels : V → Option Nat} (certificate : EscapeNoneCertificate A target labels)
include certificate

theorem layer_not_none (bound : Nat) (vertex : V) (inside : A.escapeLayer target bound vertex) :
    labels vertex ≠ none := by
  induction bound generalizing vertex with
  | zero => exact certificate.goals vertex inside
  | succ bound ih =>
    rcases inside with goal | step
    · exact certificate.goals vertex goal
    · intro unresolved
      by_cases own : A.owner vertex = A.player
      · rw [if_pos own] at step
        obtain ⟨child, edge, childInside⟩ := step
        exact ih child childInside (certificate.own vertex own unresolved child edge)
      · rw [if_neg own] at step
        obtain ⟨child, edge, childNone⟩ := certificate.other vertex own unresolved
        exact ih child (step child edge) childNone

theorem none_outside (vertex : V) (unresolved : labels vertex = none) (bound : Nat) :
    ¬ A.escapeLayer target bound vertex := fun inside => certificate.layer_not_none bound vertex inside unresolved

theorem none_no_guarantee (vertex : V) (unresolved : labels vertex = none)
    (strategy : A.Strategy) (past : List V) (bound : Nat) : ¬ A.escapeWithin target strategy past bound vertex :=
  fun guaranteed => certificate.none_outside vertex unresolved bound
    (A.escapeWithin_layer target strategy past bound vertex guaranteed)

end EscapeNoneCertificate
end PetaProof.HistoryArena

namespace PetaProof.EscapePropagation

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/-- 辺IDの入力と、到達ゲームの局面・手番・指し手が同じグラフを表す条件。 -/
structure ArenaMatch (input : Input V E) (arena : HistoryArena V) : Prop where
  edges : ∀ vertex child, arena.edge vertex child ↔
    ∃ edge ∈ input.outgoing vertex, input.child edge = child
  owner : ∀ vertex, input.own vertex = true ↔ arena.owner vertex = arena.player

namespace State
variable (input : Input V E) {arena : HistoryArena V} {target : V → Prop}

theorem runLabels_none_certificate (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices) :
    HistoryArena.EscapeNoneCertificate arena target (runLabels input goals vertices) := by
  constructor
  · intro vertex goal unresolved
    have zero := runLabels_goal_zero input goals vertices vertex ((goals_correct vertex).mp goal)
    rw [zero] at unresolved
    cases unresolved
  · intro vertex own pending child edge
    obtain ⟨move, member, same⟩ := (matching.edges vertex child).mp edge
    have absent := runLabels_own_infinite input goals vertices covered vertex
      ((matching.owner vertex).mpr own) pending move member
    simpa only [same] using absent
  · intro vertex _ pending
    obtain ⟨move, member, absent⟩ := runLabels_other_infinite input goals vertices covered vertex pending
    exact ⟨input.child move, (matching.edges vertex (input.child move)).mpr ⟨move, member, rfl⟩, absent⟩

theorem runLabels_none_no_guarantee (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (unresolved : runLabels input goals vertices vertex = none)
    (strategy : arena.Strategy) (past : List V) (bound : Nat) :
    ¬ arena.escapeWithin target strategy past bound vertex :=
  (runLabels_none_certificate input matching goals vertices goals_correct covered).none_no_guarantee
    vertex unresolved strategy past bound

/-- 出力noneの局面には、同じ履歴不要応手で目標を避け続ける相手方策がある。 -/
theorem runLabels_none_spoiler (matching : ArenaMatch input arena) (goals vertices : List V)
    (goals_correct : ∀ vertex, target vertex ↔ vertex ∈ goals) (covered : ∀ vertex, vertex ∈ vertices)
    (vertex : V) (unresolved : runLabels input goals vertices vertex = none)
    (strategy : arena.Strategy) (bound : Nat) :
    ¬ target (arena.play strategy (arena.escapeSpoiler target vertices covered) vertex bound) :=
  arena.escapeSpoiler_avoids target vertices covered vertex
    ((runLabels_none_certificate input matching goals vertices goals_correct covered).none_outside
      vertex unresolved vertices.length) strategy bound

end State
end PetaProof.EscapePropagation
