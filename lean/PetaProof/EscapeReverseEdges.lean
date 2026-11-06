import PetaProof.EscapeFifo

/-! pop済み頂点から元辺IDを列挙する。経路ではなく、各子の逆辺表だけを一度読む。 -/
namespace PetaProof.EscapeReverseEdges

universe u v
variable {V : Type u} {E : Type v} [DecidableEq E]

structure Input (V : Type u) (E : Type v) where
  child : E → V
  incoming : V → List E
  incoming_correct : ∀ vertex edge, edge ∈ incoming vertex ↔ child edge = vertex
  incoming_unique : ∀ vertex, (incoming vertex).Nodup

namespace Input
variable (input : Input V E)

def notifications (popped : List V) : List E := popped.flatMap input.incoming

omit [DecidableEq E] in
theorem notifications_complete (popped : List V) (edge : E) :
    edge ∈ input.notifications popped ↔ input.child edge ∈ popped := by
  simp only [notifications, List.mem_flatMap, input.incoming_correct]
  constructor
  · rintro ⟨vertex, member, same⟩
    exact same ▸ member
  · intro member
    exact ⟨input.child edge, member, rfl⟩

omit [DecidableEq E] in
/-- 子が異なれば元辺IDも異なる。同じ子への別の元辺は消さない。 -/
theorem notifications_unique (popped : List V) (unique : popped.Nodup) :
    (input.notifications popped).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun vertex _ => input.incoming_unique vertex, ?_⟩
  apply List.Pairwise.imp ?_ unique
  intro first second different edge inFirst other inSecond equal
  have left := (input.incoming_correct first edge).mp inFirst
  have right := (input.incoming_correct second other).mp inSecond
  subst other
  exact different (left.symm.trans right)

def markAll (seen : E → Bool) : List E → E → Bool
  | [] => seen
  | edge :: rest => markAll (markSeen seen edge) rest

theorem markAll_spec (seen : E → Bool) (edges : List E) (edge : E) :
    markAll seen edges edge = true ↔ edge ∈ edges ∨ seen edge = true := by
  induction edges generalizing seen with
  | nil => simp [markAll]
  | cons head rest ih =>
    rw [markAll, ih, markSeen_true_iff]
    simp only [List.mem_cons]
    simp only [or_left_comm, or_assoc]

/-- 実際の全逆辺走査から、通知履歴とpop済み集合の一致を得る。 -/
theorem scan_complete (popped : List V) (edge : E) :
    markAll (fun _ => false) (input.notifications popped) edge = true ↔ input.child edge ∈ popped := by
  simp [markAll_spec, input.notifications_complete]

private theorem count_lt_two (items : List E) (unique : items.Nodup) (edge : E) :
    items.count edge < 2 := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = edge
    · subst head
      simp [List.count_cons, List.count_eq_zero_of_not_mem parts.1]
    · simpa [List.count_cons, same, Ne.symm same] using ih parts.2

/-- popする子が重複しなければ、総通知数は全元辺数以下である。 -/
theorem notification_count_bound (popped : List V) (unique : popped.Nodup)
    (edges : List E) (covered : ∀ edge, edge ∈ edges) :
    (input.notifications popped).length ≤ edges.length := by
  have bound := history_length_bound edges (input.notifications popped) 2
    (fun edge _ => covered edge) (fun edge _ => count_lt_two _ (input.notifications_unique popped unique) edge)
  simpa using bound

/-- FIFOの投入不変条件から、そのpop履歴に対する総辺通知上界へ直接接続する。 -/
theorem fifo_notification_count_bound (state : EscapeFifo.State V) (inv : EscapeFifo.Invariant state)
    (edges : List E) (covered : ∀ edge, edge ∈ edges) :
    (input.notifications (state.popped.map Prod.fst)).length ≤ edges.length := by
  have unique : ((state.popped.map Prod.fst) ++ (state.pending.map Prod.fst)).Nodup := by
    simpa only [EscapeFifo.State.total, List.map_append] using inv.unique
  exact input.notification_count_bound _ (List.pairwise_append.mp unique).1 edges covered

end Input
end PetaProof.EscapeReverseEdges
