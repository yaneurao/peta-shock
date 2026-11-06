import PetaProof.HitCounter

/-!
admitの確定済みガードとFIFOキューの影のモデル。
poppedは証明用の取り出し履歴であり、本番へ履歴配列を追加しない。
-/
namespace PetaProof

universe u
variable {V : Type u} [DecidableEq V]

theorem markSeen_true_iff (seen : V → Bool) (edge other : V) :
    markSeen seen edge other = true ↔ other = edge ∨ seen other = true := by
  by_cases same : other = edge <;> simp [markSeen, same]

omit [DecidableEq V] in
theorem nodup_append_fresh (vertices : List V) (unique : vertices.Nodup)
    (v : V) (fresh : v ∉ vertices) : (vertices ++ [v]).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨unique, by simp, ?_⟩
  intro a member b singleton same
  have last : b = v := by simpa using singleton
  have equal : a = v := same.trans last
  exact fresh (equal ▸ member)

structure AdmissionQueue (V : Type u) where
  admitted : V → Bool
  popped : List V
  pending : List V

namespace AdmissionQueue

def total (queue : AdmissionQueue V) : List V := queue.popped ++ queue.pending

def initial : AdmissionQueue V := ⟨fun _ => false, [], []⟩

def admit (queue : AdmissionQueue V) (v : V) : AdmissionQueue V :=
  if queue.admitted v then queue else {
    admitted := markSeen queue.admitted v
    popped := queue.popped
    pending := queue.pending ++ [v]
  }

/-- 本番のpop_frontに対応する。辺の通知完了は、この関数だけでは主張しない。 -/
def pop (queue : AdmissionQueue V) : AdmissionQueue V :=
  match queue.pending with
  | [] => queue
  | v :: rest => { queue with popped := queue.popped ++ [v], pending := rest }

structure Invariant (queue : AdmissionQueue V) : Prop where
  unique : queue.total.Nodup
  covers : ∀ v, queue.admitted v = true ↔ v ∈ queue.total

omit [DecidableEq V] in
theorem initial_invariant : Invariant (initial : AdmissionQueue V) := by
  constructor
  · exact List.nodup_nil
  · intro v
    simp [initial, total]

/-- 確定済み頂点を再度積まないため、取り出し済みの頂点も含めて重複が増えない。 -/
theorem admit_preserves (queue : AdmissionQueue V) (invariant : Invariant queue) (v : V) :
    Invariant (admit queue v) := by
  cases admitted : queue.admitted v with
  | true => simpa only [admit, admitted, ite_true] using invariant
  | false =>
    have fresh : v ∉ queue.total := by
      intro member
      have seen := (invariant.covers v).mpr member
      rw [admitted] at seen
      cases seen
    simp only [admit, admitted, Bool.false_eq_true, ite_false]
    constructor
    · simpa only [total, List.append_assoc] using nodup_append_fresh queue.total invariant.unique v fresh
    · intro w
      change markSeen queue.admitted v w = true ↔ w ∈ queue.popped ++ (queue.pending ++ [v])
      rw [← List.append_assoc]
      change markSeen queue.admitted v w = true ↔ w ∈ queue.total ++ [v]
      rw [markSeen_true_iff, List.mem_append, List.mem_singleton, ← invariant.covers w]
      exact or_comm

omit [DecidableEq V] in
theorem pop_total (queue : AdmissionQueue V) : (pop queue).total = queue.total := by
  cases pending : queue.pending with
  | nil => simp [pop, pending]
  | cons v rest => simp [pop, pending, total, List.append_assoc]

omit [DecidableEq V] in
theorem pop_admitted (queue : AdmissionQueue V) : (pop queue).admitted = queue.admitted := by
  cases pending : queue.pending <;> simp [pop, pending]

omit [DecidableEq V] in
theorem pop_preserves (queue : AdmissionQueue V) (invariant : Invariant queue) : Invariant (pop queue) := by
  constructor
  · rw [pop_total]
    exact invariant.unique
  · intro v
    rw [pop_admitted, pop_total]
    exact invariant.covers v

omit [DecidableEq V] in
theorem popped_unique (queue : AdmissionQueue V) (invariant : Invariant queue) : queue.popped.Nodup :=
  (List.pairwise_append.mp invariant.unique).1

theorem cannot_readmit_popped (queue : AdmissionQueue V) (invariant : Invariant queue)
    (v : V) (popped : v ∈ queue.popped) : admit queue v = queue := by
  have admitted := (invariant.covers v).mpr (by simp [total, popped])
  simp only [admit, admitted, ite_true]

omit [DecidableEq V] in
/-- キューが空なら、確定済み頂点は全て取り出し済みである。 -/
theorem drained_iff_popped (queue : AdmissionQueue V) (invariant : Invariant queue)
    (empty : queue.pending = []) (v : V) : queue.admitted v = true ↔ v ∈ queue.popped := by
  simpa only [total, empty, List.append_nil] using invariant.covers v

/-- admitとpopを任意に繰り返した、実行可能なキュー状態。 -/
inductive Reachable : AdmissionQueue V → Prop
  | initial : Reachable initial
  | admit {queue : AdmissionQueue V} : Reachable queue → (v : V) → Reachable (AdmissionQueue.admit queue v)
  | pop {queue : AdmissionQueue V} : Reachable queue → Reachable (AdmissionQueue.pop queue)

theorem Reachable.invariant {queue : AdmissionQueue V} (run : Reachable queue) : Invariant queue := by
  induction run with
  | initial => exact initial_invariant
  | admit _ v ih => exact admit_preserves _ ih v
  | pop _ ih => exact pop_preserves _ ih

end AdmissionQueue
end PetaProof
