import PetaProof.AdmissionQueue

/-!
leaf評価値ごとの通知と、取り出した子頂点ごとの逆辺通知を互いに素なバッチとして扱う。
辺を子頂点で重複除去せず、入力の辺IDをそのまま列挙する。
-/
namespace PetaProof

universe u v w
variable {E : Type u} {K : Type v} [DecidableEq K]

def notificationBatch (edges : List E) (key : E → K) (current : K) : List E :=
  edges.filter (fun edge => key edge == current)

def notificationTrace (edges : List E) (key : E → K) : List K → List E
  | [] => []
  | current :: rest => notificationBatch edges key current ++ notificationTrace edges key rest

theorem mem_notificationBatch (edges : List E) (key : E → K) (current : K) (edge : E) :
    edge ∈ notificationBatch edges key current ↔ edge ∈ edges ∧ key edge = current := by
  simp only [notificationBatch, List.mem_filter, beq_iff_eq]

/-- 各バッチの列挙が全辺を漏れなく含むことも、重複しないこととは別に保証する。 -/
theorem mem_notificationTrace (edges : List E) (key : E → K) (keys : List K) (edge : E) :
    edge ∈ notificationTrace edges key keys ↔ edge ∈ edges ∧ key edge ∈ keys := by
  induction keys with
  | nil => simp [notificationTrace]
  | cons current rest ih =>
    rw [notificationTrace, List.mem_append, mem_notificationBatch, ih, List.mem_cons]
    constructor
    · rintro (⟨member, same⟩ | ⟨member, present⟩)
      · exact ⟨member, Or.inl same⟩
      · exact ⟨member, Or.inr present⟩
    · rintro ⟨member, same | present⟩
      · exact Or.inl ⟨member, same⟩
      · exact Or.inr ⟨member, present⟩

/-- バッチのキーが未使用なら、そのバッチの辺は過去に通知されていない。 -/
theorem notificationBatch_fresh (edges : List E) (key : E → K) (keys : List K)
    (current : K) (fresh : current ∉ keys) (edge : E) (member : edge ∈ notificationBatch edges key current) :
    edge ∉ notificationTrace edges key keys := by
  intro previous
  have same := ((mem_notificationBatch edges key current edge).mp member).2
  have earlier := ((mem_notificationTrace edges key keys edge).mp previous).2
  exact fresh (same ▸ earlier)

theorem notificationTrace_unique (edges : List E) (key : E → K) (keys : List K)
    (edges_unique : edges.Nodup) (keys_unique : keys.Nodup) :
    (notificationTrace edges key keys).Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons current rest ih =>
    have nodup := List.nodup_cons.mp keys_unique
    apply List.pairwise_append.mpr
    refine ⟨edges_unique.filter _, ih nodup.2, ?_⟩
    intro a member b earlier same
    have fresh := notificationBatch_fresh edges key rest current nodup.1 a member
    exact fresh (same ▸ earlier)

end PetaProof

namespace PetaProof

universe u v
variable {A : Type u} {B : Type v}

/-- Sum.inlはleaf閾値の通知、Sum.inrは子頂点の取り出しによる通知として使う。 -/
def leafKeys : List (Sum A B) → List A
  | [] => []
  | .inl value :: rest => value :: leafKeys rest
  | .inr _ :: rest => leafKeys rest

def nodeKeys : List (Sum A B) → List B
  | [] => []
  | .inl _ :: rest => nodeKeys rest
  | .inr value :: rest => value :: nodeKeys rest

theorem mem_leafKeys (keys : List (Sum A B)) (value : A) : value ∈ leafKeys keys ↔ .inl value ∈ keys := by
  induction keys with
  | nil => simp [leafKeys]
  | cons current rest ih => cases current <;> simp [leafKeys, ih]

theorem mem_nodeKeys (keys : List (Sum A B)) (value : B) : value ∈ nodeKeys keys ↔ .inr value ∈ keys := by
  induction keys with
  | nil => simp [nodeKeys]
  | cons current rest ih => cases current <;> simp [nodeKeys, ih]

/-- leaf通知と頂点通知を任意に交互実行しても、各種類が一意ならキー全体も一意。 -/
theorem keys_unique_of_projections (keys : List (Sum A B))
    (leaves_unique : (leafKeys keys).Nodup) (nodes_unique : (nodeKeys keys).Nodup) : keys.Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons current rest ih =>
    cases current with
    | inl value =>
      have leaves := List.nodup_cons.mp leaves_unique
      apply List.nodup_cons.mpr
      exact ⟨fun member => leaves.1 ((mem_leafKeys rest value).mpr member), ih leaves.2 nodes_unique⟩
    | inr value =>
      have nodes := List.nodup_cons.mp nodes_unique
      apply List.nodup_cons.mpr
      exact ⟨fun member => nodes.1 ((mem_nodeKeys rest value).mpr member), ih leaves_unique nodes.2⟩

/-- 降順のleaf閾値列と一度だけ取り出すキューから、辺の通知全体の一意性を導く。 -/
theorem notifications_unique_from_queue_levels {V : Type u} {E : Type v} [DecidableEq V]
    (edges : List E) (edges_unique : edges.Nodup) (key : E → Sum Int V)
    (keys : List (Sum Int V)) (levels : List Int) (descending : levels.Pairwise (fun a b => b < a))
    (queue : AdmissionQueue V) (queue_invariant : queue.Invariant)
    (leaves : leafKeys keys = levels) (nodes : nodeKeys keys = queue.popped) :
    (notificationTrace edges key keys).Nodup := by
  have level_unique : levels.Nodup := descending.imp (by intro a b less same; omega)
  have key_unique := keys_unique_of_projections keys
    (by simpa only [leaves] using level_unique)
    (by simpa only [nodes] using AdmissionQueue.popped_unique queue queue_invariant)
  exact notificationTrace_unique edges key keys edges_unique key_unique

end PetaProof
