import PetaProof.LinearCycleFlags

/-! 行のfilter・mapと短絡anyの結果およびイベント数を同時に計算する。 -/
namespace PetaProof.CountedRowOps

universe u v
variable {A : Type u} {B : Type v}

def filter (allow : A → Bool) : List A → List A × Nat
  | [] => ([], 0)
  | item :: rest =>
    let next := filter allow rest
    if allow item then (item :: next.1, next.2 + 2) else (next.1, next.2 + 1)

theorem filter_spec (allow : A → Bool) (items : List A) :
    (filter allow items).1 = items.filter allow ∧
      (filter allow items).2 = items.length + (items.filter allow).length := by
  induction items with
  | nil => exact ⟨rfl, rfl⟩
  | cons item rest ih =>
    cases permitted : allow item <;>
      simp [filter, permitted, ih.1, ih.2, List.filter_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def map (source : A → B) : List A → List B × Nat
  | [] => ([], 0)
  | item :: rest =>
    let next := map source rest
    (source item :: next.1, next.2 + 2)

theorem map_spec (source : A → B) (items : List A) :
    (map source items).1 = items.map source ∧ (map source items).2 = 2 * items.length := by
  induction items with
  | nil => exact ⟨rfl, rfl⟩
  | cons item rest ih =>
    simp [map, ih.1, ih.2, Nat.mul_add, Nat.add_comm]

/-- filterで各項目を検査し、残した項目をmapする。捨てる項目も費用に含む。 -/
def select (allow : A → Bool) (source : A → B) (items : List A) : List B × Nat :=
  let selected := filter allow items
  let mapped := map source selected.1
  (mapped.1, selected.2 + mapped.2)

theorem select_spec (allow : A → Bool) (source : A → B) (items : List A) :
    (select allow source items).1 = (items.filter allow).map source ∧
      (select allow source items).2 = items.length + 3 * (items.filter allow).length := by
  have filtered := filter_spec allow items
  have mapped := map_spec source (filter allow items).1
  rw [filtered.1] at mapped
  simp only [select, mapped.1, mapped.2, filtered.1, filtered.2]
  constructor
  · trivial
  · omega

/-- 最初の成功で停止する。検査数は走査しなかったsuffixを含めない。 -/
def any (predicate : A → Bool) : List A → Bool × Nat
  | [] => (false, 0)
  | item :: rest =>
    if predicate item then (true, 1) else
      let next := any predicate rest
      (next.1, next.2 + 1)

theorem any_spec (predicate : A → Bool) (items : List A) :
    (any predicate items).1 = items.any predicate ∧ (any predicate items).2 ≤ items.length := by
  induction items with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons item rest ih =>
    cases found : predicate item <;> simp [any, found, ih.1, ih.2]

theorem sum_linear (vertices : List A) (left right : A → Nat) :
    (vertices.map (fun vertex => left vertex + 3 * right vertex)).sum =
      (vertices.map left).sum + 3 * (vertices.map right).sum := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
    simp only [List.map_cons, List.sum_cons] at *
    omega

theorem sum_mono (vertices : List A) (left right : A → Nat)
    (bound : ∀ vertex, left vertex ≤ right vertex) :
    (vertices.map left).sum ≤ (vertices.map right).sum := by
  induction vertices with
  | nil => exact Nat.le_refl _
  | cons vertex rest ih =>
    have head := bound vertex
    simp only [List.map_cons, List.sum_cons]
    omega

end PetaProof.CountedRowOps

namespace PetaProof.LinearCycleFlags

universe u
variable {V : Type u}

/-- 自己辺probeを一頂点につき一度だけ実行して、その検査費用も集計する。 -/
def scanCharged (component : V → Nat) (probe : V → Bool × Nat) :
    List V → State → State × Nat
  | [], state => (state, 0)
  | vertex :: rest, state =>
    let checked := probe vertex
    let next := scanCharged component probe rest (add component (fun _ => checked.1) state vertex)
    (next.1, checked.2 + next.2)

theorem scanCharged_spec (component : V → Nat) (probe : V → Bool × Nat)
    (vertices : List V) (state : State) :
    (scanCharged component probe vertices state).1 = scan component (fun vertex => (probe vertex).1) vertices state ∧
      (scanCharged component probe vertices state).2 = (vertices.map (fun vertex => (probe vertex).2)).sum := by
  induction vertices generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons vertex rest ih =>
    have same : add component (fun _ => (probe vertex).1) state vertex =
        add component (fun vertex => (probe vertex).1) state vertex := rfl
    simp [scanCharged, same, ih, scan]

end PetaProof.LinearCycleFlags
