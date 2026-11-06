import PetaProof.GeneratedStratumFamily
import PetaProof.CoreEnumeration

/-! phaseごとの全状態を記録せず、要求した頂点の順位だけを固定長配列へ保存する。
順位の生成器の費用は含めず、取得・保存の側の不変条件を扱う。 -/
namespace PetaProof.SelectiveRankCapture

universe u v
variable {n : Nat} {K : Type u} {S : Type v}

def capture (read : Fin n → Nat) : List (Fin n) → Array (Option Nat) → Array (Option Nat)
  | [], slots => slots
  | vertex :: rest, slots => capture read rest (slots.setIfInBounds vertex.val (some (read vertex)))

theorem capture_size (read : Fin n → Nat) (vertices : List (Fin n)) (slots : Array (Option Nat)) :
    (capture read vertices slots).size = slots.size := by
  induction vertices generalizing slots with
  | nil => rfl
  | cons vertex rest ih => simp only [capture, ih, Array.size_setIfInBounds]

theorem capture_get (read : Fin n → Nat) (vertices : List (Fin n)) (slots : Array (Option Nat))
    (space : slots.size = n) (vertex : Fin n) :
    (capture read vertices slots)[vertex.val]? =
      if vertex ∈ vertices then some (some (read vertex)) else slots[vertex.val]? := by
  induction vertices generalizing slots with
  | nil => simp [capture]
  | cons head rest ih =>
    rw [capture, ih _ (by simpa only [Array.size_setIfInBounds] using space)]
    by_cases later : vertex ∈ rest
    · simp [later]
    · by_cases same : vertex = head
      · subst head
        have valid : vertex.val < slots.size := by omega
        simp [later, Array.getElem?_setIfInBounds, valid]
      · have different : head.val ≠ vertex.val := by intro equal; exact same (Fin.ext equal.symm)
        simp [later, same, Array.getElem?_setIfInBounds, different, Ne.symm different]

/-- payloadは今回のphaseの状態から読む。過去のpayload列・状態列を返却値へ含めない。 -/
def run (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat) :
    List K → S → Array (Option Nat) → S × Array (Option Nat)
  | [], state, slots => (state, slots)
  | key :: rest, state, slots =>
    let next := step key state
    run step requests payload rest next (capture (payload key next) (requests key) slots)

theorem run_state (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (levels : List K) (state : S) (slots : Array (Option Nat)) :
    (run step requests payload levels state slots).1 = levels.foldl (fun state key => step key state) state := by
  induction levels generalizing state slots with
  | nil => rfl
  | cons key rest ih => exact ih _ _

theorem run_size (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (levels : List K) (state : S) (slots : Array (Option Nat)) :
    (run step requests payload levels state slots).2.size = slots.size := by
  induction levels generalizing state slots with
  | nil => rfl
  | cons key rest ih => simp only [run, ih, capture_size]

/-- 現在状態の不変条件と今回の要求への値の一致だけで、保存結果を特定できる。 -/
theorem run_get (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (good : S → Prop) (expected : Fin n → Nat)
    (preserved : ∀ key state, good state → good (step key state))
    (correct : ∀ key state, good state → ∀ vertex, vertex ∈ requests key →
      payload key (step key state) vertex = expected vertex)
    (levels : List K) (state : S) (valid : good state) (slots : Array (Option Nat)) (space : slots.size = n)
    (vertex : Fin n) :
    (run step requests payload levels state slots).2[vertex.val]? =
      if vertex ∈ levels.flatMap requests then some (some (expected vertex)) else slots[vertex.val]? := by
  induction levels generalizing state slots with
  | nil => simp [run]
  | cons key rest ih =>
    rw [run, ih _ (preserved key state valid) _ (by simpa only [capture_size] using space),
      capture_get _ _ _ space]
    by_cases later : vertex ∈ rest.flatMap requests
    · simp [later]
    · by_cases current : vertex ∈ requests key
      · simp [later, current, correct key state valid vertex current]
      · simp [later, current]

/-- 同じ頂点を一回だけ要求すれば、順位参照・格納は頂点数以下。 -/
theorem requests_bound [DecidableEq K] (levels : List K) (requests : K → List (Fin n))
    (unique : (levels.flatMap requests).Nodup) :
    (levels.flatMap requests).length ≤ n := by
  have bound := DistinctWork.length_le (levels.flatMap requests) (List.finRange n) unique
    (fun vertex _ => CoreEnumeration.finRange_covers n vertex)
  simpa using bound

/-- 頂点ごとに保存するphaseを一つだけ指定すれば、全phaseを通じても重複しない。 -/
theorem routed_unique (levels : List K) (requests : K → List (Fin n)) (target : Fin n → Option K)
    (unique : levels.Nodup) (rowsUnique : ∀ key, (requests key).Nodup)
    (routed : ∀ key vertex, vertex ∈ requests key → target vertex = some key) :
    (levels.flatMap requests).Nodup := by
  induction levels with
  | nil => exact List.Pairwise.nil
  | cons key rest ih =>
    have parts := List.nodup_cons.mp unique
    change List.Pairwise (fun a b => a ≠ b) (requests key ++ rest.flatMap requests)
    apply List.pairwise_append.mpr
    refine ⟨rowsUnique key, ih parts.2, ?_⟩
    intro first present second later same
    subst second
    obtain ⟨other, member, inRow⟩ := List.mem_flatMap.mp later
    have one := routed key first present
    have two := routed other first inRow
    have equal : key = other := Option.some.inj (one.symm.trans two)
    exact parts.1 (equal ▸ member)

def reads (levels : List K) (requests : K → List (Fin n)) : Nat :=
  (levels.map (fun key => (requests key).length)).sum

theorem reads_exact (levels : List K) (requests : K → List (Fin n)) :
    reads levels requests = (levels.flatMap requests).length := by
  induction levels with
  | nil => rfl
  | cons key rest ih => simp only [reads, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append] at *; omega

theorem reads_bound [DecidableEq K] (levels : List K) (requests : K → List (Fin n))
    (target : Fin n → Option K) (unique : levels.Nodup) (rowsUnique : ∀ key, (requests key).Nodup)
    (routed : ∀ key vertex, vertex ∈ requests key → target vertex = some key) : reads levels requests ≤ n := by
  rw [reads_exact]
  exact requests_bound levels requests (routed_unique levels requests target unique rowsUnique routed)

def storedRank (slots : Array (Option Nat)) (vertex : Fin n) : Nat :=
  ((slots[vertex.val]?).getD none).getD 0

/-- 取得要求がない頂点は既定順位0でよいとき、最終のN要素だけで全順位を復元できる。 -/
theorem run_complete (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (good : S → Prop) (expected : Fin n → Nat)
    (preserved : ∀ key state, good state → good (step key state))
    (correct : ∀ key state, good state → ∀ vertex, vertex ∈ requests key →
      payload key (step key state) vertex = expected vertex)
    (levels : List K) (state : S) (valid : good state)
    (covered : ∀ vertex, vertex ∈ levels.flatMap requests ∨ expected vertex = 0) (vertex : Fin n) :
    storedRank (run step requests payload levels state (Array.replicate n none)).2 vertex = expected vertex := by
  have get := run_get step requests payload good expected preserved correct levels state valid
    (Array.replicate n none) (by simp) vertex
  unfold storedRank
  rw [get]
  by_cases present : vertex ∈ levels.flatMap requests
  · simp [present]
  · have zero := (covered vertex).resolve_left present
    have within : vertex.val < n := vertex.isLt
    simp [present, Array.getElem?_eq_getElem, within, zero]

end PetaProof.SelectiveRankCapture
