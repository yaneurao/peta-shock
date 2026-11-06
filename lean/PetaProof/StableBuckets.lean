import PetaProof.LocalPreparationAccounting

/-! 互いに素な選択条件を、一回の入力走査で安定なバケットへ分配する。 -/
namespace PetaProof.StableBuckets

universe u
variable {E : Type u}

/-- 最初に該当するバケット番号。どれにも該当しない入力は捨てる。 -/
def route : List (E → Bool) → E → Option Nat
  | [], _ => none
  | select :: rest, edge => if select edge then some 0 else (route rest edge).map Nat.succ

def Disjoint (selectors : List (E → Bool)) : Prop :=
  selectors.Pairwise (fun first second => ∀ edge, first edge = true → second edge = false)

theorem route_member (selectors : List (E → Bool)) (edge : E) (key : Nat)
    (found : route selectors edge = some key) : ∃ select ∈ selectors, select edge = true := by
  induction selectors generalizing key with
  | nil => cases found
  | cons select rest ih =>
    cases active : select edge with
    | true => exact ⟨select, by simp, active⟩
    | false =>
      cases tailKey : route rest edge with
      | none => simp [route, active, tailKey] at found
      | some next =>
        obtain ⟨other, member, yes⟩ := ih next tailKey
        exact ⟨other, by simp [member], yes⟩

theorem route_tail (select : E → Bool) (rest : List (E → Bool)) (disjoint : Disjoint (select :: rest))
    (edge : E) (key : Nat) :
    route (select :: rest) edge = some (key + 1) ↔ route rest edge = some key := by
  cases active : select edge with
  | false =>
    cases next : route rest edge <;> simp [route, active, next]
  | true =>
    have absent : route rest edge ≠ some key := by
      intro found
      obtain ⟨other, member, yes⟩ := route_member rest edge key found
      have no := List.rel_of_pairwise_cons disjoint member edge active
      rw [yes] at no
      cases no
    simp [route, active, absent]

def put (selectors : List (E → Bool)) (buckets : Nat → List E) (edge : E) : Nat → List E :=
  match route selectors edge with
  | none => buckets
  | some key => fun current => if current = key then buckets current ++ [edge] else buckets current

def build (selectors : List (E → Bool)) : List E → (Nat → List E) → (Nat → List E)
  | [], buckets => buckets
  | edge :: rest, buckets => build selectors rest (put selectors buckets edge)

theorem build_spec (selectors : List (E → Bool)) (edges : List E) (buckets : Nat → List E) (key : Nat) :
    build selectors edges buckets key = buckets key ++
      edges.filter (fun edge => decide (route selectors edge = some key)) := by
  induction edges generalizing buckets with
  | nil => simp [build]
  | cons edge rest ih =>
    rw [build, ih]
    cases found : route selectors edge with
    | none => simp [put, found]
    | some next =>
      by_cases same : key = next
      · subst next
        simp [put, found, List.append_assoc]
      · have different := Ne.symm same
        simp [put, found, same, different]

def table (selectors : List (E → Bool)) (edges : List E) : Nat → List E :=
  build selectors edges (fun _ => [])

/-- キーを表参照等で与える分配器。条件列の線形探索を分配ループへ要求しない。 -/
def putKey (key : E → Option Nat) (buckets : Nat → List E) (edge : E) : Nat → List E :=
  match key edge with
  | none => buckets
  | some index => fun current => if current = index then buckets current ++ [edge] else buckets current

def buildKey (key : E → Option Nat) : List E → (Nat → List E) → (Nat → List E)
  | [], buckets => buckets
  | edge :: rest, buckets => buildKey key rest (putKey key buckets edge)

theorem buildKey_correct (selectors : List (E → Bool)) (key : E → Option Nat)
    (correct : ∀ edge, key edge = route selectors edge) (edges : List E) (buckets : Nat → List E) :
    buildKey key edges buckets = build selectors edges buckets := by
  have equal : key = route selectors := funext correct
  subst key
  induction edges generalizing buckets with
  | nil => rfl
  | cons edge rest ih => simpa only [buildKey, build, putKey, put] using ih (put selectors buckets edge)

/-- キー計算そのものは含めず、非空キー一件につき登録一回を数える。 -/
def registrations (key : E → Option Nat) : List E → Nat
  | [] => 0
  | edge :: rest => (if (key edge).isSome then 1 else 0) + registrations key rest

theorem registrations_bound (key : E → Option Nat) (edges : List E) :
    registrations key edges ≤ edges.length := by
  induction edges with
  | nil => simp [registrations]
  | cons edge rest ih =>
    cases found : key edge <;> simp [registrations, found] <;> omega

theorem table_head (select : E → Bool) (rest : List (E → Bool)) (edges : List E) :
    table (select :: rest) edges 0 = edges.filter select := by
  rw [table, build_spec]
  simp only [List.nil_append]
  congr 1
  funext edge
  cases active : select edge with
  | true => simp [route, active]
  | false => cases tailKey : route rest edge <;> simp [route, active, tailKey]

theorem table_tail (select : E → Bool) (rest : List (E → Bool)) (edges : List E)
    (disjoint : Disjoint (select :: rest)) :
    (fun key => table (select :: rest) edges (key + 1)) = table rest edges := by
  funext key
  simp only [table, build_spec, List.nil_append]
  congr 1
  funext edge
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using route_tail select rest disjoint edge key

/-- 構築済み表の次の行へ進むだけで、入力辺を再走査しない。 -/
def collect : Nat → (Nat → List E) → List (List E)
  | 0, _ => []
  | count + 1, buckets => buckets 0 :: collect count (fun key => buckets (key + 1))

theorem collect_length (count : Nat) (buckets : Nat → List E) :
    (collect count buckets).length = count := by
  induction count generalizing buckets with
  | zero => rfl
  | succ count ih => simp only [collect, List.length_cons, ih]

theorem collect_table (selectors : List (E → Bool)) (edges : List E) (disjoint : Disjoint selectors) :
    collect selectors.length (table selectors edges) = selectors.map (fun select => edges.filter select) := by
  induction selectors with
  | nil => rfl
  | cons select rest ih =>
    simp only [List.length_cons, collect, table_head, table_tail select rest edges disjoint, List.map_cons]
    rw [ih disjoint.of_cons]

end PetaProof.StableBuckets
