import PetaProof.Certificate

/-! 選択手を一手に固定した後のdepth。leaf手を0、内部手を1として数え、上限で飽和する。
capでの再帰は仕様用であり、大規模入力でこの再帰を全局面へ実行する提案ではない。 -/
namespace PetaProof.SelectedDepth

universe u
variable {V : Type u}

def bump (cap depth : Nat) : Nat := min (depth + 1) cap

/-- next=noneはleaf手。cap回まで選択手を辿る、飽和距離の参照定義。 -/
def computed (next : V → Option V) : Nat → V → Nat
  | 0, _ => 0
  | cap + 1, vertex => match next vertex with
    | none => 0
    | some child => computed next cap child + 1

theorem computed_node (next : V → Option V) (cap : Nat) (vertex child : V)
    (step : next vertex = some child) :
    computed next (cap + 1) vertex = computed next cap child + 1 := by
  simp only [computed, step]

theorem bounded (next : V → Option V) (cap : Nat) (vertex : V) :
    computed next cap vertex ≤ cap := by
  induction cap generalizing vertex with
  | zero => simp [computed]
  | succ cap ih =>
    cases step : next vertex with
    | none => simp [computed, step]
    | some child =>
      have bound := ih child
      simp only [computed, step]
      omega

/-- 上限を一つ増やして計算しても、小さい上限で見た値は変わらない。 -/
theorem truncate (next : V → Option V) (cap : Nat) (vertex : V) :
    computed next cap vertex = min (computed next (cap + 1) vertex) cap := by
  induction cap generalizing vertex with
  | zero => simp [computed]
  | succ cap ih =>
    cases step : next vertex with
    | none => simp [computed, step]
    | some child =>
      rw [computed_node next cap vertex child step,
        computed_node next (cap + 1) vertex child step]
      rw [Nat.add_min_add_right, ← ih child]

/-- 参照定義は実装で用いる局所更新式を満たす。 -/
theorem equation (next : V → Option V) (cap : Nat) (vertex : V) :
    computed next cap vertex = match next vertex with
      | none => 0
      | some child => bump cap (computed next cap child) := by
  cases cap with
  | zero => cases next vertex <;> simp [computed, bump]
  | succ cap =>
    cases step : next vertex with
    | none => simp [computed, step]
    | some child =>
      rw [computed_node next cap vertex child step]
      change computed next cap child + 1 = min (computed next (cap + 1) child + 1) (cap + 1)
      rw [Nat.add_min_add_right, ← truncate next cap child]

/-- 上限と局所更新式を満たす表は、任意の小さい上限で参照定義と一致する。 -/
theorem solution_truncated (next : V → Option V) (cap : Nat) (depth : V → Nat)
    (updateRule : ∀ vertex, depth vertex = match next vertex with
      | none => 0
      | some child => bump cap (depth child))
    (cut : Nat) (small : cut ≤ cap) (vertex : V) :
    min (depth vertex) cut = computed next cut vertex := by
  induction cut generalizing vertex with
  | zero => simp [computed]
  | succ cut ih =>
    have update := updateRule vertex
    cases step : next vertex with
    | none => simp [step] at update; simp [computed, step, update]
    | some child =>
      have previous := ih (by omega) child
      simp only [step, bump] at update
      rw [computed_node next cut vertex child step]
      rw [update, Nat.min_assoc, Nat.min_eq_right small, Nat.add_min_add_right, previous]

/-- 循環を含む場合も解は一意。正しい距離表を追加の仮定にする必要はない。 -/
theorem unique (next : V → Option V) (cap : Nat) (depth : V → Nat)
    (within : ∀ vertex, depth vertex ≤ cap)
    (updateRule : ∀ vertex, depth vertex = match next vertex with
      | none => 0
      | some child => bump cap (depth child)) : depth = computed next cap := by
  funext vertex
  have same := solution_truncated next cap depth updateRule cap (Nat.le_refl _) vertex
  simpa only [Nat.min_eq_left (within vertex)] using same

/-- 局所更新式だけで範囲内に収まるため、一意性に独立な値域前提も不要。 -/
theorem unique_of_equation (next : V → Option V) (cap : Nat) (depth : V → Nat)
    (updateRule : ∀ vertex, depth vertex = match next vertex with
      | none => 0
      | some child => bump cap (depth child)) : depth = computed next cap := by
  apply unique next cap depth _ updateRule
  intro vertex
  rw [updateRule vertex]
  cases next vertex with
  | none => exact Nat.zero_le cap
  | some child => exact Nat.min_le_right _ _

/-- 選択手だけを辿った、leaf手直前までの内部手数。 -/
inductive LeafDistance (next : V → Option V) : V → Nat → Prop where
  | leaf {vertex} : next vertex = none → LeafDistance next vertex 0
  | node {vertex child distance} : next vertex = some child →
      LeafDistance next child distance → LeafDistance next vertex (distance + 1)

theorem bump_min (cap distance : Nat) : bump cap (min distance cap) = min (distance + 1) cap := by
  unfold bump
  by_cases short : distance ≤ cap
  · rw [Nat.min_eq_left short]
  · have large : cap ≤ distance := by omega
    rw [Nat.min_eq_right large, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem leaf_distance (next : V → Option V) {vertex : V} {distance : Nat}
    (path : LeafDistance next vertex distance) (cap : Nat) :
    computed next cap vertex = min distance cap := by
  induction path with
  | leaf step => rw [equation]; simp [step]
  | @node vertex child distance step tail ih =>
    rw [equation]
    simp only [step, ih]
    exact bump_min cap distance

/-- 上限未満なら、記録した数値どおりのleafまでの手順が実在する。 -/
theorem below_cap_has_leaf (next : V → Option V) (cap : Nat) (vertex : V)
    (short : computed next cap vertex < cap) :
    LeafDistance next vertex (computed next cap vertex) := by
  induction cap generalizing vertex with
  | zero => simp [computed] at short
  | succ cap ih =>
    cases step : next vertex with
    | none => simpa [computed, step] using LeafDistance.leaf step
    | some child =>
      have childShort : computed next cap child < cap := by
        simp only [computed, step] at short
        omega
      simpa only [computed, step] using LeafDistance.node step (ih child childShort)

/-- 飽和は循環だけでなく、上限以上の長い有限経路も含む。 -/
theorem saturated_iff (next : V → Option V) (cap : Nat) (vertex : V) :
    computed next cap vertex = cap ↔
      ∀ distance, distance < cap → ¬ LeafDistance next vertex distance := by
  constructor
  · intro same distance short path
    have exactValue := leaf_distance next path cap
    rw [Nat.min_eq_left (by omega)] at exactValue
    omega
  · intro noShort
    have limit := bounded next cap vertex
    apply Classical.byContradiction
    intro different
    have short : computed next cap vertex < cap := by omega
    exact noShort _ short (below_cap_has_leaf next cap vertex short)

/-- 内部手を辿るほど飽和depthは増えない。 -/
theorem antitone (next : V → Option V) (cap : Nat) (a b : V) (step : next a = some b) :
    computed next cap b ≤ computed next cap a := by
  have update := equation next cap a
  have limit := bounded next cap b
  simp only [step, bump] at update
  rw [update]
  exact Nat.le_min.mpr ⟨by omega, limit⟩

theorem strict_below_cap (next : V → Option V) (cap : Nat) (a b : V)
    (step : next a = some b) (short : computed next cap a < cap) :
    computed next cap b + 1 = computed next cap a := by
  have update := equation next cap a
  simp only [step, bump] at update
  by_cases under : computed next cap b + 1 ≤ cap
  · rw [Nat.min_eq_left under] at update
    exact update.symm
  · rw [Nat.min_eq_right (by omega)] at update
    omega

/-- 選択手の非空循環は必ず上限に飽和する。 -/
theorem cycle_saturated (next : V → Option V) (cap : Nat) {a b : V}
    (step : next a = some b) (back : Walk (fun x y => next x = some y) b a) :
    computed next cap a = cap := by
  have returnBound := back.nat_antitone (computed next cap) (antitone next cap)
  have update := equation next cap a
  have limit := bounded next cap a
  simp only [step, bump] at update
  by_cases under : computed next cap b + 1 ≤ cap
  · rw [Nat.min_eq_left under] at update
    omega
  · rw [Nat.min_eq_right (by omega)] at update
    exact update

/-- 循環へ至る枝分かれのない選択経路も、全て同じ上限になる。 -/
theorem reaches_saturated (next : V → Option V) (cap : Nat) {root target : V}
    (path : Walk (fun x y => next x = some y) root target)
    (saturated : computed next cap target = cap) : computed next cap root = cap := by
  have reachBound := path.nat_antitone (computed next cap) (antitone next cap)
  have limit := bounded next cap root
  omega

theorem cycle_has_no_leaf (next : V → Option V) {a b : V}
    (step : next a = some b) (back : Walk (fun x y => next x = some y) b a)
    (distance : Nat) (path : LeafDistance next a distance) : False := by
  have infinite := cycle_saturated next (distance + 1) step back
  have finite := leaf_distance next path (distance + 1)
  rw [Nat.min_eq_left (by omega)] at finite
  omega

end PetaProof.SelectedDepth
