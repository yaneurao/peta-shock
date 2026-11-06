import PetaProof.FiniteSink

/-!
単調に増える確定領域の進捗上界。
各成功回で有限候補列挙内の未確定頂点を少なくとも1個加えるなら、成功回数は候補数以下。
C++のキューがこの進捗条件を満たすという実装対応は別の証明である。
-/

namespace PetaProof

universe u
variable {V : Type u}

/-- 既存の確定領域を保持し、毎回新しい候補を加えるなら、要素数は成功回数分だけ増える。 -/
theorem admission_growth (vertices : List V) (won : Nat → V → Prop)
    (monotone : ∀ i v, won i v → won (i + 1) v) (n : Nat)
    (fresh : ∀ i, i < n → ∃ v, v ∈ vertices ∧ won (i + 1) v ∧ ¬ won i v) :
    ThresholdGame.population vertices (won 0) + n ≤ ThresholdGame.population vertices (won n) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have earlier := ih (fun i hi => fresh i (by omega))
    obtain ⟨v, member, new, old⟩ := fresh n (by omega)
    have growth := population_strict_subset vertices (won n) (won (n + 1))
      (monotone n) v member new old
    omega

/-- K候補のどれかを毎回新規確定する成功回数は高々K回。閾値をまたいでも同じ。 -/
theorem admission_count_bound (vertices : List V) (won : Nat → V → Prop)
    (monotone : ∀ i v, won i v → won (i + 1) v) (n : Nat)
    (fresh : ∀ i, i < n → ∃ v, v ∈ vertices ∧ won (i + 1) v ∧ ¬ won i v) :
    n ≤ vertices.length := by
  have growth := admission_growth vertices won monotone n fresh
  have upper := ThresholdGame.population_bound vertices (won n)
  omega

/-- 未停止なら必ず新規確定があるという進捗仕様の下では、K回以内に停止条件を満たす。 -/
theorem progress_stops (vertices : List V) (won : Nat → V → Prop)
    (monotone : ∀ i v, won i v → won (i + 1) v) (stopped : Nat → Prop)
    (progress : ∀ i, ¬ stopped i → ∃ v, v ∈ vertices ∧ won (i + 1) v ∧ ¬ won i v) :
    ∃ n, n ≤ vertices.length ∧ stopped n := by
  classical
  apply Classical.byContradiction
  intro none
  have fresh : ∀ i, i < vertices.length + 1 →
      ∃ v, v ∈ vertices ∧ won (i + 1) v ∧ ¬ won i v := by
    intro i hi
    apply progress i
    intro done
    exact none ⟨i, by omega, done⟩
  have bound := admission_count_bound vertices won monotone (vertices.length + 1) fresh
  omega

end PetaProof
