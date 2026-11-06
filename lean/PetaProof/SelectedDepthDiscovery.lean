import PetaProof.SelectedDepthUnwind
import PetaProof.QueueScanAccounting

/-! 確定局面を再利用し、経路内再訪で止まる前向き経路収集。
fuelは参照実装の停止証明用。経路を組合せ的に列挙する処理ではない。 -/
namespace PetaProof.SelectedDepth

universe u
variable {V : Type u} [DecidableEq V]

def discover (next : V → Option V) (done : V → Bool) : Nat → V → List V → Option (List V)
  | 0, _, _ => none
  | fuel + 1, head, rest => match next head with
    | none => some (head :: rest)
    | some child =>
      if done child = true ∨ child ∈ head :: rest then some (head :: rest)
      else discover next done fuel child (head :: rest)

/-- 返る経路は非空で連結し、元の経路を含み、三種類の停止条件のいずれかを満たす。 -/
theorem discover_spec (next : V → Option V) (done : V → Bool) (fuel : Nat)
    (head : V) (rest result : List V) (linked : Linked next (head :: rest))
    (found : discover next done fuel head rest = some result) :
    ∃ last tail, result = last :: tail ∧ Linked next (last :: tail) ∧
      (∀ child, next last = some child → done child = true ∨ child ∈ last :: tail) ∧
      (∀ x ∈ head :: rest, x ∈ result) := by
  induction fuel generalizing head rest result with
  | zero => simp [discover] at found
  | succ fuel ih =>
    cases step : next head with
    | none =>
      have same : head :: rest = result := by simpa [discover, step] using found
      subst result
      refine ⟨head, rest, rfl, linked, ?_, fun _ h => h⟩
      intro child edge
      simp [step] at edge
    | some child =>
      by_cases stopped : done child = true ∨ child ∈ head :: rest
      · have same : head :: rest = result := by
          simpa only [discover, step, if_pos stopped, Option.some.injEq] using found
        subst result
        refine ⟨head, rest, rfl, linked, ?_, fun _ h => h⟩
        intro target edge
        have sameChild : target = child := Option.some.inj (edge.symm.trans step)
        exact sameChild ▸ stopped
      · have recurse : discover next done fuel child (head :: rest) = some result := by
          simpa only [discover, step, if_neg stopped] using found
        obtain ⟨last, tail, same, connected, ended, included⟩ :=
          ih child (head :: rest) result ⟨step, linked⟩ recurse
        exact ⟨last, tail, same, connected, ended, fun x present => included x (by simp [present])⟩

/-- 経路が重複せず有限一覧内にあれば、N+1を超えるfuelは不要。 -/
theorem discover_exists (next : V → Option V) (done : V → Bool) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (fuel : Nat) (head : V) (rest : List V)
    (distinct : (head :: rest).Nodup)
    (enough : vertices.length < (head :: rest).length + fuel) :
    ∃ result, discover next done fuel head rest = some result := by
  induction fuel generalizing head rest with
  | zero =>
    have limit := DistinctWork.length_le (head :: rest) vertices distinct (fun v _ => covered v)
    simp only [Nat.add_zero] at enough
    omega
  | succ fuel ih =>
    cases step : next head with
    | none => exact ⟨head :: rest, by simp [discover, step]⟩
    | some child =>
      by_cases stopped : done child = true ∨ child ∈ head :: rest
      · exact ⟨head :: rest, by simp only [discover, step, if_pos stopped]⟩
      · have fresh : child ∉ head :: rest := fun member => stopped (Or.inr member)
        have unique : (child :: head :: rest).Nodup := List.nodup_cons.mpr ⟨fresh, distinct⟩
        obtain ⟨result, found⟩ := ih child (head :: rest) unique (by simp only [List.length_cons] at *; omega)
        exact ⟨result, by simpa only [discover, step, if_neg stopped] using found⟩

/-- 収集した経路をpopすると、確定済み局面と今回の全局面に正しいdepthが入る。 -/
theorem discovered_sweep_correct (next : V → Option V) (cap : Nat) (done : V → Bool)
    (table : V → Nat) (fuel : Nat) (root : V) (result : List V)
    (settled : ∀ x, done x = true → table x = computed next cap x)
    (untouched : ∀ x, done x ≠ true → table x = cap)
    (found : discover next done fuel root [] = some result) :
    (∀ x, done x = true ∨ x ∈ result → unwind next cap result table x = computed next cap x) ∧
    (∀ x, ¬ (done x = true ∨ x ∈ result) → unwind next cap result table x = cap) ∧
    root ∈ result := by
  obtain ⟨last, tail, same, linked, stopped, included⟩ :=
    discover_spec next done fuel root [] result trivial found
  have rootMember := included root (by simp)
  subst result
  have after := path_sweep_correct next cap table (fun x => done x = true) last tail
    linked settled untouched stopped
  exact ⟨after.1, after.2, rootMember⟩

end PetaProof.SelectedDepth
