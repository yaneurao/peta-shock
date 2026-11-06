import PetaProof.RankedPolicy

/-!
有限・終端なしのアリーナのco-Buchiゲームについて、履歴不要決定性を証明する。
最大順位付き保証領域の補集合で安全候補削除が空になることを示し、
削除から構成した反証方策を元のゲームへ戻す。
将棋のleaf・四回出現規則・C++実装との同一性は、この定理に含めない。
-/

namespace PetaProof.HistoryArena

universe u
variable {V : Type u} (A : HistoryArena V)

/-- 最大保証領域には、通常の1手のOR/AND伝播で追加できる頂点も既に含まれる。 -/
theorem maximal_policy_ordinary {won : V → Prop} (policy : A.RankedPolicy won)
    (maximal : A.PolicyMaximal won) : A.OrdinaryClosed won := by
  intro v success
  by_cases inside : won v
  · exact inside
  · rcases success with ⟨own, w, edge, child⟩ | ⟨other, all⟩
    · let expanded := policy.addGood (current := fun x => x = v)
        (fun x hx => by simpa only [hx] using inside) (fun _ => w)
        (by intro x hx _; simpa only [hx] using edge)
        (by
          intro x y hx follows
          subst x
          have selected := follows.2 own
          exact Or.inl (by simpa only [selected] using child))
      exact maximal _ expanded v (Or.inr rfl)
    · let expanded := policy.addGood (current := fun x => x = v)
        (fun x hx => by simpa only [hx] using inside) policy.choice
        (fun x _ own => policy.legal x own)
        (by
          intro x y hx follows
          subst x
          exact Or.inl (all y follows.1))
      exact maximal _ expanded v (Or.inr rfl)

/-- 補集合内の安全集合を、旧保証領域への出口も許した新しい保証領域へ持ち上げる。 -/
noncomputable def RankedPolicy.addResidualSafe {won : V → Prop} (policy : A.RankedPolicy won)
    (ordinary : A.OrdinaryClosed won) {current : {v // ¬ won v} → Prop}
    (safe : (A.complementTrap ordinary).restricted.GoodSafeSet current) :
    A.RankedPolicy (fun v => won v ∨ ∃ outside : ¬ won v, current ⟨v, outside⟩) := by
  classical
  let trap := A.complementTrap ordinary
  let choice := fun v => if outside : ¬ won v then
    (trap.restricted.goodSafeChoice safe ⟨v, outside⟩).val else policy.choice v
  apply policy.addGood (current := fun v => ∃ outside : ¬ won v, current ⟨v, outside⟩)
    (fun _ h => h.choose) choice
  · intro v hv _
    obtain ⟨outside, _⟩ := hv
    simp only [choice, dif_pos outside]
    exact trap.restricted.goodSafeChoice_legal safe ⟨v, outside⟩
  · intro v w hv follows
    obtain ⟨outside, member⟩ := hv
    by_cases child : won w
    · exact Or.inl child
    · let source : {v // ¬ won v} := ⟨v, outside⟩
      let target : {v // ¬ won v} := ⟨w, child⟩
      have subfollows : trap.restricted.FollowsChoice (trap.restricted.goodSafeChoice safe) source target := by
        refine ⟨follows.1, ?_⟩
        intro own
        apply Subtype.ext
        simpa only [choice, dif_pos outside] using follows.2 own
      have good := trap.restricted.goodSafeChoice_stays safe source target member subfollows
      exact Or.inr ⟨⟨child, good.1⟩, good.2⟩

/-- 最大保証領域の補集合には、空でない安全集合が残り得ない。 -/
theorem residual_safe_empty {won : V → Prop} (policy : A.RankedPolicy won)
    (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won)
    {current : {v // ¬ won v} → Prop}
    (safe : (A.complementTrap ordinary).restricted.GoodSafeSet current) :
    ∀ v, ¬ current v := by
  intro v member
  let expanded := policy.addResidualSafe A ordinary safe
  exact v.property (maximal _ expanded v.val (Or.inr ⟨v.property, member⟩))

/-- 補集合の候補削除は有限回で空になる。履歴依存戦略の不在を先に仮定しない。 -/
theorem residual_deletion_empty {won : V → Prop} (policy : A.RankedPolicy won)
    (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∃ n, n ≤ ((A.complementTrap ordinary).vertices vertices).length ∧
      ∀ v, ¬ (A.complementTrap ordinary).restricted.goodIter n v := by
  let trap := A.complementTrap ordinary
  obtain ⟨n, bound, stable⟩ := trap.restricted.goodIter_stable_exists
    (trap.vertices vertices) (trap.vertices_cover vertices covered)
  exact ⟨n, bound, A.residual_safe_empty policy maximal ordinary stable⟩

/-- 勝敗が混在するゲームでも、最大保証領域の外側を覆う反証方策が存在する。 -/
theorem residual_counter_exists {won : V → Prop} (policy : A.RankedPolicy won)
    (maximal : A.PolicyMaximal won) (ordinary : A.OrdinaryClosed won)
    (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    Nonempty (A.complementTrap ordinary).restricted.Counterstrategy := by
  obtain ⟨n, _, empty⟩ := A.residual_deletion_empty policy maximal ordinary vertices covered
  exact ⟨(A.complementTrap ordinary).restricted.counterstrategyOfEmpty n empty⟩

/-- 最大の履歴不要保証領域は、任意の全履歴依存戦略を許した勝利領域と一致する。 -/
theorem maximal_policy_exact_history {won : V → Prop} (policy : A.RankedPolicy won)
    (maximal : A.PolicyMaximal won) (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∀ v, won v ↔ A.HistoryWinning v := by
  have ordinary := A.maximal_policy_ordinary policy maximal
  obtain ⟨counter⟩ := A.residual_counter_exists policy maximal ordinary vertices covered
  intro v
  constructor
  · exact policy.history_winning vertices covered v
  · intro winning
    apply Classical.byContradiction
    intro outside
    exact (A.complementTrap ordinary).counter_refutes_original counter v outside winning

/-- 有限・終端なしのco-Buchiゲームでは、正反両側に履歴不要方策の証拠を構成できる。 -/
theorem memoryless_determinacy (vertices : List V) (covered : ∀ v, v ∈ vertices) :
    ∃ won, Nonempty (A.RankedPolicy won) ∧ (∀ v, won v ↔ A.HistoryWinning v) ∧
      ∃ ordinary : A.OrdinaryClosed won,
        Nonempty (A.complementTrap ordinary).restricted.Counterstrategy := by
  obtain ⟨won, ⟨policy⟩, maximal⟩ := A.maximal_policy_exists vertices covered
  have ordinary := A.maximal_policy_ordinary policy maximal
  exact ⟨won, ⟨policy⟩, A.maximal_policy_exact_history policy maximal vertices covered,
    ordinary, A.residual_counter_exists policy maximal ordinary vertices covered⟩

/-- 個別の勝利局面にも、全履歴を使う戦略に代わる順位付き履歴不要方策がある。 -/
theorem history_winning_iff_ranked (vertices : List V) (covered : ∀ v, v ∈ vertices) (v : V) :
    A.HistoryWinning v ↔ ∃ won, Nonempty (A.RankedPolicy won) ∧ won v := by
  constructor
  · intro winning
    obtain ⟨won, policy, exactness, _⟩ := A.memoryless_determinacy vertices covered
    exact ⟨won, policy, (exactness v).mpr winning⟩
  · rintro ⟨won, ⟨policy⟩, inside⟩
    exact policy.history_winning vertices covered v inside

end PetaProof.HistoryArena
