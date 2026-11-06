import PetaProof.Infinite
import PetaProof.CoBuchiExamples
import PetaProof.PropagationExamples

/-! 周期経路の構成、悪い自己循環の排除、将棋モデルへの接続を検査する。 -/
namespace PetaProof.InfiniteExamples

/-- 帰りの歩道が0手でも、自己循環を無限反復できる。 -/
theorem self_loop_repeats :
    ∃ path : Nat → Unit, (∀ i, (fun _ _ => True) (path i) (path (i + 1))) ∧
      ∀ n, ∃ i, n ≤ i ∧ (fun _ _ => True) (path i) (path (i + 1)) :=
  bad_cycle_repeats (R := fun _ _ : Unit => True) (bad := fun _ _ => True)
    (a := ()) (b := ()) trivial trivial (.nil ())

theorem bad_self_loop_not_coBuchi : ¬ AllPathsCoBuchi
    (fun _ _ : Unit => True) (fun _ _ => True) := by
  intro safe
  exact safe.no_bad_cycle () () trivial trivial (Reachable.refl ())

/-- 一時的な悪い辺1回は、無限経路条件でも許される。 -/
theorem transient_all_paths_coBuchi :
    AllPathsCoBuchi CoBuchiExamples.edge CoBuchiExamples.bad :=
  (no_bad_cycle_iff_all_paths _ _ [false, true] (by intro v; cases v <;> simp)).mp
    CoBuchiExamples.transient_edge_is_allowed

theorem checking_loop_has_coBuchi_region :
    Nonempty (PropagationExamples.loopGame.CoBuchiRegion (fun _ => False ∨ True)) :=
  ⟨PropagationExamples.loopRegion.positional.coBuchi [false, true]
    (by intro v; cases v <;> simp)⟩

end PetaProof.InfiniteExamples
