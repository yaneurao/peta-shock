import PetaProof.Pruning

/-!
局所王手循環の追加と、悪い出口による削除伝播を確認する抽象グラフ。
合法な将棋盤面を構成した例ではなく、各辺で手番が交代する2頂点の例である。
-/

namespace PetaProof.PropagationExamples

open ThresholdGame

/-- 先手は非王手、後手は王手で同じ2局面を往復する。閾値は10。 -/
def loopGame : ThresholdGame Bool where
  legal := fun v m => m = .node (!v)
  owner := id
  check := fun v _ => v = true
  player := false
  threshold := 10
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by
    intro v w legal
    cases v <;> cases w <;> simp_all
  nonempty_moves := fun v => ⟨.node (!v), rfl⟩
  no_mutual_cycle := by
    intro a b edge back
    cases a with
    | false => cases edge.2
    | true =>
      cases b with
      | true => cases edge.1
      | false =>
        cases back with
        | cons first _ => cases first.2

/-- 同じ追加集合内の後手の継続が王手なので、両局面をまとめて確定できる。 -/
def loopBatch : loopGame.SafeBatch (fun _ => False) (fun _ => True) where
  fresh := by intro _ _ impossible; contradiction
  choice := fun v => .node (!v)
  chosen_legal := by intro _ _ _; rfl
  safe := by
    intro v _ m follows
    have legal := follows.1
    change m = .node (!v) at legal
    subst m
    apply Or.inr
    constructor
    · trivial
    · cases v <;> simp [loopGame]

noncomputable def loopRegion : loopGame.RankedRegion (fun _ => False ∨ True) :=
  RankedRegion.extend RankedRegion.empty loopBatch

theorem loop_region_has_moves (v : Bool) : ∃ m, loopGame.Follows loopRegion.choice v m :=
  loopRegion.has_following_move v (Or.inr True.intro)

theorem loop_region_rank (v : Bool) : loopRegion.rank v = 1 := by
  simp [loopRegion, RankedRegion.extend, RankedRegion.empty, RankedRegion.extendedRank]

theorem loop_is_safe : loopGame.SafeSet (fun _ => False) (fun _ => True) :=
  loopGame.safeSet_of_batch loopBatch

/-- 後手の手番には、王手でない悪いleaf出口0もある版。 -/
def escapeLegal (v : Bool) (m : Move Bool) : Prop :=
  m = .node (!v) ∨ (v = true ∧ m = .leaf 0)

theorem escape_node {v w : Bool} (legal : escapeLegal v (.node w)) :
    loopGame.legal v (.node w) := by
  cases legal with
  | inl h => exact h
  | inr h => cases h.2

def escapeGame : ThresholdGame Bool := {
  loopGame with
  legal := escapeLegal
  alternating := fun v w legal => loopGame.alternating v w (escape_node legal)
  nonempty_moves := fun v => ⟨.node (!v), Or.inl rfl⟩
  no_mutual_cycle := by
    intro a b edge back
    exact loopGame.no_mutual_cycle a b ⟨escape_node edge.1, edge.2⟩
      (back.map (fun _ _ h => ⟨escape_node h.1, h.2⟩))
}

/-- 相手がleaf0を選べるため、後手局面は1回目の削除で消える。 -/
theorem bad_exit_deleted : ¬ escapeGame.prune (fun _ => False) (fun _ => True) true := by
  intro survives
  have bad := survives.2.2 (by decide) (.leaf 0) (Or.inr ⟨rfl, rfl⟩)
  change (10 : Int) ≤ 0 at bad
  omega

/-- その子にしか進めない先手局面も、次の削除で消える。 -/
theorem escape_all_deleted (v : Bool) :
    ¬ escapeGame.pruneIter (fun _ => False) (fun _ => True) 2 v := by
  intro survives
  cases v with
  | true => exact bad_exit_deleted survives.1
  | false =>
    obtain ⟨m, legal, safe⟩ := survives.2.1 rfl
    have selected : m = .node true := by
      cases legal with
      | inl h => exact h
      | inr h => cases h.1
    subst m
    rcases safe with impossible | ⟨child, _⟩
    · contradiction
    · exact bad_exit_deleted child

/-- 通常OR伝播の例。良いleaf20と悪いleaf-20があっても、自分は良い方を選べる。 -/
def ordinaryGame : ThresholdGame Unit where
  legal := fun _ m => m = .leaf 20 ∨ m = .leaf (-20)
  owner := fun _ => false
  check := fun _ _ => False
  player := false
  threshold := 10
  mate := 32000
  positive := by decide
  bounded := by decide
  alternating := by
    intro _ _ legal
    cases legal with
    | inl impossible => cases impossible
    | inr impossible => cases impossible
  nonempty_moves := fun _ => ⟨.leaf 20, Or.inl rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def ordinaryBatch : ordinaryGame.SafeBatch (fun _ => False) (fun _ => True) :=
  SafeBatch.ofOrdinary
    (by intro _ _ impossible; contradiction)
    (fun _ => .leaf 20)
    (by intro _ _ _; exact Or.inl rfl)
    (by
      intro v _ m follows
      have selected : (.leaf 20 : Move Unit) = m := follows.2 rfl
      rw [← selected]
      decide)

noncomputable def ordinaryRegion : ordinaryGame.RankedRegion (fun _ => False ∨ True) :=
  RankedRegion.extend RankedRegion.empty ordinaryBatch

theorem ordinary_leaf_is_good : (10 : Int) ≤ 20 :=
  ordinaryRegion.closed () (Or.inr True.intro) (.leaf 20)
    ⟨Or.inl rfl, by intro _; simp [ordinaryRegion, RankedRegion.extend,
      RankedRegion.extendedChoice, ordinaryBatch, SafeBatch.ofOrdinary]⟩

end PetaProof.PropagationExamples
