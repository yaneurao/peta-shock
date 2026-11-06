import PetaProof.Localization
import PetaProof.Scc
import PetaProof.History

/-!
定理の前提が空虚でないこと、および重要な拒否条件を確認する小さな抽象グラフ。
盤面の合法性の証明ではない。各辺は手番を交代させる。
-/

namespace PetaProof.Examples

def cycleEdge (a b : Bool) : Prop := b = !a

def cycleTail : Walk cycleEdge true false := .cons rfl (.nil false)

/-- 王手なしの2頂点循環を値0として受理できる。 -/
def drawCertificate : Certificate Bool where
  edge := cycleEdge
  owner := id
  check := fun _ _ => False
  player := false
  value := fun _ => 0
  mate := 32000
  mate_pos := by decide
  bounded := by intro _; omega
  monotone := by intro _ _ _; omega
  no_own_cycle := by
    intro a b e back
    cases a with
    | false => exact e.2.2.2 rfl
    | true =>
      cases b with
      | true => cases e.1
      | false =>
        cases back with
        | cons first _ => exact first.2.2.2 rfl
  opponent_cycle_checks := by intro _ _ _ positive; omega

theorem draw_payoff : drawCertificate.repetitionPayoff
    (a := false) (b := true) rfl cycleTail = 0 := by
  simp [Certificate.repetitionPayoff, Walk.Every, Certificate.OwnChecks,
    Certificate.OpponentChecks, drawCertificate, cycleTail]

/-- 局所minimax方程式だけなら、王手なしの循環に+100と-100を付けても整合してしまう。 -/
def falseDrawValue (a : Bool) : Int := if a then -100 else 100

theorem false_draw_is_locally_consistent (a b : Bool) (e : cycleEdge a b) :
    -falseDrawValue b = falseDrawValue a := by
  cases a <;> cases b <;> simp_all [cycleEdge, falseDrawValue]

/-- しかし先手視点で+100と約束すると、相手の非王手枝がSCC内にある検査条件を満たせない。 -/
theorem false_draw_fails_cycle_check : ¬ (∀ a b, cycleEdge a b →
    (0 : Int) < 100 → (0 : Int) < 100 → Walk cycleEdge b a →
    a ≠ false → False) := by
  intro checked
  exact checked true false rfl (by decide) (by decide)
    (.cons rfl (.nil true)) (by decide)

/-- 自分だけが王手する循環も、値0の局所方程式だけでは検出できない。 -/
theorem own_check_fails_cycle_check : ¬ (∀ a b,
    (cycleEdge a b ∧ (-32000 : Int) < 0 ∧ (-32000 : Int) < 0 ∧
      (a = false → a = false)) →
    Walk (fun x y => cycleEdge x y ∧ (-32000 : Int) < 0 ∧ (-32000 : Int) < 0 ∧
      (x = false → x = false)) b a → False) := by
  intro acyclic
  exact acyclic false true ⟨rfl, by decide, by decide, id⟩
    (.cons ⟨rfl, by decide, by decide, id⟩ (.nil false))

/-- 2頂点循環の代表falseへ至る、順位0/1の森。 -/
def cycleInward : ReachForest cycleEdge where
  root := fun _ => false
  parent := fun _ => false
  rank := fun v => if v then 1 else 0
  step := by intro v notRoot; cases v <;> simp_all [cycleEdge]
  root_parent := by intro _ _; rfl
  decreasing := by intro v notRoot; cases v <;> simp_all

def cycleOutward : ReachForest (fun a b => cycleEdge b a) where
  root := fun _ => false
  parent := fun _ => false
  rank := fun v => if v then 1 else 0
  step := by intro v notRoot; cases v <;> simp_all [cycleEdge]
  root_parent := by intro _ _; rfl
  decreasing := by intro v notRoot; cases v <;> simp_all

/-- 成分内往復の森を使って、2頂点が本当に同じSCCであることを証明する。 -/
def cyclePartition : SccPartition cycleEdge :=
  .ofForests (fun _ => 0) (by intro _ _ _; exact Nat.le_refl 0) cycleInward cycleOutward
    (by intro _; rfl) (by intro _ _ _; rfl)

theorem cycle_component_is_cyclic : CyclicVertex cycleEdge false :=
  (cyclePartition.cyclic_iff false).2 (Or.inr ⟨true, by decide, rfl⟩)

def sixMoves : Walk cycleEdge false false :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil false))))))

/-- 6手・7訪問で先手局面が4回現れ、切り出した実際の区間が引き分け保証を満たす。 -/
theorem fourfold_draw_trace :
    ∃ (stem : Walk drawCertificate.edge false false) (next : Bool)
      (edge : drawCertificate.edge false next) (back : Walk drawCertificate.edge next false)
      (suffix : Walk drawCertificate.edge false false),
      sixMoves = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count false = 1 ∧ (Walk.cons edge back).visits.count false = 4 ∧
      drawCertificate.value false ≤ drawCertificate.repetitionPayoff edge back :=
  drawCertificate.fourfold_from_walk sixMoves false (by decide)

/-- 鳩の巣原理の境界値も確認する。2頂点で6手続けば四回出現を含む。 -/
theorem six_moves_force_fourfold : ∃ v ∈ [false, true], 4 ≤ sixMoves.visits.count v := by
  apply fourfold_exists [false, true] sixMoves.visits
  · intro v _
    cases v <;> simp
  · decide

end PetaProof.Examples
