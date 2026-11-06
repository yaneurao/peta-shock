import PetaProof.DepthWriter
import PetaProof.Checks
import PetaProof.SignedBounds

/-! depth方式の最終SCC検査から、保存最大手による実対局の保証までを接続する。
生成された安全順位表を入力にせず、局所minimax条件とSCC検査の受理条件を用いる。 -/
namespace PetaProof.DepthCheckedOutput

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}

/-- 値は固定プレイヤー視点、writerの評価値は局面の手番側視点。 -/
def moverValue (G : ThresholdGame V) (value : V → Int) (vertex : V) : Int :=
  if G.owner vertex = G.player then value vertex else -value vertex

def fixedScore (value : V → Int) : Move V → Int
  | .leaf score => score
  | .node child => value child

structure Input (G : ThresholdGame V) (E : Type v) where
  writer : DepthWriter.Input V E
  move : E → Move V
  value : V → Int
  bounded : ∀ vertex, -G.mate ≤ value vertex ∧ value vertex ≤ G.mate
  raw_eq : ∀ vertex edge, writer.raw vertex edge =
    moverValue G (fun _ => fixedScore value (move edge)) vertex
  best_eq : ∀ vertex, writer.best vertex = moverValue G value vertex
  legal : ∀ vertex edge, edge ∈ writer.rows vertex → G.legal vertex (move edge)
  covers : ∀ vertex command, G.legal vertex command →
    ∃ edge ∈ writer.rows vertex, move edge = command

namespace Input
variable (I : Input G E)

/-- 自分は許可集合、相手は元の全合法手。 -/
def follows (vertex : V) (move : Move V) : Prop :=
  ∃ edge ∈ I.writer.rows vertex, I.move edge = move ∧
    (G.owner vertex = G.player → I.writer.allowed vertex edge)

def internal (vertex child : V) : Prop := I.follows vertex (.node child)

/-- 相手の非最善応手も落とさない。 -/
theorem opponent_all (vertex : V) (move : Move V) (other : G.owner vertex ≠ G.player)
    (legal : G.legal vertex move) : I.follows vertex move := by
  obtain ⟨edge, member, same⟩ := I.covers vertex move legal
  exact ⟨edge, member, same, fun own => False.elim (other own)⟩

/-- 保存出力から選ばれた最大手は、shrinkの有無によらず検査対象に含まれる。 -/
theorem maximum_follows (shrink : Bool) (vertex : V) (edge : E)
    (member : edge ∈ I.writer.outputRows shrink vertex)
    (maximal : ∀ other ∈ I.writer.outputRows shrink vertex,
      I.writer.saved vertex other ≤ I.writer.saved vertex edge) : I.follows vertex (I.move edge) :=
  ⟨edge, ((I.writer.output_member shrink vertex edge).mp member).1, rfl,
    fun _ => (I.writer.output_maximum_iff shrink vertex edge member).mp maximal⟩

/-- 手番側の局所minimax検査から、固定視点では値が下がらない。 -/
theorem move_lower (vertex : V) (move : Move V) (allowed : I.follows vertex move) :
    I.value vertex ≤ fixedScore I.value move := by
  obtain ⟨edge, member, same, accepted⟩ := allowed
  have upper := I.writer.upper vertex edge member
  rw [I.raw_eq vertex edge, I.best_eq vertex, same] at upper
  by_cases own : G.owner vertex = G.player
  · have exactValue := (accepted own).1
    rw [I.raw_eq vertex edge, I.best_eq vertex, same] at exactValue
    simp only [moverValue, if_pos own] at exactValue
    omega
  · simp only [moverValue, if_neg own] at upper
    omega

theorem monotone (vertex child : V) (edge : I.internal vertex child) :
    I.value vertex ≤ I.value child := I.move_lower vertex (.node child) edge

/-- C++の最終検査に相当する二つのSCC検査。正しいSCC分割の証拠は明示的に要求する。 -/
structure Accepted where
  base : V → V → Prop
  own_subset : ∀ a b,
    OwnCheckingEdge I.internal G.owner G.check G.player I.value G.mate a b → base a b
  basePartition : SccPartition base
  ownPartition : SccPartition (fun a b =>
    OwnCheckingEdge I.internal G.owner G.check G.player I.value G.mate a b ∧
      basePartition.cyclicFlag a ∧ basePartition.cyclicFlag b)
  ownAccepted : ∀ vertex, ¬ ownPartition.cyclicFlag vertex
  positivePartition : SccPartition (fun a b =>
    I.internal a b ∧ 0 < I.value a ∧ 0 < I.value b)
  positiveAccepted : ∀ a b, I.internal a b → 0 < I.value a → 0 < I.value b →
    G.owner a ≠ G.player → positivePartition.component a = positivePartition.component b → G.check a b

def checks (accepted : I.Accepted) : PartitionChecks V where
  edge := I.internal
  owner := G.owner
  check := G.check
  player := G.player
  value := I.value
  mate := G.mate
  mate_pos := Int.lt_of_lt_of_le G.positive G.bounded
  bounded := I.bounded
  monotone := I.monotone
  base := accepted.base
  own_subset := accepted.own_subset
  basePartition := accepted.basePartition
  ownPartition := accepted.ownPartition
  ownAccepted := accepted.ownAccepted
  positivePartition := accepted.positivePartition
  positiveAccepted := accepted.positiveAccepted

def certificate (accepted : I.Accepted) : Certificate V := (I.checks accepted).certificate

/-- 正評価の閉じた経路で、相手の非王手が一つでもあれば最終検査は受理できない。 -/
theorem positive_quiet_cycle_rejected (accepted : I.Accepted)
    (a b : V) (edge : I.internal a b) (back : Walk I.internal b a)
    (positive : 0 < I.value a) (other : G.owner a ≠ G.player)
    (quiet : ¬ G.check a b) : False := by
  have next := I.monotone a b edge
  have positiveChild : 0 < I.value b := by omega
  exact quiet ((I.certificate accepted).opponent_cycle_checks a b edge positive
    positiveChild back other)

/-- 負評価で長い経路を優先しても、自分の王手千日手を許可する理由にはならない。 -/
theorem own_checking_cycle_rejected (accepted : I.Accepted)
    (a b : V) (edge : I.internal a b) (back : Walk I.internal b a)
    (better : -G.mate < I.value a)
    (checks : (Walk.cons edge back).Every (fun x y => G.owner x = G.player → G.check x y)) :
    False := (I.certificate accepted).loop_not_own_checks edge back better checks

/-- 手順全体で終局利得を保証する。安全順位表の存在を仮定する定理ではない。 -/
theorem terminal_lower [DecidableEq V] (accepted : I.Accepted) (plan : G.MovePlan)
    (chosen : ∀ history vertex, I.follows vertex (plan.choose history vertex))
    (root : V) (payoff : Int) (result : G.TerminalResult plan root payoff) :
    I.value root ≤ payoff := by
  let C := I.certificate accepted
  let P := fun a b => I.value root ≤ I.value a ∧ I.internal a b
  apply ThresholdGame.TerminalResult.property G result
    (fun vertex => I.value root ≤ I.value vertex) P
    (fun score => I.value root ≤ score) (Int.le_refl _)
  · intro history vertex move lower _ same
    have follows : I.follows vertex move := by rw [← same]; exact chosen history vertex
    have bound := I.move_lower vertex move follows
    cases move with
    | leaf score => exact Int.le_trans lower bound
    | node child => exact ⟨Int.le_trans lower bound, lower, follows⟩
  · intro a b edge back all
    let convert : ∀ x y, G.LegalNode x y ∧ P x y → C.edge x y := fun _ _ h => h.2.2
    let edge' : C.edge a b := all.1.2
    let back' : Walk C.edge b a := (back.withEvery P all.2).map convert
    have rootLower : I.value root ≤ I.value a := all.1.1
    have guarantee := C.repetition_guarantee edge' back'
    have same := G.repetitionValue_map
      (show G.LegalNode a b ∧ P a b from ⟨edge, all.1⟩)
      (back.withEvery P all.2) convert
    rw [G.repetitionValue_restrict edge back all.1 all.2] at same
    rw [← G.repetitionValue_eq_certificate C rfl rfl rfl rfl edge' back'] at guarantee
    rw [same] at guarantee
    exact Int.le_trans rootLower guarantee

/-- 履歴ごとに保存最大手を選ぶ条件。同点候補を任意に切り替えてよい。 -/
def MaximumPlan (shrink : Bool) (self : G.MovePlan) : Prop :=
  ∀ history vertex, G.owner vertex = G.player →
    ∃ edge ∈ I.writer.outputRows shrink vertex,
      self.choose history vertex = I.move edge ∧
      ∀ other ∈ I.writer.outputRows shrink vertex,
        I.writer.saved vertex other ≤ I.writer.saved vertex edge

/-- 検証済みの選択手を使う合法計画。最大手を選ぶ計画の実在も示す。 -/
def selectedPlan : G.MovePlan where
  choose := fun _ vertex => I.move (I.writer.selected vertex)
  legal := fun _ vertex => I.legal vertex _ (I.writer.selected_member vertex)

theorem selectedPlan_maximum (shrink : Bool) : I.MaximumPlan shrink I.selectedPlan := by
  intro history vertex _
  have member : I.writer.selected vertex ∈ I.writer.outputRows shrink vertex :=
    (I.writer.output_member shrink vertex _).mpr
      ⟨I.writer.selected_member vertex, Or.inr (I.writer.selected_exact vertex)⟩
  exact ⟨I.writer.selected vertex, member, rfl,
    (I.writer.output_maximum_iff shrink vertex _ member).mpr (I.writer.selected_allowed vertex)⟩

/-- SCC検査の受理から、実際の保存最大手選択の終局保証までを直接つなぐ。 -/
theorem output_lower [DecidableEq V] (accepted : I.Accepted) (shrink : Bool)
    (self opponent : G.MovePlan) (selected : I.MaximumPlan shrink self)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    I.value root ≤ payoff := by
  apply I.terminal_lower accepted (G.combinePlans self opponent) _ root payoff result
  intro history vertex
  by_cases own : G.owner vertex = G.player
  · obtain ⟨edge, member, same, maximal⟩ := selected history vertex own
    simpa only [ThresholdGame.combinePlans, if_pos own, same] using
      I.maximum_follows shrink vertex edge member maximal
  · simpa only [ThresholdGame.combinePlans, if_neg own] using
      I.opponent_all vertex (opponent.choose history vertex) own (opponent.legal history vertex)

theorem output_positive_no_draw [DecidableEq V] (accepted : I.Accepted) (shrink : Bool)
    (self opponent : G.MovePlan) (selected : I.MaximumPlan shrink self)
    (root : V) (positive : 0 < I.value root)
    (result : G.TerminalResult (G.combinePlans self opponent) root 0) : False := by
  have lower := I.output_lower accepted shrink self opponent selected root 0 result
  omega

theorem output_no_mate_loss [DecidableEq V] (accepted : I.Accepted) (shrink : Bool)
    (self opponent : G.MovePlan) (selected : I.MaximumPlan shrink self)
    (root : V) (better : -G.mate < I.value root)
    (result : G.TerminalResult (G.combinePlans self opponent) root (-G.mate)) : False := by
  have lower := I.output_lower accepted shrink self opponent selected root (-G.mate) result
  omega

/-- depthが正確な距離でなくても、有限入力では正利得の最初の終局が存在する。 -/
theorem output_positive_terminates [DecidableEq V] (accepted : I.Accepted) (shrink : Bool)
    (self opponent : G.MovePlan) (selected : I.MaximumPlan shrink self)
    (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (root : V) (positive : 0 < I.value root) :
    ∃ payoff, ∃ result : G.TerminalResult (G.combinePlans self opponent) root payoff,
      0 < payoff ∧ result.plies ≤ 3 * vertices.length := by
  obtain ⟨payoff, ⟨result⟩⟩ := G.terminal_result_exists vertices covered
    (G.combinePlans self opponent) root
  have lower := I.output_lower accepted shrink self opponent selected root payoff result
  exact ⟨payoff, result, by omega, ThresholdGame.TerminalResult.plies_bound G vertices covered result⟩

/-- 両視点の検査が通り、保証値が符号反転で対応すれば、その値は厳密なゲーム値。
単なるminimax方程式の固定点を正しい値と仮定する必要はない。 -/
theorem exact_value [DecidableEq V] {F : Type v} (accepted : I.Accepted)
    (other : Input G.opposite F) (otherAccepted : other.Accepted)
    (oppositeValues : ∀ vertex, other.value vertex = -I.value vertex) (root : V) :
    G.ExactValue root (I.value root) := by
  constructor
  · refine ⟨I.selectedPlan, ?_⟩
    intro opponent payoff result
    exact I.output_lower accepted false I.selectedPlan opponent (I.selectedPlan_maximum false)
      root payoff result
  · refine ⟨other.selectedPlan.unopposite, ?_⟩
    intro self payoff result
    have reflected := ThresholdGame.TerminalResult.opposite G result
    rw [G.opposite_combine, ThresholdGame.MovePlan.opposite_unopposite] at reflected
    have upper := other.output_lower otherAccepted false other.selectedPlan self.opposite
      (other.selectedPlan_maximum false) root (-payoff) reflected
    rw [oppositeValues root] at upper
    omega

/-- 両者とも保存最大手を選ぶ実対局は、その厳密値で終局する。 -/
theorem opposite_outputs_exact [DecidableEq V] {F : Type v} (accepted : I.Accepted)
    (other : Input G.opposite F) (otherAccepted : other.Accepted)
    (oppositeValues : ∀ vertex, other.value vertex = -I.value vertex)
    (shrink otherShrink : Bool) (self opponent : G.MovePlan)
    (selected : I.MaximumPlan shrink self)
    (otherSelected : other.MaximumPlan otherShrink opponent.opposite)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    payoff = I.value root := by
  have lower := I.output_lower accepted shrink self opponent selected root payoff result
  have reflected := ThresholdGame.TerminalResult.opposite G result
  rw [G.opposite_combine] at reflected
  have upper := other.output_lower otherAccepted otherShrink opponent.opposite self.opposite
    otherSelected root (-payoff) reflected
  rw [oppositeValues root] at upper
  omega

end Input
end PetaProof.DepthCheckedOutput
