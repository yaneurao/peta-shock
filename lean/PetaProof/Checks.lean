import PetaProof.Scc

/-!
SCC検査の条件からCertificateを構成する接続部。
SccPartitionの証拠の生成は別段階だが、意味論的な循環条件を直接仮定する必要はなくなる。
-/

namespace PetaProof

universe u

def OwnCheckingEdge {V : Type u} (edge : V → V → Prop) (owner : V → Bool)
    (check : V → V → Prop) (player : Bool) (value : V → Int) (mate : Int)
    (a b : V) : Prop :=
  edge a b ∧ -mate < value a ∧ -mate < value b ∧ (owner a = player → check a b)

/-- C++の検査に対応するSCC分割と、その分割上の受理条件。 -/
structure PartitionChecks (V : Type u) where
  edge : V → V → Prop
  owner : V → Bool
  check : V → V → Prop
  player : Bool
  value : V → Int
  mate : Int
  mate_pos : 0 < mate
  bounded : ∀ v, -mate ≤ value v ∧ value v ≤ mate
  monotone : ∀ a b, edge a b → value a ≤ value b
  /-- 方策による辺削除前の、自分の王手を続けるグラフ。 -/
  base : V → V → Prop
  own_subset : ∀ a b, OwnCheckingEdge edge owner check player value mate a b → base a b
  basePartition : SccPartition base
  /-- baseの循環core内へ限定した、自分の王手継続グラフのSCC。 -/
  ownPartition : SccPartition (fun a b =>
    OwnCheckingEdge edge owner check player value mate a b ∧
    basePartition.cyclicFlag a ∧ basePartition.cyclicFlag b)
  ownAccepted : ∀ v, ¬ ownPartition.cyclicFlag v
  positivePartition : SccPartition (fun a b => edge a b ∧ 0 < value a ∧ 0 < value b)
  positiveAccepted : ∀ a b, edge a b → 0 < value a → 0 < value b →
    owner a ≠ player → positivePartition.component a = positivePartition.component b → check a b

namespace PartitionChecks

/-- 両方のSCC検査が受理すれば、前回証明した下限保証の条件を満たす。 -/
def certificate {V : Type u} (P : PartitionChecks V) : Certificate V where
  edge := P.edge
  owner := P.owner
  check := P.check
  player := P.player
  value := P.value
  mate := P.mate
  mate_pos := P.mate_pos
  bounded := P.bounded
  monotone := P.monotone
  no_own_cycle := by
    intro a b e back
    apply acyclic_of_core P.own_subset P.basePartition.cyclicFlag
      (fun v cycle => (P.basePartition.cyclic_iff v).1 cycle) _ e back
    intro x y localEdge localBack
    exact P.ownAccepted x ((P.ownPartition.cyclic_iff x).1
      ⟨y, localEdge, ⟨localBack⟩⟩)
  opponent_cycle_checks := by
    intro a b e ha hb back other
    exact opponent_checks_of_partition P.edge P.value P.owner P.check P.player
      P.monotone P.positivePartition P.positiveAccepted e ha hb back other

end PartitionChecks
end PetaProof
