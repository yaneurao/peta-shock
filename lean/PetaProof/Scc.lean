import PetaProof.Localization

/-!
SCC分割の証拠を、局所的な辺・順位条件から検証する。
C++のKosaraju実装そのものの証明ではない。成分番号の単調性と往復の森を使う。
-/

namespace PetaProof

universe u
variable {V : Type u} {R : V → V → Prop}

/-- 各頂点から同じ成分の代表へ至る森。順位の厳密な減少により循環を防ぐ。 -/
structure ReachForest (R : V → V → Prop) where
  root : V → V
  parent : V → V
  rank : V → Nat
  step : ∀ v, v ≠ root v → R v (parent v)
  root_parent : ∀ v, v ≠ root v → root (parent v) = root v
  decreasing : ∀ v, v ≠ root v → rank (parent v) < rank v

namespace ReachForest

/-- 森の局所条件から、実際の有限歩道が存在することを導く。 -/
theorem reaches_root (F : ReachForest R) (v : V) : Nonempty (Walk R v (F.root v)) := by
  generalize hv : F.rank v = n
  induction n using Nat.strongRecOn generalizing v with
  | ind n ih =>
    by_cases done : v = F.root v
    · rw [← done]
      exact ⟨.nil v⟩
    · obtain ⟨tail⟩ := ih (F.rank (F.parent v)) (by
        have := F.decreasing v done
        omega) (F.parent v) rfl
      rw [F.root_parent v done] at tail
      exact ⟨.cons (F.step v done) tail⟩

end ReachForest

/-- 成分番号は辺の向きに非減少。同じ番号内は強連結である。 -/
structure SccPartition (R : V → V → Prop) where
  component : V → Nat
  ordered : ∀ a b, R a b → component a ≤ component b
  connected : ∀ a b, component a = component b → Nonempty (Walk R a b)

namespace SccPartition

/-- C++の成分サイズと自己ループによる循環フラグの、集合としての仕様。 -/
def cyclicFlag (P : SccPartition R) (v : V) : Prop :=
  R v v ∨ ∃ w, w ≠ v ∧ P.component v = P.component w

/-- トポロジカル順の番号と往復の森から、SCC分割の証拠を構成できる。 -/
def ofForests (component : V → Nat)
    (ordered : ∀ a b, R a b → component a ≤ component b)
    (inward : ReachForest R) (outward : ReachForest (fun x y => R y x))
    (roots_match : ∀ v, inward.root v = outward.root v)
    (shared_root : ∀ a b, component a = component b → inward.root a = inward.root b) :
    SccPartition R where
  component := component
  ordered := ordered
  connected := by
    intro a b same
    obtain ⟨toRoot⟩ := inward.reaches_root a
    obtain ⟨fromRoot⟩ := outward.reaches_root b
    have out := fromRoot.reverse
    rw [← roots_match b, ← shared_root a b same] at out
    exact ⟨toRoot.append out⟩

/-- この証拠を持つ成分番号は、単なる近似ではなく相互到達可能性と一致する。 -/
theorem same_iff (P : SccPartition R) (a b : V) :
    P.component a = P.component b ↔
      Nonempty (Walk R a b) ∧ Nonempty (Walk R b a) := by
  constructor
  · intro same
    exact ⟨P.connected a b same, P.connected b a same.symm⟩
  · rintro ⟨⟨forward⟩, ⟨backward⟩⟩
    have h₁ := forward.nat_monotone P.component P.ordered
    have h₂ := backward.nat_monotone P.component P.ordered
    omega

/-- C++の「2頂点以上の成分、または自己ループ」が循環頂点と一致する根拠。 -/
theorem cyclic_iff (P : SccPartition R) (v : V) :
    CyclicVertex R v ↔ R v v ∨ ∃ w, w ≠ v ∧ P.component v = P.component w := by
  constructor
  · rintro ⟨w, e, ⟨back⟩⟩
    by_cases same : w = v
    · exact Or.inl (same ▸ e)
    · exact Or.inr ⟨w, same, (P.same_iff v w).2
        ⟨⟨.cons e (.nil w)⟩, ⟨back⟩⟩⟩
  · rintro (self | ⟨w, different, same⟩)
    · exact ⟨v, self, ⟨.nil v⟩⟩
    · obtain ⟨forward⟩ := P.connected v w same
      obtain ⟨backward⟩ := P.connected w v same.symm
      cases forward with
      | nil => exact False.elim (different rfl)
      | cons e tail => exact ⟨_, e, ⟨tail.append backward⟩⟩

end SccPartition

/-- SCC分割の証拠を使い、正の領域の成分検査から相手の王手条件を得る。 -/
theorem opponent_checks_of_partition (edge : V → V → Prop) (value : V → Int)
    (owner : V → Bool) (check : V → V → Prop) (player : Bool)
    (mono : ∀ a b, edge a b → value a ≤ value b)
    (partition : SccPartition (fun x y => edge x y ∧ 0 < value x ∧ 0 < value y))
    (checked : ∀ a b, edge a b → 0 < value a → 0 < value b →
      owner a ≠ player → partition.component a = partition.component b → check a b)
    {a b : V} (e : edge a b) (ha : 0 < value a) (hb : 0 < value b)
    (back : Walk edge b a) (other : owner a ≠ player) : check a b := by
  apply opponent_checks_of_scc edge value owner check player mono partition.component
    (fun x y forward backward => (partition.same_iff x y).2 ⟨⟨forward⟩, ⟨backward⟩⟩)
    checked e ha hb back other

end PetaProof
