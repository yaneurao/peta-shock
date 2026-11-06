import PetaProof.Certificate

/-!
王手循環の検査を事前計算したcore内に限定してよいことの証明。
ここではSCCを実装せず、「循環に含まれる頂点」を到達可能性から定義する。
-/

namespace PetaProof

universe u
variable {V : Type u} {R S : V → V → Prop}

/-- 長さ1以上の閉じた歩道に含まれる頂点。自己ループも含む。 -/
def CyclicVertex (R : V → V → Prop) (v : V) : Prop :=
  ∃ w, R v w ∧ Nonempty (Walk R w v)

theorem cyclic_target {a b : V} (e : R a b) (back : Walk R b a) :
    CyclicVertex R b := by
  cases back with
  | nil => exact ⟨_, e, ⟨.nil _⟩⟩
  | cons first tail => exact ⟨_, first, ⟨tail.append (.cons e (.nil _))⟩⟩

/-- 枝の削除で新しい循環頂点は生じない。 -/
theorem cyclic_subrelation (sub : ∀ a b, S a b → R a b)
    {v : V} (h : CyclicVertex S v) : CyclicVertex R v := by
  obtain ⟨w, e, ⟨back⟩⟩ := h
  exact ⟨w, sub v w e, ⟨back.map sub⟩⟩

/-- Sの閉じた歩道の全枝は、元のグラフRの循環頂点間にある。 -/
theorem closed_walk_in_core (sub : ∀ a b, S a b → R a b)
    {a b : V} (e : S a b) (back : Walk S b a) :
    (Walk.cons e back).Every (fun x y => CyclicVertex R x ∧ CyclicVertex R y) := by
  apply Walk.every_returning _ _ (.cons e back) (.nil a)
  intro x y ex ret
  exact ⟨⟨y, sub x y ex, ⟨ret.map sub⟩⟩, cyclic_target (sub x y ex) (ret.map sub)⟩

/-- 元グラフの循環頂点を全て含むcoreだけでSを検査しても、Sの循環を見落とさない。 -/
theorem acyclic_of_core (sub : ∀ a b, S a b → R a b)
    (core : V → Prop) (covers : ∀ v, CyclicVertex R v → core v)
    (localAcyclic : ∀ a b, (S a b ∧ core a ∧ core b) →
      Walk (fun x y => S x y ∧ core x ∧ core y) b a → False)
    {a b : V} (e : S a b) (back : Walk S b a) : False := by
  have all := closed_walk_in_core sub e back
  -- 長さ0の歩道ではなく、元の先頭枝を残したまま局所検査へ渡す。
  apply localAcyclic a b ⟨e, covers a all.1.1, covers b all.1.2⟩
  exact (back.withEvery _ all.2).map
    (fun x y h => ⟨h.1, covers x h.2.1, covers y h.2.2⟩)

/-- 正の値の部分グラフのSCC番号に関するC++検査から、反復区間の王手条件を導く。
component_correctはSCC実装との対応に必要な前提であり、このファイルでは証明しない。 -/
theorem opponent_checks_of_scc (edge : V → V → Prop) (value : V → Int)
    (owner : V → Bool) (check : V → V → Prop) (player : Bool)
    (mono : ∀ a b, edge a b → value a ≤ value b)
    (component : V → Nat)
    (component_correct : ∀ a b,
      Walk (fun x y => edge x y ∧ 0 < value x ∧ 0 < value y) a b →
      Walk (fun x y => edge x y ∧ 0 < value x ∧ 0 < value y) b a →
      component a = component b)
    (checked : ∀ a b, edge a b → 0 < value a → 0 < value b →
      owner a ≠ player → component a = component b → check a b)
    {a b : V} (e : edge a b) (ha : 0 < value a) (hb : 0 < value b)
    (back : Walk edge b a) (other : owner a ≠ player) : check a b := by
  have lifted := back.restrict value mono 1 (fun _ _ => True) (by omega)
    back.every_true
  have positiveBack : Walk (fun x y => edge x y ∧ 0 < value x ∧ 0 < value y) b a :=
    lifted.map (by
      intro x y h
      exact ⟨h.1, by omega, by omega⟩)
  exact checked a b e ha hb other
    (component_correct a b (.cons ⟨e, ha, hb⟩ (.nil b)) positiveBack)

end PetaProof
