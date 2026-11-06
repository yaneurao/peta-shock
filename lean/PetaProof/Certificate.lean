import Std

/-!
保証検査の意味論。leaf評価値の正確さは仮定せず、入力の終端利得として扱う。
C++のSCC実装そのものではなく、その検査が満たすべき条件から保証を導く。
-/

namespace PetaProof

universe u

/-- 同じ頂点を複数回通ってよい有限の歩道。nilは長さ0。 -/
inductive Walk {V : Type u} (R : V → V → Prop) : V → V → Type u where
  | nil (v) : Walk R v v
  | cons {a b c} : R a b → Walk R b c → Walk R a c

namespace Walk

variable {V : Type u} {R S : V → V → Prop} {a b c : V}

def append : {a b c : V} → Walk R a b → Walk R b c → Walk R a c
  | _, _, _, .nil _, k => k
  | _, _, _, .cons e tail, k => .cons e (append tail k)

def map : {a b : V} → Walk R a b → (∀ x y, R x y → S x y) → Walk S a b
  | _, _, .nil v, _ => .nil v
  | _, _, .cons e tail, f => .cons (f _ _ e) (map tail f)

/-- 頂点の表現も変える写像。部分型の局面から元の局面へ戻すときに使う。 -/
def mapVertices {W : Type u} {T : W → W → Prop} (f : V → W)
    (preserves : ∀ x y, R x y → T (f x) (f y)) :
    {a b : V} → Walk R a b → Walk T (f a) (f b)
  | _, _, .nil v => .nil (f v)
  | _, _, .cons e tail => .cons (preserves _ _ e) (mapVertices f preserves tail)

/-- 歩道の全着手に成り立つ性質。単純閉路に限定しない。 -/
def Every (P : V → V → Prop) : {a b : V} → Walk R a b → Prop
  | _, _, .nil _ => True
  | a, _, .cons (b := b) _ tail => P a b ∧ Every P tail

theorem every_true (h : Walk R a b) : h.Every (fun _ _ => True) := by
  induction h with
  | nil => trivial
  | cons _ _ ih => exact ⟨True.intro, ih⟩

theorem monotone (f : V → Int) (mono : ∀ x y, R x y → f x ≤ f y)
    (h : Walk R a b) : f a ≤ f b := by
  induction h with
  | nil => exact Int.le_refl _
  | cons e tail ih => exact Int.le_trans (mono _ _ e) ih

/-- 閉じた歩道上の各枝は、残りの歩道を使って始点へ戻れる。SCC検査との接点。 -/
theorem every_returning (P : V → V → Prop)
    (stepProperty : ∀ x y, R x y → Walk R y x → P x y)
    (h : Walk R a b) (back : Walk R b a) : h.Every P := by
  induction h with
  | nil => trivial
  | cons e tail ih =>
      exact ⟨stepProperty _ _ e (tail.append back), ih (back.append (.cons e (.nil _)))⟩

theorem every_returning_above (f : V → Int)
    (mono : ∀ x y, R x y → f x ≤ f y) (t : Int) (P : V → V → Prop)
    (stepProperty : ∀ x y, R x y → t ≤ f x → t ≤ f y → Walk R y x → P x y)
    (h : Walk R a b) (back : Walk R b a) (lower : t ≤ f a) : h.Every P := by
  induction h with
  | nil => trivial
  | cons e tail ih =>
      have next := Int.le_trans lower (mono _ _ e)
      exact ⟨stepProperty _ _ e lower next (tail.append back),
        ih (back.append (.cons e (.nil _))) next⟩

/-- 単調な値の下限を歩道の全頂点へ持ち上げ、枝条件も追加する。 -/
def restrict (f : V → Int) (mono : ∀ x y, R x y → f x ≤ f y)
    (t : Int) (P : V → V → Prop) : {a b : V} → (h : Walk R a b) →
    t ≤ f a → h.Every P →
    Walk (fun x y => R x y ∧ t ≤ f x ∧ t ≤ f y ∧ P x y) a b
  | _, _, .nil v, _, _ => .nil v
  | _, _, .cons e tail, lower, all =>
      let next := Int.le_trans lower (mono _ _ e)
      .cons ⟨e, lower, next, all.1⟩ (restrict f mono t P tail next all.2)

/-- 辺を削ったグラフで新たな閉じた歩道が生じることはない。 -/
theorem no_cycle_of_subrelation
    (sub : ∀ x y, S x y → R x y)
    (acyclic : ∀ x y, R x y → Walk R y x → False)
    (e : S a b) (back : Walk S b a) : False :=
  acyclic a b (sub a b e) (back.map sub)

/-- 全着手について確認した性質を、実際の枝の条件へ移す。 -/
def withEvery (P : V → V → Prop) : {a b : V} → (h : Walk R a b) →
    h.Every P → Walk (fun x y => R x y ∧ P x y) a b
  | _, _, .nil v, _ => .nil v
  | _, _, .cons e tail, all => .cons ⟨e, all.1⟩ (withEvery P tail all.2)

/-- 逆辺上の歩道を、元の向きの逆順の歩道へ戻す。 -/
def reverse : {a b : V} → Walk (fun x y => R y x) a b → Walk R b a
  | _, _, .nil v => .nil v
  | _, _, .cons e tail => (reverse tail).append (.cons e (.nil _))

theorem nat_monotone (f : V → Nat) (mono : ∀ x y, R x y → f x ≤ f y)
    (h : Walk R a b) : f a ≤ f b := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons e _ ih => exact Nat.le_trans (mono _ _ e) ih

theorem nat_antitone (f : V → Nat) (anti : ∀ x y, R x y → f y ≤ f x)
    (h : Walk R a b) : f b ≤ f a := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons e _ ih => exact Nat.le_trans ih (anti _ _ e)

end Walk

/-- 手番側視点の値を、固定したプレイヤーpの視点へ変換する。 -/
def perspective {V : Type u} (owner : V → Bool) (value : V → Int)
    (p : Bool) (v : V) : Int := if owner v = p then value v else -value v

/-- C++の局所minimax検査から、方策に従った内部手での値の単調性を導く。 -/
theorem negamax_monotone {V : Type u} (owner : V → Bool) (value : V → Int)
    (p : Bool) (a b : V) (alternate : owner b ≠ owner a)
    (upper : -value b ≤ value a)
    (chosen : owner a = p → -value b = value a) :
    perspective owner value p a ≤ perspective owner value p b := by
  cases ha : owner a <;> cases hb : owner b <;> cases p <;>
    simp_all [perspective] <;> omega

/-- 同じ局所検査から、採用可能なleaf手の終端利得の下限を導く。 -/
theorem negamax_leaf {V : Type u} (owner : V → Bool) (value : V → Int)
    (p : Bool) (v : V) (score : Int) (upper : score ≤ value v)
    (chosen : owner v = p → score = value v) :
    perspective owner value p v ≤ (if owner v = p then score else -score) := by
  by_cases h : owner v = p <;> simp_all [perspective] <;> omega

/-- 固定プレイヤーの候補手と相手の全応手を残したグラフに対する検査条件。 -/
structure Certificate (V : Type u) where
  edge : V → V → Prop
  owner : V → Bool
  check : V → V → Prop
  player : Bool
  value : V → Int
  mate : Int
  mate_pos : 0 < mate
  bounded : ∀ v, -mate ≤ value v ∧ value v ≤ mate
  monotone : ∀ a b, edge a b → value a ≤ value b
  /-- 自分が王手を継続する枝だけを残した、-Mateより良い領域に循環がない。 -/
  no_own_cycle : ∀ a b,
    (edge a b ∧ -mate < value a ∧ -mate < value b ∧
      (owner a = player → check a b)) →
    Walk (fun x y => edge x y ∧ -mate < value x ∧ -mate < value y ∧
      (owner x = player → check x y)) b a → False
  /-- 正の領域で循環に含まれる相手の枝は、すべて王手である。 -/
  opponent_cycle_checks : ∀ a b, edge a b → 0 < value a → 0 < value b →
    Walk edge b a → owner a ≠ player → check a b

namespace Certificate

variable {V : Type u} (C : Certificate V)

def OwnChecks (a b : V) : Prop := C.owner a = C.player → C.check a b
def OpponentChecks (a b : V) : Prop := C.owner a ≠ C.player → C.check a b

/-- 正の約束値を持つ閉じた歩道では、相手が全着手で王手している。 -/
theorem positive_loop_opponent_checks {a b : V} (e : C.edge a b)
    (back : Walk C.edge b a) (positive : 0 < C.value a) :
    (Walk.cons e back).Every C.OpponentChecks := by
  apply Walk.every_returning_above C.value C.monotone 1 C.OpponentChecks _
    (.cons e back) (.nil a) (by omega)
  intro x y ex lx ly ret hx
  exact C.opponent_cycle_checks x y ex (by omega) (by omega) ret hx

/-- -Mateより良い約束値なら、自分だけが王手し続ける閉じた歩道は許されない。 -/
theorem loop_not_own_checks {a b : V} (e : C.edge a b)
    (back : Walk C.edge b a) (better : -C.mate < C.value a) :
    ¬ (Walk.cons e back).Every C.OwnChecks := by
  intro all
  have next : -C.mate < C.value b := by have := C.monotone a b e; omega
  apply C.no_own_cycle a b ⟨e, better, next, all.1⟩
  have lifted := back.restrict C.value C.monotone (-C.mate + 1)
    C.OwnChecks (by omega) all.2
  exact lifted.map (by
    intro x y h
    exact ⟨h.1, by omega, by omega, h.2.2.2⟩)

/-- 反復区間の利得。双方連続王手では自分負けを先に置くが、保証値>-Mateなら既に拒否される。 -/
noncomputable def repetitionPayoff {a b : V} (e : C.edge a b)
    (back : Walk C.edge b a) : Int := by
  classical
  exact if (Walk.cons e back).Every C.OwnChecks then -C.mate
    else if (Walk.cons e back).Every C.OpponentChecks then C.mate else 0

/-- 閉じた歩道による終局利得は、その区間の始点の約束値を下回らない。 -/
theorem repetition_guarantee {a b : V} (e : C.edge a b)
    (back : Walk C.edge b a) : C.value a ≤ C.repetitionPayoff e back := by
  classical
  unfold repetitionPayoff
  split
  · rename_i own
    have not_better : ¬ -C.mate < C.value a := by
      intro better
      exact C.loop_not_own_checks e back better own
    omega
  · split
    · exact (C.bounded a).2
    · rename_i _ opponent
      have nonpositive : ¬ 0 < C.value a := by
        intro positive
        exact opponent (C.positive_loop_opponent_checks e back positive)
      omega

/-- rootから反復区間へ至る道があっても、rootの約束値は保たれる。 -/
theorem repetition_from_root {root a b : V} (stem : Walk C.edge root a)
    (e : C.edge a b) (back : Walk C.edge b a) :
    C.value root ≤ C.repetitionPayoff e back :=
  Int.le_trans (stem.monotone C.value C.monotone) (C.repetition_guarantee e back)

/-- leaf出口についても、局所的な下限条件と内部手の単調性でrootまで保証が届く。 -/
theorem leaf_from_root {root v : V} (stem : Walk C.edge root v)
    (payoff : Int) (leaf_lower : C.value v ≤ payoff) : C.value root ≤ payoff :=
  Int.le_trans (stem.monotone C.value C.monotone) leaf_lower

/-- 許可候補を減らしても保証検査条件は保たれる。新旧候補の安全な和集合からの制限にも使える。 -/
def restrictEdges (S : V → V → Prop) (sub : ∀ a b, S a b → C.edge a b) :
    Certificate V where
  edge := S
  owner := C.owner
  check := C.check
  player := C.player
  value := C.value
  mate := C.mate
  mate_pos := C.mate_pos
  bounded := C.bounded
  monotone := fun a b e => C.monotone a b (sub a b e)
  no_own_cycle := by
    intro a b e back
    apply C.no_own_cycle a b ⟨sub a b e.1, e.2⟩
    exact back.map (fun x y h => ⟨sub x y h.1, h.2⟩)
  opponent_cycle_checks := by
    intro a b e ha hb back other
    exact C.opponent_cycle_checks a b (sub a b e) ha hb (back.map sub) other

/-- 実対局の「leafに出る」または「反復で終局」の有限な証拠。
四回目かどうかを要求していない。どの非空反復区間にも成立する強い条件で証明する。 -/
inductive Outcome (root : V) : Int → Type u where
  | leaf {v : V} (stem : Walk C.edge root v) (payoff : Int)
      (leaf_lower : C.value v ≤ payoff) : Outcome root payoff
  | repetition {a b : V} (stem : Walk C.edge root a)
      (e : C.edge a b) (back : Walk C.edge b a) :
      Outcome root (C.repetitionPayoff e back)

/-- 保証検査の中心命題。受理されたグラフ上の任意の有限終局は約束値を下回らない。 -/
theorem sound {root : V} {payoff : Int} (outcome : C.Outcome root payoff) :
    C.value root ≤ payoff := by
  cases outcome with
  | leaf => exact C.leaf_from_root (by assumption) _ (by assumption)
  | repetition stem e back => exact C.repetition_from_root stem e back

/-- 双方の下限保証が同じ値を挟むなら、その対戦結果はその値に一致する。 -/
theorem opposite_guarantees (value payoff : Int)
    (lower : value ≤ payoff) (upper : -value ≤ -payoff) : payoff = value := by
  omega

end Certificate
end PetaProof
