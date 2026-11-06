import PetaProof.ThresholdDeterminacy

/-!
leafと四回出現で終わる有限手順に対する正反両側の保証。
終局区間は最初の出現から四回目までの閉じた歩道全体を使う。
任意の履歴依存戦略に対する終局手順の生成そのものは、ここではまだ扱わない。
-/

namespace PetaProof.Walk

universe u
variable {V : Type u} {R : V → V → Prop} {a b : V}

theorem every_and {P Q : V → V → Prop} (walk : Walk R a b)
    (left : walk.Every P) (right : walk.Every Q) : walk.Every (fun v w => P v w ∧ Q v w) := by
  induction walk with
  | nil => trivial
  | cons _ _ ih => exact ⟨⟨left.1, right.1⟩, ih left.2 right.2⟩

theorem every_mono {P Q : V → V → Prop} (walk : Walk R a b) (all : walk.Every P)
    (implies : ∀ v w, R v w → P v w → Q v w) : walk.Every Q := by
  induction walk with
  | nil => trivial
  | cons edge _ ih => exact ⟨implies _ _ edge all.1, ih all.2⟩

theorem every_map {S : V → V → Prop} (walk : Walk R a b)
    (edges : ∀ v w, R v w → S v w) (P : V → V → Prop) :
    (walk.map edges).Every P ↔ walk.Every P := by
  induction walk with
  | nil => exact Iff.rfl
  | cons _ _ ih => simpa only [map, Every] using and_congr (Iff.refl _) ih

end PetaProof.Walk

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

/-- 固定プレイヤー視点の千日手利得。両者王手なら自分負けを先に置くが、元のモデルはその循環を拒否する。 -/
noncomputable def repetitionValue {R : V → V → Prop} {a b : V}
    (edge : R a b) (back : Walk R b a) : Int := by
  classical
  let loop := Walk.cons edge back
  exact if loop.Every (fun v w => G.owner v = G.player → G.check v w) then -G.mate
    else if loop.Every (fun v w => G.owner v ≠ G.player → G.check v w) then G.mate else 0

/-- 以前の保証検査で使った利得と、同じ条件のもとで完全に一致する。 -/
theorem repetitionValue_eq_certificate (certificate : Certificate V)
    (owner : certificate.owner = G.owner) (check : certificate.check = G.check)
    (player : certificate.player = G.player) (mate : certificate.mate = G.mate)
    {a b : V} (edge : certificate.edge a b) (back : Walk certificate.edge b a) :
    G.repetitionValue edge back = certificate.repetitionPayoff edge back := by
  have own : certificate.OwnChecks = (fun v w => G.owner v = G.player → G.check v w) := by
    funext v w
    simp only [Certificate.OwnChecks, owner, check, player]
  have opponent : certificate.OpponentChecks = (fun v w => G.owner v ≠ G.player → G.check v w) := by
    funext v w
    simp only [Certificate.OpponentChecks, owner, check, player]
  unfold repetitionValue Certificate.repetitionPayoff
  dsimp only
  rw [own, opponent, mate]

/-- 相手の手を固定し、自分の全合法手を残す。 -/
def Replies (response : V → Move V) (v : V) (m : Move V) : Prop :=
  G.legal v m ∧ (G.owner v ≠ G.player → response v = m)

/-- 相手がleafでも反復でも閾値未満に抑える証拠。王手継続中は毎手順位を減らす。 -/
structure RefutationRegion (lost : V → Prop) where
  response : V → Move V
  chosen_legal : ∀ v, lost v → G.owner v ≠ G.player → G.legal v (response v)
  closed : ∀ v, lost v → ∀ m, G.Replies response v m →
    match m with
    | .node w => lost w
    | .leaf score => score < G.threshold
  rank : V → Nat
  strict_checking : ∀ v w, lost v → G.Replies response v (.node w) →
    (G.owner v ≠ G.player → G.check v w) → rank w < rank v

namespace RefutationRegion

variable {G} {lost : V → Prop}

def Internal (region : G.RefutationRegion lost) (v w : V) : Prop :=
  lost v ∧ G.Replies region.response v (.node w)

/-- 反証方策上では、相手が連続王手する非空の閉じた歩道はない。 -/
theorem no_opponent_check_loop (region : G.RefutationRegion lost) {a b : V}
    (edge : region.Internal a b) (back : Walk region.Internal b a) :
    ¬ (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  intro all
  have decreases := region.strict_checking a b edge.1 edge.2 all.1
  have returning := (back.withEvery _ all.2).nat_antitone region.rank
    (fun v w h => Nat.le_of_lt (region.strict_checking v w h.1.1 h.1.2 h.2))
  omega

/-- 反復利得は0以下なので、正の閾値未満である。 -/
theorem repetition_lt (region : G.RefutationRegion lost) {a b : V}
    (edge : region.Internal a b) (back : Walk region.Internal b a) :
    G.repetitionValue edge back < G.threshold := by
  classical
  have no_win := region.no_opponent_check_loop edge back
  have positive := G.positive
  have bound := G.bounded
  by_cases own : (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w)
  · simp only [repetitionValue, if_pos own]
    omega
  · simp only [repetitionValue, if_neg own, if_neg no_win]
    exact positive

/-- rootからどの経路で到達したleafでも、閾値未満になる。 -/
theorem leaf_lt (region : G.RefutationRegion lost) {root v : V}
    (inside : lost root) (stem : Walk region.Internal root v) (score : Int)
    (leaf : G.Replies region.response v (.leaf score)) : score < G.threshold := by
  have child := (Reachable.closed
    (fun x y h _ => region.closed x h.1 (.node y) h.2) ⟨stem⟩ inside)
  exact region.closed v child (.leaf score) leaf

/-- 実際の手順の最初から四回目までの区間にも、反証の上界が成り立つ。 -/
theorem fourfold_lt [DecidableEq V] (region : G.RefutationRegion lost) {root last : V}
    (trace : Walk region.Internal root last) (v : V) (many : 4 ≤ trace.visits.count v) :
    ∃ (stem : Walk region.Internal root v) (next : V) (edge : region.Internal v next)
      (back : Walk region.Internal next v) (suffix : Walk region.Internal v last),
      trace = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 ∧
      G.repetitionValue edge back < G.threshold := by
  obtain ⟨stem, next, edge, back, suffix, original, first, fourth⟩ := trace.fourfold_interval v many
  exact ⟨stem, next, edge, back, suffix, original, first, fourth, region.repetition_lt edge back⟩

end RefutationRegion

namespace RankedRegion

variable {G} {won : V → Prop}

def FiniteInternal (region : G.RankedRegion won) (v w : V) : Prop :=
  won v ∧ G.Follows region.choice v (.node w)

/-- 正側の反復区間では、相手の全着手が王手になる。 -/
theorem finite_loop_opponent_checks (region : G.RankedRegion won) {a b : V}
    (edge : region.FiniteInternal a b) (back : Walk region.FiniteInternal b a) :
    (Walk.cons edge back).Every (fun v w => G.owner v ≠ G.player → G.check v w) := by
  apply Walk.every_returning _ _ (Walk.cons edge back) (.nil a)
  intro v w e returning other
  exact region.positional.cycle_checks v w e.1 e.2 returning other

/-- 双方王手の閉路を拒否する元の仮定から、自分の連続王手負けも排除できる。 -/
theorem finite_loop_not_own_checks (region : G.RankedRegion won) {a b : V}
    (edge : region.FiniteInternal a b) (back : Walk region.FiniteInternal b a) :
    ¬ (Walk.cons edge back).Every (fun v w => G.owner v = G.player → G.check v w) := by
  intro own
  let loop := Walk.cons edge back
  have opponent := region.finite_loop_opponent_checks edge back
  have checks : loop.Every G.check := loop.every_mono (loop.every_and own opponent) (by
    intro v w _ both
    by_cases self : G.owner v = G.player
    · exact both.1 self
    · exact both.2 self)
  exact G.no_mutual_cycle a b ⟨edge.2.1, checks.1⟩
    ((back.withEvery _ checks.2).map (fun _ _ h => ⟨h.1.2.1, h.2⟩))

theorem finite_repetition_ge (region : G.RankedRegion won) {a b : V}
    (edge : region.FiniteInternal a b) (back : Walk region.FiniteInternal b a) :
    G.threshold ≤ G.repetitionValue edge back := by
  classical
  have own := region.finite_loop_not_own_checks edge back
  have opponent := region.finite_loop_opponent_checks edge back
  simp only [repetitionValue, if_neg own, if_pos opponent]
  exact G.bounded

theorem finite_leaf_ge (region : G.RankedRegion won) {root v : V} (inside : won root)
    (stem : Walk region.FiniteInternal root v) (score : Int)
    (leaf : G.Follows region.choice v (.leaf score)) : G.threshold ≤ score := by
  have child := (Reachable.closed
    (fun x y h _ => region.closed x h.1 (.node y) h.2) ⟨stem⟩ inside)
  exact region.closed v child (.leaf score) leaf

theorem finite_fourfold_ge [DecidableEq V] (region : G.RankedRegion won) {root last : V}
    (trace : Walk region.FiniteInternal root last) (v : V) (many : 4 ≤ trace.visits.count v) :
    ∃ (stem : Walk region.FiniteInternal root v) (next : V) (edge : region.FiniteInternal v next)
      (back : Walk region.FiniteInternal next v) (suffix : Walk region.FiniteInternal v last),
      trace = (stem.append (.cons edge back)).append suffix ∧
      stem.visits.count v = 1 ∧ (Walk.cons edge back).visits.count v = 4 ∧
      G.threshold ≤ G.repetitionValue edge back := by
  obtain ⟨stem, next, edge, back, suffix, original, first, fourth⟩ := trace.fourfold_interval v many
  exact ⟨stem, next, edge, back, suffix, original, first, fourth, region.finite_repetition_ge edge back⟩

end RankedRegion
end PetaProof.ThresholdGame
