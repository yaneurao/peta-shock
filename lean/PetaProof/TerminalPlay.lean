import PetaProof.FiniteRefutation

/-!
全履歴に依存する合法な選択から、最初のleafまたは四回出現までの手順を生成する。
途中で四回出現した後に探索を続けた手順は終局証拠として受け入れない。
-/

namespace PetaProof.Walk

universe u
variable {V : Type u} {R : V → V → Prop} {a b c : V}

theorem visits_snoc (trace : Walk R a b) (edge : R b c) :
    (trace.append (.cons edge (.nil c))).visits = trace.visits ++ [c] := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa only [append, visits, List.cons_append] using congrArg (List.cons _) (ih edge)

theorem steps_snoc (trace : Walk R a b) (edge : R b c) :
    (trace.append (.cons edge (.nil c))).steps = trace.steps + 1 := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [append, steps, ih]

/-- pastは現在頂点を含まない古い順の履歴。選択には現在頂点を末尾に加えて渡す。 -/
def Selected (choose : List V → V → Move V) (past : List V) :
    {a b : V} → Walk R a b → Prop
  | _, _, .nil _ => True
  | a, _, .cons (b := b) _ tail =>
    choose (past ++ [a]) a = .node b ∧ Selected choose (past ++ [a]) tail

theorem selected_snoc (choose : List V → V → Move V) (trace : Walk R a b)
    (past : List V) (selected : trace.Selected choose past) (edge : R b c)
    (last : choose (past ++ trace.visits) b = .node c) :
    (trace.append (.cons edge (.nil c))).Selected choose past := by
  induction trace generalizing past with
  | nil => exact ⟨last, trivial⟩
  | cons _ tail ih =>
    refine ⟨selected.1, ih (past ++ [_]) selected.2 edge ?_⟩
    simpa only [visits, List.append_assoc, List.singleton_append] using last

/-- 履歴依存の選択でも、各手で不変条件を保てば全歩道で保持される。 -/
theorem selected_invariant (choose : List V → V → Move V) (domain : V → Prop)
    (P : V → V → Prop)
    (step : ∀ history v w, domain v → R v w → choose history v = .node w →
      domain w ∧ P v w)
    (trace : Walk R a b) (past : List V) (inside : domain a)
    (selected : trace.Selected choose past) : domain b ∧ trace.Every P := by
  induction trace generalizing past with
  | nil => exact ⟨inside, trivial⟩
  | cons edge tail ih =>
    have next := step (past ++ [_]) _ _ inside edge selected.1
    have rest := ih (past ++ [_]) next.1 selected.2
    exact ⟨rest.1, next.2, rest.2⟩

theorem every_append (left : Walk R a b) (right : Walk R b c) (P : V → V → Prop) :
    (left.append right).Every P ↔ left.Every P ∧ right.Every P := by
  induction left with
  | nil => simp only [append, Every, true_and]
  | cons _ _ ih => simp only [append, Every, ih, and_assoc]

theorem every_withEvery (trace : Walk R a b) (P Q : V → V → Prop) (all : trace.Every P) :
    (trace.withEvery P all).Every Q ↔ trace.Every Q := by
  induction trace with
  | nil => exact Iff.rfl
  | cons _ _ ih => simpa only [withEvery, Every] using and_congr (Iff.refl _) (ih all.2)

end PetaProof.Walk

namespace PetaProof.ThresholdGame

universe u
variable {V : Type u} (G : ThresholdGame V)

def LegalNode (v w : V) : Prop := G.legal v (.node w)

/-- 各手を過去の全訪問列と現在局面から選ぶ全域な合法計画。各プレイヤーの戦略にも用いる。 -/
structure MovePlan where
  choose : List V → V → Move V
  legal : ∀ history v, G.legal v (choose history v)

noncomputable def defaultPlan : G.MovePlan where
  choose := fun _ v => Classical.choose (G.nonempty_moves v)
  legal := fun _ v => Classical.choose_spec (G.nonempty_moves v)

/-- 自分の手番はself、相手の手番はopponentを使う。履歴は双方に全て渡す。 -/
def combinePlans (self opponent : G.MovePlan) : G.MovePlan where
  choose := fun history v => if G.owner v = G.player then self.choose history v else opponent.choose history v
  legal := by
    intro history v
    by_cases own : G.owner v = G.player
    · simpa only [if_pos own] using self.legal history v
    · simpa only [if_neg own] using opponent.legal history v

/-- 最初に終局した実際の手順。四回出現の利得は最初から四回目までの区間全体で計算する。 -/
inductive TerminalResult [DecidableEq V] (plan : G.MovePlan) (root : V) : Int → Type u where
  | leaf {v : V} (trace : Walk G.LegalNode root v)
      (selected : trace.Selected plan.choose [])
      (quiet : ∀ w, trace.visits.count w < 4)
      (score : Int) (legal : G.legal v (.leaf score))
      (last : plan.choose trace.visits v = .leaf score) : TerminalResult plan root score
  | repetition {last v next : V} (trace : Walk G.LegalNode root last)
      (selected : trace.Selected plan.choose [])
      (earliest : ∀ w, trace.visits.dropLast.count w < 4)
      (stem : Walk G.LegalNode root v) (edge : G.LegalNode v next)
      (back : Walk G.LegalNode next v) (suffix : Walk G.LegalNode v last)
      (original : trace = (stem.append (.cons edge back)).append suffix)
      (first : stem.visits.count v = 1) (fourth : (Walk.cons edge back).visits.count v = 4) :
      TerminalResult plan root (G.repetitionValue edge back)

/-- まだ終局していない実行を、残りの有限手数で終局証拠へ延長する。 -/
theorem terminal_extension [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (plan : G.MovePlan) (root : V) (fuel : Nat) {v : V} (trace : Walk G.LegalNode root v)
    (selected : trace.Selected plan.choose []) (quiet : ∀ w, trace.visits.count w < 4)
    (bound : 3 * vertices.length ≤ trace.steps + fuel) :
    ∃ payoff, Nonempty (G.TerminalResult plan root payoff) := by
  classical
  induction fuel generalizing v with
  | zero =>
    have short := trace.steps_before_fourfold vertices (fun w _ => covered w) (fun w _ => quiet w)
    simp only [Nat.add_zero] at bound
    omega
  | succ fuel ih =>
    cases command : plan.choose trace.visits v with
    | leaf score =>
      have legal : G.legal v (.leaf score) := by rw [← command]; exact plan.legal trace.visits v
      exact ⟨score, ⟨.leaf trace selected quiet score legal command⟩⟩
    | node w =>
      have legal : G.LegalNode v w := by change G.legal v (.node w); rw [← command]; exact plan.legal trace.visits v
      let next := trace.append (.cons legal (.nil w))
      have next_selected : next.Selected plan.choose [] :=
        trace.selected_snoc plan.choose [] selected legal command
      by_cases next_quiet : ∀ x, next.visits.count x < 4
      · have length : next.steps = trace.steps + 1 := trace.steps_snoc legal
        exact ih next next_selected next_quiet (by omega)
      · have repeated : ∃ x, 4 ≤ next.visits.count x := by
          apply Classical.byContradiction
          intro none
          apply next_quiet
          intro x
          have not_many : ¬ 4 ≤ next.visits.count x := fun h => none ⟨x, h⟩
          omega
        obtain ⟨x, many⟩ := repeated
        obtain ⟨stem, middle, edge, back, suffix, original, first, fourth⟩ := next.fourfold_interval x many
        have earliest : ∀ x, next.visits.dropLast.count x < 4 := by
          intro x
          change (trace.append (.cons legal (.nil w))).visits.dropLast.count x < 4
          rw [trace.visits_snoc legal, List.dropLast_concat]
          exact quiet x
        exact ⟨G.repetitionValue edge back,
          ⟨.repetition next next_selected earliest stem edge back suffix original first fourth⟩⟩

/-- 任意の合法な全履歴依存計画に、leafまたは最初の四回出現で終わる手順が実在する。 -/
theorem terminal_result_exists [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    (plan : G.MovePlan) (root : V) : ∃ payoff, Nonempty (G.TerminalResult plan root payoff) := by
  apply G.terminal_extension vertices covered plan root (3 * vertices.length) (.nil root) trivial
  · intro w
    by_cases same : root = w <;> simp [Walk.visits, same]
  · simp only [Walk.steps, Nat.zero_add, Nat.le_refl]

/-- leafを指す最後の1手も含めた終局までの手数。 -/
def TerminalResult.plies [DecidableEq V] {plan : G.MovePlan} {root : V} {payoff : Int} :
    G.TerminalResult plan root payoff → Nat
  | .leaf trace _ _ _ _ _ => trace.steps + 1
  | .repetition trace _ _ _ _ _ _ _ _ _ => trace.steps

/-- leafも四回出現も、N局面の列挙に対して3N手以内に起きる。 -/
theorem TerminalResult.plies_bound [DecidableEq V] (vertices : List V) (covered : ∀ v, v ∈ vertices)
    {plan : G.MovePlan} {root : V} {payoff : Int} (result : G.TerminalResult plan root payoff) :
    result.plies ≤ 3 * vertices.length := by
  cases result with
  | leaf trace _ quiet _ _ _ =>
    have short := trace.steps_before_fourfold vertices (fun v _ => covered v) (fun v _ => quiet v)
    change trace.steps + 1 ≤ _
    omega
  | repetition trace _ earliest _ _ _ _ _ _ _ =>
    have bound := history_length_bound vertices trace.visits.dropLast 4
      (fun v _ => covered v) (fun v _ => earliest v)
    rw [List.length_dropLast, trace.visits_length] at bound
    change trace.steps ≤ _
    simp only [Nat.add_sub_cancel, Nat.reduceSub] at bound
    omega

/-- 辺に方策の証拠を追加しても、反復利得は変わらない。 -/
theorem repetitionValue_restrict {R P : V → V → Prop} {a b : V}
    (edge : R a b) (back : Walk R b a) (head : P a b) (all : back.Every P) :
    G.repetitionValue (show R a b ∧ P a b from ⟨edge, head⟩) (back.withEvery P all) =
      G.repetitionValue edge back := by
  classical
  unfold repetitionValue
  dsimp only
  simp only [Walk.Every, back.every_withEvery P]
  split <;> simp_all

theorem repetitionValue_map {R S : V → V → Prop} {a b : V}
    (edge : R a b) (back : Walk R b a) (mapEdge : ∀ v w, R v w → S v w) :
    G.repetitionValue (mapEdge a b edge) (back.map mapEdge) = G.repetitionValue edge back := by
  classical
  unfold repetitionValue
  dsimp only
  simp only [Walk.Every, back.every_map mapEdge]
  split <;> simp_all

end PetaProof.ThresholdGame
