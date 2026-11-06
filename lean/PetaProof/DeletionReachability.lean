import PetaProof.FiniteDeletionResponse
import PetaProof.EscapeLayers

/-! 違反辺を単一目標へ付け替え、同期削除を手番反転した到達ゲームへ帰着する。 -/
namespace PetaProof.HistoryArena

variable {n : Nat} {A : HistoryArena (Fin n)}

/-- 生存集合は毎回減少するため、次段の継続条件だけでも次段の生存を表す。 -/
theorem goodIter_step_iff (k : Nat) (v : Fin n) :
    A.goodIter (k + 1) v ↔ A.StayGood (A.goodIter k) v := by
  constructor
  · exact And.right
  · intro stays
    refine ⟨?_, stays⟩
    induction k with
    | zero => trivial
    | succ k ih =>
      have earlier := A.stayGood_mono (fun _ alive => alive.1) stays
      exact ⟨ih earlier, earlier⟩

namespace DeletionInput

variable (input : DeletionInput A)

/-- noneは到達目標。違反辺はそこで直ちに到達成功とする。 -/
def redirect (v w : Fin n) : Option (Fin n) := if input.bad v w then none else some w

def reachNext : Option (Fin n) → List (Option (Fin n))
  | none => [none]
  | some v => (input.next v).map (input.redirect v)

def reachArena : HistoryArena (Option (Fin n)) where
  edge := fun v w => w ∈ input.reachNext v
  owner := fun v => match v with | none => !A.player | some v => A.owner v
  player := !A.player
  bad := fun _ _ => False
  moves_exist := by
    intro v
    cases v with
    | none => exact ⟨none, by simp [reachNext]⟩
    | some v =>
      obtain ⟨w, edge⟩ := A.moves_exist v
      exact ⟨input.redirect v w, List.mem_map.mpr ⟨w, (input.edges v w).mpr edge, rfl⟩⟩

theorem reach_edge_goal (v : Fin n) : input.reachArena.edge (some v) none ↔
    ∃ w, A.edge v w ∧ A.bad v w := by
  change none ∈ (input.next v).map (input.redirect v) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨w, member, same⟩
    have flag : input.bad v w = true := by
      cases bad : input.bad v w <;> simp [redirect, bad] at same ⊢
    exact ⟨w, (input.edges v w).mp member, (input.bad_correct v w).mp flag⟩
  · rintro ⟨w, edge, bad⟩
    exact ⟨w, (input.edges v w).mpr edge, by simp [redirect, (input.bad_correct v w).mpr bad]⟩

theorem reach_edge_node (v w : Fin n) : input.reachArena.edge (some v) (some w) ↔
    A.edge v w ∧ ¬ A.bad v w := by
  change some w ∈ (input.next v).map (input.redirect v) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨child, member, same⟩
    have flag : input.bad v child = false := by
      cases bad : input.bad v child <;> simp [redirect, bad] at same ⊢
    have equal : child = w := by simpa [redirect, flag] using same
    subst child
    exact ⟨(input.edges v w).mp member, fun bad => by
      have yes := (input.bad_correct v w).mpr bad
      simp [flag] at yes⟩
  · rintro ⟨edge, nonbad⟩
    have flag : input.bad v w = false := Bool.eq_false_iff.mpr (fun yes => nonbad ((input.bad_correct v w).mp yes))
    exact ⟨w, (input.edges v w).mpr edge, by simp [redirect, flag]⟩

theorem reach_owner (v : Fin n) : input.reachArena.owner (some v) = input.reachArena.player ↔
    A.owner v ≠ A.player := by
  change A.owner v = !A.player ↔ A.owner v ≠ A.player
  cases A.owner v <;> cases A.player <;> decide

theorem reach_goal_layer (k : Nat) : input.reachArena.escapeLayer (fun v => v = none) k none :=
  input.reachArena.escapeLayer_mono _ (Nat.zero_le k) none rfl

/-- pの全ての非違反手、qの一つの違反手または削除済み手、という双対性。 -/
theorem reach_step_iff (current : Fin n → Prop) (reached : Option (Fin n) → Prop)
    (goal : reached none) (same : ∀ v, reached (some v) ↔ ¬ current v) (v : Fin n) :
    input.reachArena.escapeStep (fun v => v = none) reached (some v) ↔ ¬ A.StayGood current v := by
  classical
  have notGoal : ¬ (some v : Option (Fin n)) = none := by simp
  simp only [escapeStep, notGoal, false_or]
  by_cases own : A.owner v = A.player
  · have reversed : input.reachArena.owner (some v) ≠ input.reachArena.player :=
      fun equal => (input.reach_owner v).mp equal own
    rw [if_neg reversed]
    constructor
    · intro all stays
      obtain ⟨w, edge, nonbad, alive⟩ := stays.1 own
      exact (same w).mp (all (some w) ((input.reach_edge_node v w).mpr ⟨edge, nonbad⟩)) alive
    · intro failed child edge
      cases child with
      | none => exact goal
      | some w =>
        obtain ⟨legal, nonbad⟩ := (input.reach_edge_node v w).mp edge
        apply (same w).mpr
        intro alive
        exact failed ⟨fun _ => ⟨w, legal, nonbad, alive⟩, fun other => False.elim (other own)⟩
  · have reversed := (input.reach_owner v).mpr own
    rw [if_pos reversed]
    constructor
    · rintro ⟨child, edge, inside⟩ stays
      cases child with
      | none =>
        obtain ⟨w, legal, bad⟩ := (input.reach_edge_goal v).mp edge
        exact (stays.2 own w legal).1 bad
      | some w =>
        have legal := ((input.reach_edge_node v w).mp edge).1
        exact (same w).mp inside (stays.2 own w legal).2
    · intro failed
      apply Classical.byContradiction
      intro noChild
      apply failed
      refine ⟨fun impossible => False.elim (own impossible), ?_⟩
      intro _ w edge
      have nonbad : ¬ A.bad v w := by
        intro bad
        exact noChild ⟨none, (input.reach_edge_goal v).mpr ⟨w, edge, bad⟩, goal⟩
      refine ⟨nonbad, ?_⟩
      apply Classical.byContradiction
      intro absent
      exact noChild ⟨some w, (input.reach_edge_node v w).mpr ⟨edge, nonbad⟩, (same w).mpr absent⟩

/-- 第k到達層と第k同期削除の補集合が、ずれなく一致する。 -/
theorem reach_layer_iff (k : Nat) (v : Fin n) :
    input.reachArena.escapeLayer (fun v => v = none) k (some v) ↔ ¬ A.goodIter k v := by
  induction k generalizing v with
  | zero => simp [escapeLayer, goodIter]
  | succ k ih =>
    change input.reachArena.escapeStep _ (input.reachArena.escapeLayer _ k) (some v) ↔ _
    rw [input.reach_step_iff (A.goodIter k) _ (input.reach_goal_layer k) ih v, goodIter_step_iff]

def reachVertices : List (Option (Fin n)) := none :: (List.finRange n).map some

theorem reachVertices_cover (v : Option (Fin n)) : v ∈ reachVertices (n := n) := by
  cases v with
  | none => simp [reachVertices]
  | some v => simp [reachVertices, List.finRange, List.mem_ofFn]

theorem reachVertices_length : (reachVertices (n := n)).length = n + 1 := by
  simp [reachVertices]

theorem reachNext_length (v : Fin n) : (input.reachNext (some v)).length = (input.next v).length := by
  simp [reachNext]

/-- 入力の辺を増殖させず、追加するのは目標の自己辺一本だけである。 -/
theorem reach_edges_count :
    ((reachVertices (n := n)).map (fun v => (input.reachNext v).length)).sum =
      1 + ((List.finRange n).map (fun v => (input.next v).length)).sum := by
  simp [reachVertices, reachNext, List.map_map, Function.comp_def, Nat.add_comm]

end DeletionInput
end PetaProof.HistoryArena
