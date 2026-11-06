import PetaProof.ValueStratumFilter

/-! 生の値を変えず、安全候補内の符号別depth優先を出力へ符号化する。 -/
namespace PetaProof.OutputPreference

universe u v
variable {E : Type u}

/-- 生の最善値に等しく、許可された候補内で符号別のdepthが最善である。 -/
def Preferred (raw : E → Int) (depth : E → Nat) (safe : E → Prop)
    (best : Int) (edge : E) : Prop :=
  safe edge ∧ raw edge = best ∧ ∀ other, safe other → raw other = best →
    if 0 ≤ best then depth edge ≤ depth other else depth other ≤ depth edge

/-- 正のdepthを最小化し、負のdepthを最大化する比較キー。 -/
def depthKey (best : Int) (depth : E → Nat) (edge : E) : Int :=
  if 0 ≤ best then (depth edge : Int) else -(depth edge : Int)

def pickMin (key : E → Int) (first : E) : List E → E
  | [] => first
  | edge :: rest => pickMin key (if key first ≤ key edge then first else edge) rest

theorem pickMin_spec (key : E → Int) (first : E) (rest : List E) :
    pickMin key first rest ∈ first :: rest ∧
      ∀ other ∈ first :: rest, key (pickMin key first rest) ≤ key other := by
  induction rest generalizing first with
  | nil => simp [pickMin]
  | cons edge rest ih =>
    let next := if key first ≤ key edge then first else edge
    have nextMember : next = first ∨ next = edge := by
      dsimp [next]
      split <;> simp
    have nextFirst : key next ≤ key first := by
      dsimp [next]
      split <;> omega
    have nextEdge : key next ≤ key edge := by
      dsimp [next]
      split <;> omega
    obtain ⟨member, minimal⟩ := ih next
    have before : key (pickMin key next rest) ≤ key next := minimal next (by simp)
    constructor
    · change pickMin key next rest ∈ first :: edge :: rest
      rcases List.mem_cons.mp member with same | tail
      · rw [same]
        rcases nextMember with eqFirst | eqEdge
        · simp [eqFirst]
        · simp [eqEdge]
      · simp [tail]
    · intro other present
      change key (pickMin key next rest) ≤ key other
      rcases List.mem_cons.mp present with same | tail
      · subst other; omega
      · rcases List.mem_cons.mp tail with same | tail
        · subst other; omega
        · exact minimal other (by simp [tail])

/-- 有限候補に安全な生の最善手があれば、符号別depthの優先手も必ず存在する。 -/
theorem preferred_exists (raw : E → Int) (depth : E → Nat) (safe : E → Prop)
    (best : Int) (candidates : List E)
    (covers : ∀ edge, safe edge → edge ∈ candidates)
    (present : ∃ edge ∈ candidates, safe edge ∧ raw edge = best) :
    ∃ edge ∈ candidates, Preferred raw depth safe best edge := by
  classical
  let kept := candidates.filter (fun edge => decide (safe edge ∧ raw edge = best))
  have nonempty : kept ≠ [] := by
    obtain ⟨edge, member, accepted⟩ := present
    have found : edge ∈ kept := by simp [kept, member, accepted]
    intro empty
    rw [empty] at found
    exact List.not_mem_nil found
  cases shape : kept with
  | nil => exact False.elim (nonempty shape)
  | cons first rest =>
    let selected := pickMin (depthKey best depth) first rest
    obtain ⟨member, minimal⟩ := pickMin_spec (depthKey best depth) first rest
    have inKept : selected ∈ kept := by rw [shape]; exact member
    have selectedInfo := List.mem_filter.mp inKept
    have accepted : safe selected ∧ raw selected = best := by simpa using selectedInfo.2
    refine ⟨selected, selectedInfo.1, accepted.1, accepted.2, ?_⟩
    intro other allowed same
    have otherKept : other ∈ kept := by simp [kept, covers other allowed, allowed, same]
    rw [shape] at otherKept
    have compare := minimal other otherKept
    change depthKey best depth selected ≤ depthKey best depth other at compare
    dsimp only [depthKey] at compare
    split at compare <;> split <;> omega

noncomputable def encoded (raw : E → Int) (preferred : E → Prop) (best : Int) (edge : E) : Int := by
  classical
  exact if raw edge = best ∧ ¬ preferred edge then raw edge - 1 else raw edge

/-- 好ましい手が一つ残り、生の全候補がbest以下なら、出力最大手は必ず好ましい。 -/
theorem maximum_iff (raw : E → Int) (preferred : E → Prop) (candidates : List E) (best : Int)
    (upper : ∀ edge ∈ candidates, raw edge ≤ best)
    (exact : ∀ edge ∈ candidates, preferred edge → raw edge = best)
    (existsPreferred : ∃ edge ∈ candidates, preferred edge) (edge : E) (member : edge ∈ candidates) :
    (∀ other ∈ candidates, encoded raw preferred best other ≤ encoded raw preferred best edge) ↔ preferred edge := by
  classical
  constructor
  · intro maximal
    obtain ⟨witness, present, chosen⟩ := existsPreferred
    have score := maximal witness present
    have same := exact witness present chosen
    by_cases accepted : preferred edge
    · exact accepted
    · by_cases tied : raw edge = best
      · simp [encoded, same, chosen, tied, accepted] at score
        omega
      · simp [encoded, same, chosen, tied] at score
        have limit := upper edge member
        omega
  · intro chosen other present
    have same := exact edge member chosen
    have limit := upper other present
    have chosenScore : encoded raw preferred best edge = best := by simp [encoded, same, chosen]
    rw [chosenScore]
    dsimp only [encoded]
    split <;> omega

/-- 1点幅を許すと、除外した同点手も再び選択範囲に入る。 -/
theorem rejected_tie_within_one (raw : E → Int) (preferred : E → Prop) (best : Int)
    (edge : E) (same : raw edge = best) (rejected : ¬ preferred edge) :
    best - encoded raw preferred best edge = 1 := by
  simp only [encoded, same, rejected, not_false_eq_true, and_self, if_pos]
  omega

theorem preferred_safe (raw : E → Int) (depth : E → Nat) (safe : E → Prop)
    (best : Int) (edge : E) (chosen : Preferred raw depth safe best edge) : safe edge := chosen.1

/-- depthを変えても優先手の安全性は変わらず、正負の比較方向だけが異なる。 -/
theorem preferred_direction (raw : E → Int) (depth : E → Nat) (safe : E → Prop)
    (best : Int) (edge other : E) (chosen : Preferred raw depth safe best edge)
    (allowed : safe other) (same : raw other = best) :
    (0 ≤ best → depth edge ≤ depth other) ∧ (best < 0 → depth other ≤ depth edge) := by
  have compare := chosen.2.2 other allowed same
  constructor <;> intro sign
  · simpa only [if_pos sign] using compare
  · simpa only [if_neg (show ¬ 0 ≤ best by omega)] using compare

/-- 出力最大手を選ぶ実際の履歴依存計画を、既存の候補表の下限保証へ接続する。
要求する存在証拠は、候補内の安全な生の最善手であり、depth優先手そのものではない。 -/
theorem encoded_plan_lower {V : Type v} [DecidableEq V] {G : ThresholdGame V}
    (table : G.ValueRankTable) (replies : table.AllReplies)
    (candidates : V → List E) (move : E → Move V)
    (raw : V → E → Int) (depth : E → Nat) (best : V → Int)
    (upper : ∀ vertex, G.owner vertex = G.player →
      ∀ edge, edge ∈ candidates vertex → raw vertex edge ≤ best vertex)
    (available : ∀ vertex, G.owner vertex = G.player →
      ∃ edge ∈ candidates vertex, table.admissibleMove vertex (move edge) ∧ raw vertex edge = best vertex)
    (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ candidates vertex, self.choose history vertex = move edge ∧
        ∀ other ∈ candidates vertex,
          encoded (raw vertex)
            (Preferred (raw vertex) depth
              (fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)) (best vertex)) (best vertex) other ≤
          encoded (raw vertex)
            (Preferred (raw vertex) depth
              (fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)) (best vertex)) (best vertex) edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply table.terminal_lower replies self opponent _ root payoff result
  intro history vertex own
  let safe := fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)
  obtain ⟨first, member, legal, same⟩ := available vertex own
  obtain ⟨witness, present, preferred⟩ := preferred_exists (raw vertex) depth safe (best vertex)
    (candidates vertex) (fun _ allowed => allowed.1) ⟨first, member, ⟨member, legal⟩, same⟩
  obtain ⟨edge, edgeMember, chosen, maximal⟩ := selected history vertex own
  have accepted := (maximum_iff (raw vertex) (Preferred (raw vertex) depth safe (best vertex))
    (candidates vertex) (best vertex) (upper vertex own) (fun _ _ accepted => accepted.2.1)
    ⟨witness, present, preferred⟩ edge edgeMember).mp maximal
  rw [chosen]
  exact accepted.1.2

end PetaProof.OutputPreference
