import PetaProof.OutputPreference

/-! 選択手を必ず残し、許可された同評価値・同depth手だけを残す保存規則。
depthの最小化そのものと、最後に保存最大値へ残す候補を区別する。 -/
namespace PetaProof.DepthWriter

universe u v

structure Input (V : Type u) (E : Type v) where
  rows : V → List E
  raw : V → E → Int
  best : V → Int
  depth : E → Nat
  selected : V → E
  keepTies : V → Bool
  selected_member : ∀ vertex, selected vertex ∈ rows vertex
  selected_exact : ∀ vertex, raw vertex (selected vertex) = best vertex
  upper : ∀ vertex edge, edge ∈ rows vertex → raw vertex edge ≤ best vertex

namespace Input
variable {V : Type u} {E : Type v} (I : Input V E)

/-- C++の選択手、または同depth候補を残すフラグで許可された手。 -/
def allowed (vertex : V) (edge : E) : Prop :=
  I.raw vertex edge = I.best vertex ∧
    (edge = I.selected vertex ∨
      I.keepTies vertex = true ∧ I.depth edge = I.depth (I.selected vertex))

theorem selected_allowed (vertex : V) : I.allowed vertex (I.selected vertex) :=
  ⟨I.selected_exact vertex, Or.inl rfl⟩

/-- 最終検査のpermits_tieと保存側の条件を対応させる。
親の再構築depthと選択手のdepthが一致する、という接続条件を明示する。 -/
theorem allowed_iff_checked [DecidableEq E] (vertex : V) (edge : E) (parentDepth : Nat)
    (selectedDepth : I.depth (I.selected vertex) = parentDepth) :
    I.allowed vertex edge ↔
      if I.keepTies vertex = true then
        I.raw vertex edge = I.best vertex ∧ I.depth edge = parentDepth
      else edge = I.selected vertex := by
  cases flag : I.keepTies vertex
  · simp only [flag, Bool.false_eq_true, if_false, allowed, false_and, or_false]
    constructor
    · exact fun h => h.2
    · intro same
      subst edge
      exact ⟨I.selected_exact vertex, rfl⟩
  · simp only [flag, if_true, allowed, true_and]
    constructor
    · rintro ⟨same, chosen | tie⟩
      · exact ⟨same, chosen ▸ selectedDepth⟩
      · exact ⟨same, tie.trans selectedDepth⟩
    · rintro ⟨same, depth⟩
      exact ⟨same, Or.inr (depth.trans selectedDepth.symm)⟩

/-- 保存用コピーだけを1下げる。内部の値とdepth表は変更しない。 -/
noncomputable def saved (vertex : V) (edge : E) : Int :=
  OutputPreference.encoded (I.raw vertex) (I.allowed vertex) (I.best vertex) edge

/-- make_output_movesの条件分岐を、そのまま書いた式との一致。 -/
theorem saved_formula [DecidableEq E] (vertex : V) (edge : E) :
    I.saved vertex edge =
      if edge ≠ I.selected vertex ∧ I.raw vertex edge = I.best vertex ∧
        (I.keepTies vertex = false ∨ I.depth edge ≠ I.depth (I.selected vertex))
      then I.raw vertex edge - 1 else I.raw vertex edge := by
  classical
  by_cases tied : I.raw vertex edge = I.best vertex <;>
    by_cases chosen : edge = I.selected vertex <;>
    by_cases equalDepth : I.depth edge = I.depth (I.selected vertex) <;>
    cases flag : I.keepTies vertex <;>
    simp [saved, OutputPreference.encoded, allowed, tied, chosen, equalDepth, flag]

/-- 保存最大手と最終検査に渡す許可集合が一致する。大域的depth最小性は不要。 -/
theorem maximum_iff (vertex : V) (edge : E) (member : edge ∈ I.rows vertex) :
    (∀ other ∈ I.rows vertex, I.saved vertex other ≤ I.saved vertex edge) ↔
      I.allowed vertex edge := by
  exact OutputPreference.maximum_iff (I.raw vertex) (I.allowed vertex) (I.rows vertex)
    (I.best vertex) (I.upper vertex) (fun _ _ h => h.1)
    ⟨I.selected vertex, I.selected_member vertex, I.selected_allowed vertex⟩ edge member

/-- 入力値域が±32000なら1点補正後も符号付き16bitの範囲内に収まる。 -/
theorem saved_bounds [DecidableEq E] (vertex : V) (edge : E)
    (bounded : -32000 ≤ I.raw vertex edge ∧ I.raw vertex edge ≤ 32000) :
    -32001 ≤ I.saved vertex edge ∧ I.saved vertex edge ≤ 32000 := by
  rw [I.saved_formula]
  split <;> omega

/-- 同depth候補を残さない場合は、保存最大手が選択手だけになる。 -/
theorem single_maximum (vertex : V) (off : I.keepTies vertex = false)
    (edge : E) (member : edge ∈ I.rows vertex) :
    (∀ other ∈ I.rows vertex, I.saved vertex other ≤ I.saved vertex edge) ↔
      edge = I.selected vertex := by
  rw [I.maximum_iff vertex edge member]
  constructor
  · intro h
    rcases h.2 with chosen | tie
    · exact chosen
    · simp [off] at tie
  · intro chosen
    subst edge
    exact I.selected_allowed vertex

/-- shrinkで生の最善手以外を削除しても、許可された最大手は消えない。 -/
noncomputable def outputRows (shrink : Bool) (vertex : V) : List E := by
  classical
  exact (I.rows vertex).filter (fun edge => decide (shrink = false ∨ I.raw vertex edge = I.best vertex))

theorem output_member (shrink : Bool) (vertex : V) (edge : E) :
    edge ∈ I.outputRows shrink vertex ↔
      edge ∈ I.rows vertex ∧ (shrink = false ∨ I.raw vertex edge = I.best vertex) := by
  classical
  simp [outputRows]

theorem output_maximum_iff (shrink : Bool) (vertex : V) (edge : E)
    (member : edge ∈ I.outputRows shrink vertex) :
    (∀ other ∈ I.outputRows shrink vertex, I.saved vertex other ≤ I.saved vertex edge) ↔
      I.allowed vertex edge := by
  apply OutputPreference.maximum_iff (I.raw vertex) (I.allowed vertex)
    (I.outputRows shrink vertex) (I.best vertex)
    (fun other present => I.upper vertex other ((I.output_member shrink vertex other).mp present).1)
    (fun _ _ h => h.1) _ edge member
  exact ⟨I.selected vertex, (I.output_member shrink vertex _).mpr
    ⟨I.selected_member vertex, Or.inr (I.selected_exact vertex)⟩, I.selected_allowed vertex⟩

end Input
end PetaProof.DepthWriter
