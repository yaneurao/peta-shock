import PetaProof.ThresholdSchedule

/-!
positive()のvalue[v]==0ガードを持つ初回確定値の影の配列。
関数V→Intは仕様上の配列であり、本番に全頂点走査を追加するものではない。
-/
namespace PetaProof

universe u
variable {V : Type u}

/-- 未確定0の場合だけ書く。既に記録された値は書き換えない。 -/
def latchValues (values : V → Int) (level : Int) (confirmed : V → Bool) : V → Int :=
  fun vertex => if values vertex = 0 then if confirmed vertex then level else 0 else values vertex

theorem latch_keeps_nonzero (values : V → Int) (level : Int) (confirmed : V → Bool)
    (vertex : V) (recorded : values vertex ≠ 0) : latchValues values level confirmed vertex = values vertex := by
  simp [latchValues, recorded]

theorem latch_existing (values : V → Int) (level : Int) (confirmed : V → Bool)
    (represented : ∀ vertex, confirmed vertex = true ↔ values vertex ≠ 0) :
    latchValues values level confirmed = values := by
  funext vertex
  by_cases zero : values vertex = 0
  · have flag : confirmed vertex = false := by
      cases flag : confirmed vertex with
      | false => rfl
      | true => exact False.elim ((represented vertex).mp flag zero)
    simp [latchValues, zero, flag]
  · simp [latchValues, zero]

/-- 新規に書く閾値が0以外なら、保持済みの値と新規記録は確定フラグを正確に表す。 -/
theorem latch_represents (values : V → Int) (level : Int) (confirmed : V → Bool) (nonzero : level ≠ 0)
    (retained : ∀ vertex, values vertex ≠ 0 → confirmed vertex = true) (vertex : V) :
    confirmed vertex = true ↔ latchValues values level confirmed vertex ≠ 0 := by
  by_cases zero : values vertex = 0
  · cases flag : confirmed vertex <;> simp [latchValues, zero, flag, nonzero]
  · simp [latchValues, zero, retained vertex zero]

/-- 同一閾値内で確定集合が増えるなら、記録の繰り返しは最後の集合での記録と一致する。 -/
theorem latch_compose (values : V → Int) (level : Int) (earlier later : V → Bool)
    (monotone : ∀ vertex, earlier vertex = true → later vertex = true) :
    latchValues (latchValues values level earlier) level later = latchValues values level later := by
  funext vertex
  by_cases recorded : values vertex = 0
  · cases before : earlier vertex with
    | false => simp [latchValues, recorded, before]
    | true =>
      have after := monotone vertex before
      by_cases zero : level = 0 <;> simp [latchValues, recorded, before, after, zero]
  · simp [latchValues, recorded]

variable [DecidableEq V]

/-- 本番のadmit一回が変更するのは1要素だけである。 -/
def writeAdmission (values : V → Int) (level : Int) (vertex : V) : V → Int :=
  fun other => if other = vertex then if values other = 0 then level else values other else values other

def writeAdmissions (values : V → Int) (level : Int) : List V → V → Int
  | [] => values
  | vertex :: rest => writeAdmissions (writeAdmission values level vertex) level rest

theorem writeAdmissions_get (values : V → Int) (level : Int) (vertices : List V) (other : V) :
    writeAdmissions values level vertices other =
      if values other = 0 ∧ other ∈ vertices then level else values other := by
  induction vertices generalizing values with
  | nil => simp [writeAdmissions]
  | cons vertex rest ih =>
    rw [writeAdmissions, ih]
    by_cases same : other = vertex
    · subst other
      by_cases recorded : values vertex = 0
      · by_cases zero : level = 0 <;> simp [writeAdmission, recorded, zero]
      · simp [writeAdmission, recorded]
    · simp [writeAdmission, same]

/-- 初期の確定済み局面か、今回投入した局面が最終集合なら、単一書込み列と一括記録は同じ。 -/
theorem writeAdmissions_eq_latch (values : V → Int) (level : Int) (vertices : List V)
    (confirmed : V → Bool)
    (represented : ∀ vertex, confirmed vertex = true ↔ values vertex ≠ 0 ∨ vertex ∈ vertices) :
    writeAdmissions values level vertices = latchValues values level confirmed := by
  funext vertex
  rw [writeAdmissions_get]
  by_cases zero : values vertex = 0
  · have represented_here : confirmed vertex = true ↔ vertex ∈ vertices := by
      simpa only [zero, ne_eq, not_true_eq_false, false_or] using represented vertex
    cases flag : confirmed vertex with
    | false =>
      have absent : vertex ∉ vertices := by
        intro member
        have impossible := represented_here.mpr member
        rw [flag] at impossible
        cases impossible
      simp [latchValues, zero, flag, absent]
    | true => simp [latchValues, zero, flag, represented_here.mp flag]
  · simp [latchValues, zero]

omit [DecidableEq V] in
/-- 各閾値の終端で、未確定だった局面だけにその閾値を記録する前向き走査。 -/
def scanValues (levels : List Int) (confirmed : Int → V → Bool) (values : V → Int) : V → Int :=
  match levels with
  | [] => values
  | level :: rest => scanValues rest confirmed (latchValues values level (confirmed level))

omit [DecidableEq V] in
/-- 正閾値なら、一度0以外を記録した後は後続の低い閾値で上書きされない。 -/
theorem scanValues_get (levels : List Int) (confirmed : Int → V → Bool) (values : V → Int)
    (positive : ∀ level ∈ levels, 0 < level) (vertex : V) :
    scanValues levels confirmed values vertex =
      if values vertex = 0 then firstWinning (fun level => confirmed level vertex) levels else values vertex := by
  induction levels generalizing values with
  | nil => by_cases zero : values vertex = 0 <;> simp [scanValues, firstWinning, zero]
  | cons level rest ih =>
    have level_positive := positive level (by simp)
    have tail_positive : ∀ next ∈ rest, 0 < next := fun next member => positive next (by simp [member])
    rw [scanValues, ih _ tail_positive]
    by_cases recorded : values vertex = 0
    · cases flag : confirmed level vertex with
      | false => simp [latchValues, recorded, flag, firstWinning]
      | true =>
        have nonzero : level ≠ 0 := by omega
        simp [latchValues, recorded, flag, firstWinning, nonzero]
    · simp [latchValues, recorded]

omit [DecidableEq V] in
theorem scanValues_initial (levels : List Int) (confirmed : Int → V → Bool)
    (positive : ∀ level ∈ levels, 0 < level) (vertex : V) :
    scanValues levels confirmed (fun _ => 0) vertex = firstWinning (fun level => confirmed level vertex) levels := by
  simpa using scanValues_get levels confirmed (fun _ => 0) positive vertex

end PetaProof
