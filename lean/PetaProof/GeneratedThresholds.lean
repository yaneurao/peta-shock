import PetaProof.PositiveLeafMarks

/-! 実際の有限辺から閾値列を生成する。合法手全体の存在判定を計算の入力にしない。 -/
namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V}
variable (ctx : QueueContext G E)

def leafScore (edge : E) : Option Int := match ctx.indexed.move edge with
  | .node _ => none
  | .leaf score => some score

def generatedLeafMarks : Array Bool :=
  PositiveLeafMarks.flags ctx.leafScore G.mate.toNat ctx.allEdges

def generatedLeafFlag (level : Int) : Bool := (ctx.generatedLeafMarks[level.toNat]?).getD false

theorem generatedLeafMarks_size : ctx.generatedLeafMarks.size = G.mate.toNat + 1 := PositiveLeafMarks.flags_size _ _ _

theorem generatedLeafFlag_spec (level : Int) (positive : 0 < level) (bounded : level ≤ G.mate) :
    ctx.generatedLeafFlag level = true ↔ ∃ vertex, G.legal vertex (.leaf level) := by
  have indexBound : level.toNat ≤ G.mate.toNat := by omega
  have flags := PositiveLeafMarks.flags_get ctx.leafScore G.mate.toNat ctx.allEdges level.toNat indexBound
  change ctx.generatedLeafMarks[level.toNat]? = some true ↔ _ at flags
  have lookup : ctx.generatedLeafFlag level = true ↔ ctx.generatedLeafMarks[level.toNat]? = some true := by
    unfold generatedLeafFlag
    cases found : ctx.generatedLeafMarks[level.toNat]? <;> simp [Option.getD]
  rw [lookup, flags]
  constructor
  · rintro ⟨edge, _, score, found, scorePositive, sameIndex⟩
    have scoreNonnegative : 0 ≤ score := by omega
    have levelNonnegative : 0 ≤ level := by omega
    have castSame := congrArg (fun index : Nat => (index : Int)) sameIndex
    simp only [Int.toNat_of_nonneg scoreNonnegative, Int.toNat_of_nonneg levelNonnegative] at castSame
    subst score
    have move : ctx.indexed.move edge = .leaf level := by
      cases actual : ctx.indexed.move edge <;> simp_all [leafScore]
    exact ⟨ctx.indexed.source edge, move ▸ ctx.indexed.legal _ edge (ctx.indexed.at_source edge)⟩
  · rintro ⟨vertex, legal⟩
    obtain ⟨edge, _, move⟩ := ctx.indexed.covers vertex (.leaf level) legal
    exact ⟨edge, ctx.allEdges_contains edge, level, by simp [leafScore, move], positive, rfl⟩

/-- 上限は必ず残し、それ以外はフラグのある正の値だけを降順に一回読む。 -/
def generatedLevels : List Int :=
  let marks := ctx.generatedLeafMarks
  processedLevels G.mate.toNat (fun level => (marks[level.toNat]?).getD false)

theorem generatedLevels_critical_iff (level : Int) : level ∈ ctx.generatedLevels ↔ G.CriticalLevel level :=
  G.processedLevels_critical_iff ctx.generatedLeafFlag (ctx.generatedLeafFlag_spec) level

theorem generatedLevels_ordered : ctx.generatedLevels.Pairwise (fun a b => b < a) := processedLevels_ordered _ _

theorem generatedLevels_valid : ∀ level ∈ ctx.generatedLevels, 0 < level ∧ level ≤ G.mate := by
  intro level member
  have critical := (ctx.generatedLevels_critical_iff level).mp member
  exact ⟨critical.1, critical.2.1⟩

theorem generatedLevels_eq : ctx.generatedLevels = G.setLevels := by
  unfold generatedLevels ThresholdGame.setLevels processedLevels
  apply List.filter_congr
  intro level member
  have range := (mem_descendingLevels G.mate.toNat level).mp member
  have bounded : level ≤ G.mate := by
    have cast := Int.toNat_of_nonneg (Int.le_of_lt G.mate_positive)
    omega
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq]
  change (level = (G.mate.toNat : Int) ∨ ctx.generatedLeafFlag level = true) ↔
    (level = (G.mate.toNat : Int) ∨ G.positiveLeafFlags level = true)
  rw [ctx.generatedLeafFlag_spec level range.1 bounded]
  simp [ThresholdGame.positiveLeafFlags]

theorem descendingLevels_length (cap : Nat) : (descendingLevels cap).length = cap := by
  induction cap with
  | zero => rfl
  | succ cap ih => simp only [descendingLevels, List.length_cons, ih]

/-- フラグ初期化、一回の辺走査、整数列生成、各値の最大五操作、採用値の出力。 -/
def scheduleGenerationWork : Nat :=
  (G.mate.toNat + 1) +
    PositiveLeafMarks.scanWork ctx.leafScore ctx.allEdges (Array.replicate (G.mate.toNat + 1) false) +
    (descendingLevels G.mate.toNat).length + 5 * (descendingLevels G.mate.toNat).length +
    ctx.generatedLevels.length

variable [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
theorem generatedLevels_length_bound : ctx.generatedLevels.length ≤ G.mate.toNat :=
  G.level_count_bound ctx.generatedLevels ctx.generatedLevels_valid ctx.generatedLevels_ordered

omit [DecidableEq V] [DecidableEq E] in
theorem scheduleGenerationWork_bound : ctx.scheduleGenerationWork ≤ 4 * ctx.allEdges.length + 8 * (G.mate.toNat + 1) := by
  have edges := PositiveLeafMarks.scanWork_bound ctx.leafScore ctx.allEdges (Array.replicate (G.mate.toNat + 1) false)
  have levels := ctx.generatedLevels_length_bound
  simp only [scheduleGenerationWork, descendingLevels_length]
  omega

/-- 閾値列・整数leaf表・pop時記録まで、有限入力から実行する片側の手続き。 -/
def generatedPositiveValues : V → Int :=
  ctx.positiveStreamingValues ctx.generatedLevels ctx.generatedLevels_valid

theorem generatedPositiveValues_eq : ctx.generatedPositiveValues = ctx.computedPositiveStreamingValues := by
  unfold generatedPositiveValues computedPositiveStreamingValues
  let first : { levels : List Int // ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate } :=
    ⟨ctx.generatedLevels, ctx.generatedLevels_valid⟩
  let second : { levels : List Int // ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate } :=
    ⟨G.setLevels, fun t member => ⟨((G.setLevels_critical_iff t).mp member).1, ((G.setLevels_critical_iff t).mp member).2.1⟩⟩
  have same : first = second := Subtype.ext ctx.generatedLevels_eq
  exact congrArg (fun item : { levels : List Int // ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate } =>
    ctx.positiveStreamingValues item.val item.property) same

def generatedValue (otherCore : V → Bool) : V → Int :=
  let own := ctx.generatedPositiveValues
  let other := (ctx.opposite otherCore).generatedPositiveValues
  fun vertex => own vertex - other vertex

theorem generatedValue_eq (otherCore : V → Bool) : ctx.generatedValue otherCore = ctx.computedStreamingValue otherCore := by
  unfold generatedValue computedStreamingValue
  rw [ctx.generatedPositiveValues_eq, (ctx.opposite otherCore).generatedPositiveValues_eq]

def generatedValueRows (otherCore : V → Bool) : List (V × Int) :=
  assembleValueRows ctx.vertices ctx.generatedPositiveValues (ctx.opposite otherCore).generatedPositiveValues

theorem generatedValueRows_eq (otherCore : V → Bool) : ctx.generatedValueRows otherCore = ctx.computedValueRows otherCore := by
  unfold generatedValueRows computedValueRows
  rw [ctx.generatedPositiveValues_eq, (ctx.opposite otherCore).generatedPositiveValues_eq]

theorem generatedValue_exact (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) (root : V) :
    G.ExactValue root (ctx.generatedValue otherCore root) := by
  rw [ctx.generatedValue_eq]
  exact ctx.computedStreamingValue_exact otherCore leaves own_covers other_covers root

/-- 両側の閾値生成も含めた主処理会計。グラフ/逆辺/core構築は依然入力側である。 -/
def generatedWork (otherCore : V → Bool) : Nat :=
  ctx.scheduleGenerationWork + (ctx.opposite otherCore).scheduleGenerationWork +
    ctx.valueWork otherCore ctx.generatedLevels ctx.generatedLevels_valid
      (ctx.opposite otherCore).generatedLevels (ctx.opposite otherCore).generatedLevels_valid

theorem generatedWork_bound (otherCore : V → Bool) :
    ctx.generatedWork otherCore ≤ 15 * ctx.vertices.length + 26 * ctx.allEdges.length +
      42 * (G.mate.toNat + 1) + ctx.localTerm ctx.generatedLevels +
      (ctx.opposite otherCore).localTerm (ctx.opposite otherCore).generatedLevels := by
  have own := ctx.scheduleGenerationWork_bound
  have other := (ctx.opposite otherCore).scheduleGenerationWork_bound
  change (ctx.opposite otherCore).scheduleGenerationWork ≤ 4 * ctx.allEdges.length + 8 * (G.mate.toNat + 1) at other
  have main := ctx.valueWork_bound otherCore ctx.generatedLevels ctx.generatedLevels_valid ctx.generatedLevels_ordered
    (ctx.opposite otherCore).generatedLevels (ctx.opposite otherCore).generatedLevels_valid (ctx.opposite otherCore).generatedLevels_ordered
  unfold generatedWork
  omega

theorem generatedRows_and_work (otherCore : V → Bool) (leaves : G.BoundedLeaves)
    (own_covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (other_covers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true) :
    (∀ row ∈ ctx.generatedValueRows otherCore, G.ExactValue row.1 row.2) ∧
      ctx.generatedWork otherCore ≤ 15 * ctx.vertices.length + 26 * ctx.allEdges.length +
        42 * (G.mate.toNat + 1) + ctx.localTerm ctx.generatedLevels +
        (ctx.opposite otherCore).localTerm (ctx.opposite otherCore).generatedLevels := by
  refine ⟨?_, ctx.generatedWork_bound otherCore⟩
  rw [ctx.generatedValueRows_eq]
  exact ctx.computedValueRows_exact otherCore leaves own_covers other_covers

end PetaProof.ThresholdGame.QueueContext
