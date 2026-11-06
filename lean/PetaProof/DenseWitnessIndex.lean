import PetaProof.SparseWitnessCut

/-! 各要求で疎な閾値列を再走査せず、代表閾値を一回の降順走査で配列化する。 -/
namespace PetaProof.DenseWitnessIndex

def Candidate (cap : Nat) (marked : Nat → Bool) (level : Nat) : Prop :=
  level = cap ∨ marked level = true

def Ceiling (cap : Nat) (marked : Nat → Bool) (query result : Nat) : Prop :=
  query ≤ result ∧ result ≤ cap ∧ Candidate cap marked result ∧
    ∀ level, query ≤ level → level ≤ cap → Candidate cap marked level → result ≤ level

/-- kより大きい閾値は処理済み。currentはそこまでの最小候補を保持する。 -/
def Frontier (cap : Nat) (marked : Nat → Bool) (k current : Nat) : Prop :=
  k ≤ current ∧ current ≤ cap ∧ Candidate cap marked current ∧
    ∀ level, k < level → level ≤ cap → Candidate cap marked level → current ≤ level

def next (marked : Nat → Bool) (level current : Nat) : Nat := if marked level then level else current

theorem next_ceiling (cap : Nat) (marked : Nat → Bool) (k current : Nat)
    (frontier : Frontier cap marked (k + 1) current) :
    Ceiling cap marked (k + 1) (next marked (k + 1) current) := by
  have lower := frontier.1
  have upper := frontier.2.1
  by_cases hit : marked (k + 1) = true
  · simp only [next, hit, ↓reduceIte]
    exact ⟨Nat.le_refl _, by omega, Or.inr hit, fun _ above _ _ => above⟩
  · have no : marked (k + 1) = false := Bool.eq_false_iff.mpr hit
    simp only [next, no, Bool.false_eq_true, ↓reduceIte]
    refine ⟨frontier.1, frontier.2.1, frontier.2.2.1, ?_⟩
    intro level above bounded candidate
    by_cases same : level = k + 1
    · rcases candidate with top | marked
      · omega
      · rw [same] at marked
        exact False.elim (hit marked)
    · exact frontier.2.2.2 level (by omega) bounded candidate

theorem next_frontier (cap : Nat) (marked : Nat → Bool) (k current : Nat)
    (frontier : Frontier cap marked (k + 1) current) :
    Frontier cap marked k (next marked (k + 1) current) := by
  obtain ⟨lower, upper, candidate, least⟩ := next_ceiling cap marked k current frontier
  exact ⟨by omega, upper, candidate, fun level above bounded valid => least level (by omega) bounded valid⟩

/-- 配列長は固定し、k+1番から1番へ降順に一回ずつ書き込む。 -/
def fill (marked : Nat → Bool) : Nat → Nat → Array Nat → Array Nat
  | 0, _, table => table
  | k + 1, current, table =>
    let representative := next marked (k + 1) current
    fill marked k representative (table.setIfInBounds (k + 1) representative)

theorem fill_size (marked : Nat → Bool) (k current : Nat) (table : Array Nat) :
    (fill marked k current table).size = table.size := by
  induction k generalizing current table with
  | zero => rfl
  | succ k ih => simp only [fill, ih, Array.size_setIfInBounds]

theorem fill_above (marked : Nat → Bool) (k current : Nat) (table : Array Nat)
    (query : Nat) (above : k < query) :
    (fill marked k current table)[query]? = table[query]? := by
  induction k generalizing current table with
  | zero => rfl
  | succ k ih =>
    rw [fill, ih _ _ (by omega)]
    have different : k + 1 ≠ query := by omega
    simp [Array.getElem?_setIfInBounds, different, Ne.symm different]

theorem fill_ceiling (cap : Nat) (marked : Nat → Bool) (k current : Nat) (table : Array Nat)
    (space : k < table.size) (frontier : Frontier cap marked k current)
    (query : Nat) (positive : 0 < query) (bounded : query ≤ k) :
    ∃ result, (fill marked k current table)[query]? = some result ∧ Ceiling cap marked query result := by
  induction k generalizing current table with
  | zero => omega
  | succ k ih =>
    by_cases same : query = k + 1
    · subst query
      refine ⟨next marked (k + 1) current, ?_, next_ceiling cap marked k current frontier⟩
      rw [fill, fill_above _ k _ _ (k + 1) (by omega)]
      simp [Array.getElem?_setIfInBounds, space]
    · rw [fill]
      apply ih _ _ (by simpa only [Array.size_setIfInBounds] using (show k < table.size by omega))
        (next_frontier cap marked k current frontier) (by omega)

def build (cap : Nat) (marked : Nat → Bool) : Array Nat :=
  fill marked cap cap (Array.replicate (cap + 1) cap)

theorem build_size (cap : Nat) (marked : Nat → Bool) : (build cap marked).size = cap + 1 := by
  simp [build, fill_size]

theorem build_ceiling (cap : Nat) (marked : Nat → Bool) (query : Nat)
    (positive : 0 < query) (bounded : query ≤ cap) :
    ∃ result, (build cap marked)[query]? = some result ∧ Ceiling cap marked query result := by
  apply fill_ceiling cap marked cap cap _ (by simp) _ query positive bounded
  exact ⟨Nat.le_refl _, Nat.le_refl _, Or.inl rfl, fun _ above below _ => by omega⟩

theorem ceiling_unique (cap : Nat) (marked : Nat → Bool) (query first second : Nat)
    (left : Ceiling cap marked query first) (right : Ceiling cap marked query second) : first = second :=
  Nat.le_antisymm (left.2.2.2 second right.1 right.2.1 right.2.2.1)
    (right.2.2.2 first left.1 left.2.1 left.2.2.1)

/-- マーク参照一回、分岐一回、current決定一回、書込一回を指定イベントとして数える。 -/
def fillWork : Nat → Nat
  | 0 => 0
  | k + 1 => 4 + fillWork k

theorem fillWork_exact (k : Nat) : fillWork k = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [fillWork, ih]; omega

def buildWork (cap : Nat) : Nat := (cap + 1) + fillWork cap

theorem buildWork_exact (cap : Nat) : buildWork cap = 5 * cap + 1 := by
  simp only [buildWork, fillWork_exact]
  omega

end PetaProof.DenseWitnessIndex

namespace PetaProof.ThresholdGame.QueueContext

universe u v
variable {V : Type u} {E : Type v} {G : ThresholdGame V} (ctx : G.QueueContext E)

def witnessMarks (index : Nat) : Bool := (ctx.generatedLeafMarks[index]?).getD false

def witnessIndex : Array Nat := DenseWitnessIndex.build G.mate.toNat ctx.witnessMarks

theorem witnessIndex_size : ctx.witnessIndex.size = G.mate.toNat + 1 := DenseWitnessIndex.build_size _ _

theorem witnessCandidate_iff (index : Nat) (positive : 0 < index) (cap : index ≤ G.mate.toNat) :
    DenseWitnessIndex.Candidate G.mate.toNat ctx.witnessMarks index ↔ G.CriticalLevel (index : Int) := by
  have cast : (G.mate.toNat : Int) = G.mate := Int.toNat_of_nonneg (Int.le_of_lt G.mate_positive)
  have flags := ctx.generatedLeafFlag_spec (index : Int) (by omega) (by omega)
  have sameFlag : ctx.witnessMarks index = ctx.generatedLeafFlag (index : Int) := by
    simp [witnessMarks, generatedLeafFlag]
  constructor
  · rintro (top | hit)
    · exact ⟨by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨by omega, by omega, Or.inr (flags.mp (sameFlag ▸ hit))⟩
  · rintro ⟨_, _, top | leaf⟩
    · exact Or.inl (by omega)
    · exact Or.inr (sameFlag.symm ▸ flags.mpr leaf)

/-- 一回構築した配列の参照が、疎な列の最小代表を探す参照仕様と一致する。 -/
theorem witnessIndex_eq (query : Int) (positive : 0 < query) (cap : query ≤ G.mate) :
    ctx.witnessIndex[query.toNat]? = some (ctx.witnessLevel query).toNat := by
  have castQuery : (query.toNat : Int) = query := Int.toNat_of_nonneg (by omega)
  have castCap : (G.mate.toNat : Int) = G.mate := Int.toNat_of_nonneg (Int.le_of_lt G.mate_positive)
  obtain ⟨result, found, lower, upper, candidate, least⟩ :=
    DenseWitnessIndex.build_ceiling G.mate.toNat ctx.witnessMarks query.toNat (by omega) (by omega)
  obtain ⟨low, critical, minimal⟩ := ctx.witnessLevel_spec query positive cap
  have criticalPositive := critical.1
  have criticalCap := critical.2.1
  have castRepresentative : ((ctx.witnessLevel query).toNat : Int) = ctx.witnessLevel query :=
    Int.toNat_of_nonneg (by omega)
  have representativeCandidate := (ctx.witnessCandidate_iff (ctx.witnessLevel query).toNat
    (by omega) (by omega)).mpr (by simpa only [castRepresentative] using critical)
  have first := least (ctx.witnessLevel query).toNat (by omega) (by omega) representativeCandidate
  have resultCritical := (ctx.witnessCandidate_iff result (by omega) upper).mp candidate
  have second := minimal (result : Int) resultCritical (by omega)
  have equal : result = (ctx.witnessLevel query).toNat := by omega
  simpa only [equal] using found

end PetaProof.ThresholdGame.QueueContext
