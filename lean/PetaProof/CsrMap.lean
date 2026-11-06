import PetaProof.CsrConstructArray

/-!
格納値の表現変換とCSR構築の可換性。
子番号が保存されれば、カウント・累積和・cursorは変わらず、格納値だけが写る。
写像の単射性は不要。番地とcursorは引き続きNatである。
-/
namespace PetaProof.CsrMap

universe u v
variable {E : Type u} {F : Type v}

def mapState (f : E → F) (state : CsrPayloadArray.State E) : CsrPayloadArray.State F :=
  ⟨state.cursor, state.memory.map f⟩

theorem put_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edge : E) (state : CsrPayloadArray.State E) :
    mapState f (CsrPayloadArray.put source edge state) =
      CsrPayloadArray.put target (f edge) (mapState f state) := by
  simp [mapState, CsrPayloadArray.put, preserves]

theorem fill_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (state : CsrPayloadArray.State E) :
    mapState f (CsrPayloadArray.fill source edges state) =
      CsrPayloadArray.fill target (edges.map f) (mapState f state) := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    simp only [CsrPayloadArray.fill, List.map_cons]
    rw [ih, put_map f source target preserves]

theorem count_run_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (array : Array Nat) :
    CsrCountArray.run target (edges.map f) array = CsrCountArray.run source edges array := by
  induction edges generalizing array with
  | nil => rfl
  | cons edge rest ih =>
    simp only [List.map_cons, CsrCountArray.run, ih, CsrCountArray.step, preserves]

theorem count_built_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (n : Nat) :
    CsrCountArray.built n target (edges.map f) = CsrCountArray.built n source edges :=
  count_run_map f source target preserves edges _

theorem prefix_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (n : Nat) :
    CsrPrefixArray.built n target (edges.map f) = CsrPrefixArray.built n source edges := by
  unfold CsrPrefixArray.built
  rw [count_built_map f source target preserves]

def mapBuilt (f : E → F) (book : CsrConstructArray.Built E) : CsrConstructArray.Built F :=
  ⟨book.positions, mapState f book.state⟩

theorem seed_map (f : E → F) (n : Nat) (seed : E) (positions : Array Nat) :
    mapState f (CsrConstructArray.seedState n seed positions) =
      CsrConstructArray.seedState n (f seed) positions := by
  simp [mapState, CsrConstructArray.seedState]

/-- カウント・prefix・末尾値からの確保を含む構築全体の等式。範囲条件で結果を仮定しない。 -/
theorem build_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (n : Nat) (seed : E) :
    mapBuilt f (CsrConstructArray.build n seed source edges) =
      CsrConstructArray.build n (f seed) target (edges.map f) := by
  simp only [CsrConstructArray.build, mapBuilt, prefix_map f source target preserves,
    fill_map f source target preserves, seed_map]

theorem read_map (f : E → F) (seed : E) (state : CsrPayloadArray.State E) (start count : Nat) :
    CsrPayloadArray.read (f seed) (mapState f state) start count =
      (CsrPayloadArray.read seed state start count).map f := by
  simp only [CsrPayloadArray.read, List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [mapState, Array.getElem?_map, Function.comp_apply]
  cases found : state.memory[start + index]? <;> rfl

theorem row_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (n : Nat) (seed : E) (vertex : Nat) :
    CsrConstructArray.row n (f seed) target (edges.map f) vertex =
      (CsrConstructArray.row n seed source edges vertex).map f := by
  have built := build_map f source target preserves edges n seed
  unfold CsrConstructArray.row
  rw [← built]
  exact read_map f seed _ _ _

theorem bucket_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (vertex : Nat) :
    Csr.bucket target (edges.map f) vertex = (Csr.bucket source edges vertex).map f := by
  simp [Csr.bucket, List.filter_map, Function.comp_def, preserves]

theorem stepSafe_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edge : E) (state : CsrPayloadArray.State E) :
    CsrPayloadArray.StepSafe target (f edge) (mapState f state) ↔ CsrPayloadArray.StepSafe source edge state := by
  simp [CsrPayloadArray.StepSafe, mapState, preserves]

theorem allSafe_map (f : E → F) (source : E → Nat) (target : F → Nat)
    (preserves : ∀ edge, target (f edge) = source edge) (edges : List E) (state : CsrPayloadArray.State E) :
    CsrPayloadArray.AllSafe target (edges.map f) (mapState f state) ↔ CsrPayloadArray.AllSafe source edges state := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
    simp only [List.map_cons, CsrPayloadArray.AllSafe, stepSafe_map f source target preserves]
    rw [← put_map f source target preserves, ih]

end PetaProof.CsrMap
