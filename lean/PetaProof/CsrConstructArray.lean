import PetaProof.CsrPrefixArray

/-!
配列カウント→インプレース累積和→末尾値での確保→cursor格納、というCSR構築全体。
以前のofFnによるoffset仕様を入力せず、構築済み配列との一致を導く。
-/
namespace PetaProof.CsrConstructArray

universe u
variable {E : Type u}

structure Built (E : Type u) where
  positions : Array Nat
  state : CsrPayloadArray.State E

/-- 確保数は入力辺数を直接使わず、計算した末尾offsetから読む。 -/
def seedState (n : Nat) (seed : E) (positions : Array Nat) : CsrPayloadArray.State E :=
  ⟨positions, Array.replicate (positions[n]?.getD 0) seed⟩

def build (n : Nat) (seed : E) (target : E → Nat) (edges : List E) : Built E :=
  let positions := CsrPrefixArray.built n target edges
  ⟨positions, CsrPayloadArray.fill target edges (seedState n seed positions)⟩

theorem allocation_read_safe (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) : n < (CsrPrefixArray.built n target edges).size := by
  rw [(CsrPrefixArray.built_invariant n target edges bounded).size]
  omega

theorem capacity_exact (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    (CsrPrefixArray.built n target edges)[n]?.getD 0 = edges.length := by
  rw [CsrPrefixArray.built_eq_offsets n target edges bounded,
    CsrArray.offsets_get n _ n (Nat.le_refl n)]
  exact Csr.total_capacity target edges n bounded

theorem seedState_exact (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    seedState n seed (CsrPrefixArray.built n target edges) =
      CsrPayloadArray.initial n edges.length (Csr.degrees target edges) seed := by
  unfold seedState
  rw [capacity_exact n target edges bounded, CsrPrefixArray.built_eq_offsets n target edges bounded]
  rfl

theorem build_exact (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) :
    build n seed target edges =
      ⟨CsrArray.offsets n (Csr.degrees target edges), CsrPayloadArray.built n seed target edges⟩ := by
  unfold build
  dsimp only
  rw [seedState_exact n seed target edges bounded, CsrPrefixArray.built_eq_offsets n target edges bounded]
  rfl

/-- 構築の三ループと末尾offsetの読出しに、それぞれ境界条件を付ける。 -/
structure Safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E) : Prop where
  count : CsrCountArray.AllSafe target edges (Array.replicate (n + 1) 0)
  prefix_safe : CsrPrefixArray.AllSafe n 1 (CsrCountArray.built n target edges)
  allocation : n < (CsrPrefixArray.built n target edges).size
  fill : CsrPayloadArray.AllSafe target edges (seedState n seed (CsrPrefixArray.built n target edges))

theorem build_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) : Safe n seed target edges := by
  refine ⟨CsrCountArray.built_safe n target edges bounded, CsrPrefixArray.built_safe n target edges bounded,
    allocation_read_safe n target edges bounded, ?_⟩
  rw [seedState_exact n seed target edges bounded]
  exact CsrPayloadArray.built_safe n seed target edges bounded

def row (n : Nat) (seed : E) (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  let book := build n seed target edges
  let start := book.positions[vertex]?.getD 0
  let stop := book.positions[vertex + 1]?.getD 0
  CsrPayloadArray.read seed book.state start (stop - start)

theorem row_eq_reference (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) :
    row n seed target edges vertex = CsrPayloadArray.row n seed target edges vertex := by
  simp only [row, build_exact n seed target edges bounded, CsrPayloadArray.row]

theorem row_accesses_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    let book := build n seed target edges
    vertex < book.positions.size ∧ vertex + 1 < book.positions.size ∧
      book.positions[vertex]?.getD 0 ≤ book.positions[vertex + 1]?.getD 0 ∧
      book.positions[vertex + 1]?.getD 0 ≤ book.state.memory.size := by
  rw [build_exact n seed target edges bounded]
  exact CsrPayloadArray.row_accesses_safe n seed target edges bounded vertex inside

/-- 三つの配列ループで構築した区間が、元の安定バケットと一致する。 -/
theorem row_exact (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (vertex : Nat) (inside : vertex < n) :
    row n seed target edges vertex = Csr.bucket target edges vertex := by
  rw [row_eq_reference n seed target edges bounded vertex]
  exact CsrPayloadArray.row_exact n seed target edges bounded vertex inside

end PetaProof.CsrConstructArray
