import PetaProof.CsrFill64

/-!
UInt64のoffset/cursorによるCSR構築。添字はtoNatでLean Arrayへ渡す。
格納型は任意で、UInt32対にも適用できる。64-bit size_t以外の環境や確保失敗は未接続。
-/
namespace PetaProof.Csr64

universe u
variable {E : Type u}

structure Built (E : Type u) where
  positions : Array UInt64
  state : State E

def unpackBuilt (book : Built E) : CsrConstructArray.Built E :=
  ⟨unpackArray book.positions, unpackState book.state⟩

def seedState (n : Nat) (seed : E) (positions : Array UInt64) : State E :=
  ⟨positions, Array.replicate (positions[n]?.getD 0).toNat seed⟩

theorem seedState_refines (n : Nat) (seed : E) (positions : Array UInt64) :
    unpackState (seedState n seed positions) = CsrConstructArray.seedState n seed (unpackArray positions) := by
  simp only [seedState, unpackState, CsrConstructArray.seedState, get_toNat]

def build (n : Nat) (seed : E) (target : E → Nat) (edges : List E) : Built E :=
  let positions := prefixBuilt n target edges
  ⟨positions, fill target edges (seedState n seed positions)⟩

theorem capacity_exact (n : Nat) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) :
    ((prefixBuilt n target edges)[n]?.getD 0).toNat = edges.length := by
  rw [← get_toNat, prefixBuilt_refines n target edges bounded fits]
  exact CsrConstructArray.capacity_exact n target edges bounded

theorem initial_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) :
    CsrPayloadArray.AllSafe target edges (unpackState (seedState n seed (prefixBuilt n target edges))) := by
  rw [seedState_refines, prefixBuilt_refines n target edges bounded fits]
  exact (CsrConstructArray.build_safe n seed target edges bounded).fill

/-- 容量内書込とUInt64加算の非折返しを使い、構築結果全体をNat版へ接続する。 -/
theorem build_refines (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) :
    unpackBuilt (build n seed target edges) = CsrConstructArray.build n seed target edges := by
  have seed_fits : (seedState n seed (prefixBuilt n target edges)).memory.size < UInt64.size := by
    simp only [seedState, Array.size_replicate, capacity_exact n target edges bounded fits]
    exact fits
  have filled := (fill_refines_and_safe target edges (seedState n seed (prefixBuilt n target edges))
    (initial_safe n seed target edges bounded fits) seed_fits).1
  rw [seedState_refines, prefixBuilt_refines n target edges bounded fits] at filled
  simp only [build, unpackBuilt, CsrConstructArray.build, prefixBuilt_refines n target edges bounded fits, filled]

theorem fill_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) :
    AllSafe target edges (seedState n seed (prefixBuilt n target edges)) := by
  have seed_fits : (seedState n seed (prefixBuilt n target edges)).memory.size < UInt64.size := by
    simp only [seedState, Array.size_replicate, capacity_exact n target edges bounded fits]
    exact fits
  exact (fill_refines_and_safe target edges _ (initial_safe n seed target edges bounded fits) seed_fits).2

structure Safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E) : Prop where
  count : CountSafe target edges (Array.replicate (n + 1) 0)
  prefix_safe : PrefixSafe n 1 (countBuilt n target edges)
  allocation : n < (prefixBuilt n target edges).size
  fill : AllSafe target edges (seedState n seed (prefixBuilt n target edges))

theorem build_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size) : Safe n seed target edges := by
  have count_size : (countBuilt n target edges).size = n + 1 := by
    have size := (CsrCountArray.built_represents n target edges bounded).size
    rw [← countBuilt_refines n target edges fits] at size
    simpa only [unpackArray, Array.size_map] using size
  have prefix_size : (prefixBuilt n target edges).size = n + 1 := by
    have size := (CsrPrefixArray.built_invariant n target edges bounded).size
    rw [← prefixBuilt_refines n target edges bounded fits] at size
    simpa only [unpackArray, Array.size_map] using size
  exact ⟨countRun_safe n target edges _ bounded (by simp),
    prefixRun_safe n 1 _ (by omega) (by rw [count_size]; omega), by rw [prefix_size]; omega,
    fill_safe n seed target edges bounded fits⟩

theorem row_accesses_safe (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size)
    (vertex : Nat) (inside : vertex < n) :
    let book := build n seed target edges
    vertex < book.positions.size ∧ vertex + 1 < book.positions.size ∧
      (book.positions[vertex]?.getD 0).toNat ≤ (book.positions[vertex + 1]?.getD 0).toNat ∧
      (book.positions[vertex + 1]?.getD 0).toNat ≤ book.state.memory.size := by
  have safe := CsrConstructArray.row_accesses_safe n seed target edges bounded vertex inside
  rw [← build_refines n seed target edges bounded fits] at safe
  simp only [unpackBuilt, unpackState, get_toNat] at safe
  simpa only [unpackArray, Array.size_map] using safe

/-- stop>=startの範囲条件はNat版から導き、機械整数の減算も同じ長さになる。 -/
def row (n : Nat) (seed : E) (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  let book := build n seed target edges
  let start := book.positions[vertex]?.getD 0
  let stop := book.positions[vertex + 1]?.getD 0
  CsrPayloadArray.read seed (unpackState book.state) start.toNat (stop - start).toNat

theorem row_refines (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size)
    (vertex : Nat) (inside : vertex < n) :
    row n seed target edges vertex = CsrConstructArray.row n seed target edges vertex := by
  have same := build_refines n seed target edges bounded fits
  have safe := CsrConstructArray.row_accesses_safe n seed target edges bounded vertex inside
  have ordered :
      (build n seed target edges).positions[vertex]?.getD 0 ≤
        (build n seed target edges).positions[vertex + 1]?.getD 0 := by
    rw [UInt64.le_iff_toNat_le, ← get_toNat, ← get_toNat]
    change (unpackBuilt (build n seed target edges)).positions[vertex]?.getD 0 ≤
      (unpackBuilt (build n seed target edges)).positions[vertex + 1]?.getD 0
    rw [same]
    exact safe.2.2.1
  unfold row CsrConstructArray.row
  dsimp only
  rw [UInt64.toNat_sub_of_le _ _ ordered, ← get_toNat, ← get_toNat]
  change CsrPayloadArray.read seed (unpackBuilt (build n seed target edges)).state
    ((unpackBuilt (build n seed target edges)).positions[vertex]?.getD 0)
    ((unpackBuilt (build n seed target edges)).positions[vertex + 1]?.getD 0 -
      (unpackBuilt (build n seed target edges)).positions[vertex]?.getD 0) = _
  rw [same]

theorem row_exact (n : Nat) (seed : E) (target : E → Nat) (edges : List E)
    (bounded : ∀ edge ∈ edges, target edge < n) (fits : edges.length < UInt64.size)
    (vertex : Nat) (inside : vertex < n) : row n seed target edges vertex = Csr.bucket target edges vertex := by
  rw [row_refines n seed target edges bounded fits vertex inside]
  exact CsrConstructArray.row_exact n seed target edges bounded vertex inside

end PetaProof.Csr64
