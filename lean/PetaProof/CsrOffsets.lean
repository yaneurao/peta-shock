import PetaProof.SccIndexedView

/-!
CSRの入次数カウントと累積和。添字はNatであり、機械整数の桁あふれは別の課題。
bucketは格納内容の証明用仕様で、本番で子ごとに全辺を再走査しない。
-/
namespace PetaProof.Csr

universe u
variable {E : Type u}

def bucket (target : E → Nat) (edges : List E) (vertex : Nat) : List E :=
  edges.filter (fun edge => target edge == vertex)

def increment (counts : Nat → Nat) (vertex : Nat) : Nat → Nat :=
  fun other => if other = vertex then counts other + 1 else counts other

def countPass (target : E → Nat) : List E → (Nat → Nat) → (Nat → Nat)
  | [], counts => counts
  | edge :: rest, counts => countPass target rest (increment counts (target edge))

theorem countPass_spec (target : E → Nat) (edges : List E) (counts : Nat → Nat) (vertex : Nat) :
    countPass target edges counts vertex = counts vertex + (bucket target edges vertex).length := by
  induction edges generalizing counts with
  | nil => simp [countPass, bucket]
  | cons edge rest ih =>
    rw [countPass, ih]
    by_cases same : target edge = vertex
    · simp [increment, bucket, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp [increment, bucket, same, Ne.symm same]

def offset (counts : Nat → Nat) : Nat → Nat
  | 0 => 0
  | vertex + 1 => offset counts vertex + counts vertex

def degrees (target : E → Nat) (edges : List E) : Nat → Nat := countPass target edges (fun _ => 0)

theorem degrees_spec (target : E → Nat) (edges : List E) (vertex : Nat) :
    degrees target edges vertex = (bucket target edges vertex).length := by
  simp [degrees, countPass_spec]

theorem offset_mono (counts : Nat → Nat) (a b : Nat) (ordered : a ≤ b) :
    offset counts a ≤ offset counts b := by
  induction b with
  | zero =>
    have same : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases before : a ≤ b
    · have lower := ih before
      simp only [offset]
      omega
    · have same : a = b + 1 := by omega
      subst a
      exact Nat.le_refl _

theorem offset_gap (counts : Nat → Nat) (vertex : Nat) :
    offset counts (vertex + 1) - offset counts vertex = counts vertex := by
  simp only [offset]
  omega

/-- 異なる子の半開区間は重ならない。 -/
theorem intervals_disjoint (counts : Nat → Nat) (a b i j : Nat) (different : a ≠ b)
    (inside_a : i < counts a) (inside_b : j < counts b) :
    offset counts a + i ≠ offset counts b + j := by
  by_cases before : a < b
  · have bound := offset_mono counts (a + 1) b (by omega)
    simp only [offset] at bound
    omega
  · have bound := offset_mono counts (b + 1) a (by omega)
    simp only [offset] at bound
    omega

theorem offset_cons (target : E → Nat) (edge : E) (rest : List E) (vertex : Nat) :
    offset (degrees target (edge :: rest)) vertex =
      offset (degrees target rest) vertex + if target edge < vertex then 1 else 0 := by
  induction vertex with
  | zero => simp [offset]
  | succ vertex ih =>
    rw [offset, ih, degrees_spec]
    by_cases same : target edge = vertex
    · simp [bucket, same, offset, degrees_spec, Nat.add_assoc]
    · by_cases before : target edge < vertex
      · have next : target edge < vertex + 1 := by omega
        simp [bucket, same, before, next, offset, degrees_spec, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have next : ¬ target edge < vertex + 1 := by omega
        simp [bucket, same, before, next, offset, degrees_spec]

/-- 全ての子番号がn未満なら、末尾offsetは必要な格納要素数に等しい。 -/
theorem total_capacity (target : E → Nat) (edges : List E) (n : Nat)
    (bounded : ∀ edge ∈ edges, target edge < n) : offset (degrees target edges) n = edges.length := by
  induction edges with
  | nil =>
    have zero : degrees target [] = fun _ => 0 := rfl
    rw [zero]
    induction n with
    | zero => rfl
    | succ n ih => simpa [offset] using ih
  | cons edge rest ih =>
    have head := bounded edge (by simp)
    have tail : ∀ edge ∈ rest, target edge < n := fun edge member => bounded edge (by simp [member])
    rw [offset_cons, if_pos head, ih tail]
    rfl

end PetaProof.Csr
