import PetaProof.ThresholdKeySweep

/-! 有限の整数評価値域に対する、キー配列の構築・範囲内読出し。 -/
namespace PetaProof.ThresholdKeys

def scoreRange (hi : Int) : Nat → List Int
  | 0 => []
  | count + 1 => hi :: scoreRange (hi - 1) count

theorem scoreRange_length (hi : Int) (count : Nat) : (scoreRange hi count).length = count := by
  induction count generalizing hi with
  | zero => rfl
  | succ count ih => simp only [scoreRange, List.length_cons, ih]

theorem scoreRange_le (hi : Int) (count : Nat) (score : Int) (member : score ∈ scoreRange hi count) : score ≤ hi := by
  induction count generalizing hi with
  | zero => cases member
  | succ count ih =>
    rcases List.mem_cons.mp member with same | later
    · omega
    · have bound := ih (hi - 1) later
      omega

theorem scoreRange_descending (hi : Int) (count : Nat) :
    (scoreRange hi count).Pairwise (fun a b => b ≤ a) := by
  induction count generalizing hi with
  | zero => exact List.Pairwise.nil
  | succ count ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih (hi - 1)⟩
    intro score member
    have bound := scoreRange_le (hi - 1) count score member
    omega

theorem scoreRange_at (hi : Int) (count index : Nat) (valid : index < count) :
    (scoreRange hi count)[index]'(by rw [scoreRange_length]; exact valid) = hi - Int.ofNat index := by
  induction count generalizing hi index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp [scoreRange]
    | succ index =>
      have bound : index < count := by omega
      have result := ih (hi - 1) index bound
      simp only [scoreRange, List.getElem_cons_succ]
      rw [result]
      simp only [Int.ofNat_eq_coe, Int.natCast_add, Int.natCast_one]
      omega

/-- 降順mergeの出力順をそのまま配列の添字順にする。index=hi-score。 -/
def dense (levels : List Int) (hi : Int) (count : Nat) : Array (Option Nat) :=
  ((sweep 0 levels (scoreRange hi count)).map Prod.snd).toArray

theorem dense_eq (levels : List Int) (hi : Int) (count : Nat) :
    dense levels hi count = ((scoreRange hi count).map (find levels)).toArray := by
  simp only [dense, sweep_correct 0 levels _ (scoreRange_descending hi count), List.map_map]
  congr 1
  apply List.map_congr_left
  intro score _
  simp [atOffset]

theorem dense_size (levels : List Int) (hi : Int) (count : Nat) : (dense levels hi count).size = count := by
  simp only [dense_eq, List.size_toArray, List.length_map, scoreRange_length]

theorem dense_at (levels : List Int) (hi : Int) (count index : Nat) (valid : index < count) :
    (dense levels hi count)[index]'(by rw [dense_size]; exact valid) = find levels (hi - Int.ofNat index) := by
  simp only [dense_eq, List.getElem_toArray, List.getElem_map, scoreRange_at hi count index valid]

/-- 各評価値を個別に閾値探索せず、count個の値をまとめて処理する比較上界。 -/
theorem dense_comparisons_bound (levels : List Int) (hi : Int) (count : Nat) :
    comparisons levels (scoreRange hi count) ≤ levels.length + count := by
  simpa only [scoreRange_length] using comparisons_bound levels (scoreRange hi count)

end PetaProof.ThresholdKeys
