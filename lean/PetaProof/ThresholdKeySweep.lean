import PetaProof.LeafBucketScan

/-! 評価値を降順に一度走査して、閾値の最初の到達番号を求める。 -/
namespace PetaProof.ThresholdKeys

def find : List Int → Int → Option Nat
  | [], _ => none
  | threshold :: rest, score => if threshold ≤ score then some 0 else (find rest score).map Nat.succ

def atOffset (offset : Nat) (levels : List Int) (score : Int) : Option Nat :=
  (find levels score).map (fun key => offset + key)

theorem atOffset_skip (offset : Nat) (threshold : Int) (rest : List Int) (score : Int)
    (below : score < threshold) :
    atOffset (offset + 1) rest score = atOffset offset (threshold :: rest) score := by
  simp only [atOffset, find, if_neg (show ¬ threshold ≤ score by omega), Option.map_map]
  congr 1
  funext key
  simp only [Function.comp_apply]
  omega

/-- 成功なら次の評価値へ、不成功なら次の閾値へ進む。どちらも巻き戻さない。 -/
def sweep (offset : Nat) (levels scores : List Int) : List (Int × Option Nat) :=
  match levels, scores with
  | [], _ => scores.map (fun score => (score, none))
  | _, [] => []
  | threshold :: rest, score :: tail =>
    if threshold ≤ score then (score, some offset) :: sweep offset (threshold :: rest) tail
    else sweep (offset + 1) rest (score :: tail)
termination_by levels.length + scores.length

theorem sweep_correct (offset : Nat) (levels scores : List Int)
    (descending : scores.Pairwise (fun a b => b ≤ a)) :
    sweep offset levels scores = scores.map (fun score => (score, atOffset offset levels score)) := by
  induction levels generalizing offset scores with
  | nil => simp [sweep, atOffset, find]
  | cons threshold rest ih =>
    induction scores generalizing offset with
    | nil => simp [sweep]
    | cons score tail tailIH =>
      by_cases hit : threshold ≤ score
      · simp only [sweep, if_pos hit, List.map_cons]
        rw [tailIH offset descending.of_cons]
        simp [atOffset, find, hit]
      · rw [sweep, if_neg hit, ih (offset + 1) (score :: tail) descending]
        apply List.map_congr_left
        intro value member
        have below : value < threshold := by
          rcases List.mem_cons.mp member with same | later
          · subst value; omega
          · have lower := List.rel_of_pairwise_cons descending later
            omega
        exact congrArg (fun key => (value, key)) (atOffset_skip offset threshold rest value below)

/-- 閾値と評価値の比較回数。行の書込と空列の判定は別に数える。 -/
def comparisons (levels scores : List Int) : Nat :=
  match levels, scores with
  | [], _ => 0
  | _, [] => 0
  | threshold :: rest, score :: tail =>
    1 + if threshold ≤ score then comparisons (threshold :: rest) tail else comparisons rest (score :: tail)
termination_by levels.length + scores.length

theorem comparisons_bound (levels scores : List Int) :
    comparisons levels scores ≤ levels.length + scores.length := by
  induction levels generalizing scores with
  | nil => simp [comparisons]
  | cons threshold rest ih =>
    induction scores with
    | nil => simp [comparisons]
    | cons score tail tailIH =>
      by_cases hit : threshold ≤ score
      · have bound := tailIH
        simp only [comparisons, if_pos hit, List.length_cons] at *
        omega
      · have bound := ih (score :: tail)
        simp only [comparisons, if_neg hit, List.length_cons] at *
        omega

theorem sweep_length (offset : Nat) (levels scores : List Int)
    (descending : scores.Pairwise (fun a b => b ≤ a)) :
    (sweep offset levels scores).length = scores.length := by
  rw [sweep_correct offset levels scores descending, List.length_map]

end PetaProof.ThresholdKeys
