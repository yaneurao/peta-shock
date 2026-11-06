import PetaProof.OutputPreference

/-! 無限を有限距離より大きく扱う経路選好のrank。安全性の証拠の順位とは別。 -/
namespace PetaProof.PathRank

universe u
variable {E : Type u}

abbrev Rank := Option Nat

/-- noneは無限rank。機械整数の飽和値と混同しない。 -/
def LE : Rank → Rank → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

def Bounded (cap : Nat) (rank : Rank) : Prop :=
  ∀ n, rank = some n → n ≤ cap

/-- 有限上界が既知なら、上界+1を無限専用の比較キーに使える。 -/
def code (cap : Nat) : Rank → Nat
  | none => cap + 1
  | some n => n

theorem code_le_iff (cap : Nat) (a b : Rank) (ha : Bounded cap a) (hb : Bounded cap b) :
    code cap a ≤ code cap b ↔ LE a b := by
  cases a with
  | none => cases b with
    | none => simp [code, LE]
    | some b => have bound := hb b rfl; simp [code, LE]; omega
  | some a => cases b with
    | none => have bound := ha a rfl; simp [code, LE]; omega
    | some b => rfl

theorem bounded_none (cap : Nat) : Bounded cap none := by
  intro n impossible
  cases impossible

theorem le_antisymm (a b : Rank) (ab : LE a b) (ba : LE b a) : a = b := by
  cases a <;> cases b <;> simp_all [LE]
  omega

def Preferred (raw : E → Int) (rank : E → Rank) (cap : Nat)
    (safe : E → Prop) (best : Int) : E → Prop :=
  OutputPreference.Preferred raw (fun edge => code cap (rank edge)) safe best

theorem preferred_exists (raw : E → Int) (rank : E → Rank) (cap : Nat)
    (safe : E → Prop) (best : Int) (candidates : List E)
    (covers : ∀ edge, safe edge → edge ∈ candidates)
    (present : ∃ edge ∈ candidates, safe edge ∧ raw edge = best) :
    ∃ edge ∈ candidates, Preferred raw rank cap safe best edge :=
  OutputPreference.preferred_exists raw (fun edge => code cap (rank edge)) safe best candidates covers present

theorem preferred_direction (raw : E → Int) (rank : E → Rank) (cap : Nat)
    (safe : E → Prop) (best : Int) (edge other : E)
    (chosen : Preferred raw rank cap safe best edge)
    (he : Bounded cap (rank edge)) (ho : Bounded cap (rank other))
    (allowed : safe other) (same : raw other = best) :
    (0 ≤ best → LE (rank edge) (rank other)) ∧ (best < 0 → LE (rank other) (rank edge)) := by
  have direction := OutputPreference.preferred_direction raw (fun e => code cap (rank e))
    safe best edge other chosen allowed same
  exact ⟨fun sign => (code_le_iff cap _ _ he ho).mp (direction.1 sign),
    fun sign => (code_le_iff cap _ _ ho he).mp (direction.2 sign)⟩

/-- 無限の安全な同点手があれば、負値で選んだ手も無限。危険な手は比較対象に入らない。 -/
theorem negative_prefers_infinite (raw : E → Int) (rank : E → Rank) (cap : Nat)
    (safe : E → Prop) (best : Int) (edge other : E)
    (chosen : Preferred raw rank cap safe best edge) (negative : best < 0)
    (bounded : Bounded cap (rank edge)) (allowed : safe other) (same : raw other = best)
    (infinite : rank other = none) : rank edge = none := by
  have lower := (preferred_direction raw rank cap safe best edge other chosen bounded
    (infinite ▸ bounded_none cap) allowed same).2 negative
  rw [infinite] at lower
  cases found : rank edge with
  | none => rfl
  | some n => simp [found, LE] at lower

end PetaProof.PathRank
