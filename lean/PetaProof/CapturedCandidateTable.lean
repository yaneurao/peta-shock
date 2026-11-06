import PetaProof.SelectiveRankCapture

/-! 選択保存で得たN要素の順位配列を、既証の候補表へ接続する。
payload生成の正しさ・費用を、この接続だけから導いたとはしない。 -/
namespace PetaProof.SelectiveRankCapture

universe u v
variable {n : Nat} {K : Type u} {S : Type v} {G : ThresholdGame (Fin n)}

def cachedTable (table : G.ValueRankTable) (slots : Array (Option Nat)) : G.ValueRankTable where
  value := table.value
  bounded := table.bounded
  rank := fun _ vertex => storedRank slots vertex

theorem cachedTable_eq (table : G.ValueRankTable) (slots : Array (Option Nat))
    (correct : ∀ vertex, storedRank slots vertex = table.rank (table.value vertex) vertex) :
    cachedTable table slots = table.diagonal := by
  unfold cachedTable ThresholdGame.ValueRankTable.diagonal
  congr 1
  funext level vertex
  exact correct vertex

theorem cached_admissible (table : G.ValueRankTable) (slots : Array (Option Nat))
    (correct : ∀ vertex, storedRank slots vertex = table.rank (table.value vertex) vertex)
    (vertex : Fin n) (move : Move (Fin n)) :
    (cachedTable table slots).admissibleMove vertex move ↔ table.admissibleMove vertex move := by
  rw [cachedTable_eq table slots correct]
  exact table.diagonal_admissible vertex move

theorem streamed_admissible (table : G.ValueRankTable)
    (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (good : S → Prop) (preserved : ∀ key state, good state → good (step key state))
    (correct : ∀ key state, good state → ∀ vertex, vertex ∈ requests key →
      payload key (step key state) vertex = table.rank (table.value vertex) vertex)
    (levels : List K) (state : S) (valid : good state)
    (covered : ∀ vertex, vertex ∈ levels.flatMap requests ∨ table.rank (table.value vertex) vertex = 0)
    (vertex : Fin n) (move : Move (Fin n)) :
    (cachedTable table (run step requests payload levels state (Array.replicate n none)).2).admissibleMove vertex move ↔
      table.admissibleMove vertex move := by
  apply cached_admissible
  exact run_complete step requests payload good (fun vertex => table.rank (table.value vertex) vertex)
    preserved correct levels state valid covered

/-- 配列化は候補集合そのものを変えず、履歴依存選択の保証も保存する。 -/
theorem streamed_plan_lower (table : G.ValueRankTable) (replies : table.AllReplies)
    (step : K → S → S) (requests : K → List (Fin n)) (payload : K → S → Fin n → Nat)
    (good : S → Prop) (preserved : ∀ key state, good state → good (step key state))
    (correct : ∀ key state, good state → ∀ vertex, vertex ∈ requests key →
      payload key (step key state) vertex = table.rank (table.value vertex) vertex)
    (levels : List K) (state : S) (valid : good state)
    (covered : ∀ vertex, vertex ∈ levels.flatMap requests ∨ table.rank (table.value vertex) vertex = 0)
    (self opponent : G.MovePlan)
    (selected : (cachedTable table (run step requests payload levels state (Array.replicate n none)).2).AdmissiblePlan self)
    (root : Fin n) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply table.terminal_lower replies self opponent _ root payoff result
  intro history vertex own
  exact (streamed_admissible table step requests payload good preserved correct levels state valid covered vertex
    (self.choose history vertex)).mp (selected history vertex own)

end PetaProof.SelectiveRankCapture

namespace PetaProof.ThresholdGame.StratumFamily

universe u
variable {V : Type u} {G : ThresholdGame V}

/-- 最低値の層は順位条件を持たず、要求から省いて既定順位0としてよい。 -/
theorem bottom_diagonal_rank (family : G.StratumFamily) (vertex : V) (bottom : family.value vertex = -G.mate) :
    family.table.diagonal.rank 0 vertex = 0 := by
  have positive := G.mate_positive
  simp [ValueRankTable.diagonal, table, bottom, show ¬ 0 < -G.mate by omega]

end PetaProof.ThresholdGame.StratumFamily
