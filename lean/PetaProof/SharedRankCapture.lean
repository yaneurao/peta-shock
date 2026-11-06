import PetaProof.SharedRankRequests

/-! 共通証拠を供給するインターフェイスと選択保存を接続する。
共通証拠供給器は非計算的なままであり、実phaseの効率的な生成器の検証とは区別する。 -/
namespace PetaProof.ThresholdGame.SharedRankFamily

universe u
variable {n : Nat} {E : Type u} {G : ThresholdGame (Fin n)}
variable {ctx : G.QueueContext E} {otherCore : Fin n → Bool}
variable (shared : SharedRankFamily ctx otherCore) (requests : Requests shared)

/-- 保存側は今回のキーとN要素だけを持つ。証拠供給器自体の格納量は別途である。 -/
noncomputable def captured : Array (Option Nat) :=
  (SelectiveRankCapture.run (fun key _ => key) requests.get (fun _ current => shared.payload current)
    shared.keys (false, 0) (Array.replicate n none)).2

theorem captured_size : (shared.captured requests).size = n := by
  unfold captured
  rw [SelectiveRankCapture.run_size]
  simp

/-- 最終表とのpayload一致を外から仮定せず、固定した共通証拠と取得先から導く。 -/
theorem captured_correct (vertex : Fin n) :
    SelectiveRankCapture.storedRank (shared.captured requests) vertex =
      shared.table.rank (shared.table.value vertex) vertex := by
  apply SelectiveRankCapture.run_complete (fun key _ => key) requests.get
    (fun _ current => shared.payload current) (fun _ => True)
    (fun vertex => shared.table.rank (shared.table.value vertex) vertex)
    (fun _ _ _ => trivial) _ shared.keys (false, 0) trivial _ vertex
  · intro key _ _ vertex present
    exact shared.target_payload vertex key ((requests.get_iff key vertex).mp present)
  · intro vertex
    cases found : shared.target vertex with
    | none => exact Or.inr (shared.omitted_rank_zero vertex found)
    | some key =>
      exact Or.inl (List.mem_flatMap.mpr
        ⟨key, shared.target_registered vertex key found, (requests.get_iff key vertex).mpr found⟩)

theorem captured_reads_bound : SelectiveRankCapture.reads shared.keys requests.get ≤ n :=
  SelectiveRankCapture.reads_bound shared.keys requests.get shared.target shared.keys_unique requests.get_unique
    (fun key vertex present => (requests.get_iff key vertex).mp present)

theorem captured_admissible (vertex : Fin n) (move : Move (Fin n)) :
    (SelectiveRankCapture.cachedTable shared.table (shared.captured requests)).admissibleMove vertex move ↔
      shared.table.admissibleMove vertex move :=
  SelectiveRankCapture.cached_admissible shared.table _ (shared.captured_correct requests) vertex move

theorem captured_nonempty (vertex : Fin n) (own : G.owner vertex = G.player) :
    ∃ move, (SelectiveRankCapture.cachedTable shared.table (shared.captured requests)).admissibleMove vertex move := by
  obtain ⟨move, safe⟩ := shared.nonempty vertex own
  exact ⟨move, (shared.captured_admissible requests vertex move).mpr safe⟩

theorem captured_plan_lower (self opponent : G.MovePlan)
    (selected : (SelectiveRankCapture.cachedTable shared.table (shared.captured requests)).AdmissiblePlan self)
    (root : Fin n) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : shared.value root ≤ payoff := by
  apply shared.table.terminal_lower shared.replies self opponent _ root payoff result
  intro history vertex own
  exact (shared.captured_admissible requests vertex (self.choose history vertex)).mp (selected history vertex own)

/-- 共通証拠・要求表・保存結果を全て入力から構成し、追加のpayload一致仮定を置かない。 -/
theorem generated_capture_lower [DecidableEq E] (atTop : G.threshold = G.mate)
    (leaves : G.BoundedLeaves)
    (covers : ∀ vertex, CyclicVertex G.OpponentChecking vertex → ctx.core vertex = true)
    (otherCovers : ∀ vertex, CyclicVertex G.opposite.OpponentChecking vertex → otherCore vertex = true)
    (self opponent : G.MovePlan)
    (selected : let source : SharedRankFamily ctx otherCore := fromGenerated atTop leaves covers otherCovers
      (SelectiveRankCapture.cachedTable source.table (source.captured source.buildRequests)).AdmissiblePlan self)
    (root : Fin n) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) :
    ctx.generatedValue otherCore root ≤ payoff := by
  let source : SharedRankFamily ctx otherCore := fromGenerated atTop leaves covers otherCovers
  exact source.captured_plan_lower source.buildRequests self opponent selected root payoff result

end PetaProof.ThresholdGame.SharedRankFamily
