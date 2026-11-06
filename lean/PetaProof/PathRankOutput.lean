import PetaProof.PathRank

/-! 無限rankを含む符号別選好を、保存値の最大手選択と元ゲームの下限へ接続する。 -/
namespace PetaProof.PathRank

universe u v
variable {E : Type u} {V : Type v}

theorem encoded_maximum_iff (raw : E → Int) (rank : E → Rank) (cap : Nat)
    (safe : E → Prop) (best : Int) (candidates : List E)
    (covers : ∀ edge, safe edge → edge ∈ candidates)
    (upper : ∀ edge ∈ candidates, raw edge ≤ best)
    (present : ∃ edge ∈ candidates, safe edge ∧ raw edge = best)
    (edge : E) (member : edge ∈ candidates) :
    (∀ other ∈ candidates,
      OutputPreference.encoded raw (Preferred raw rank cap safe best) best other ≤
      OutputPreference.encoded raw (Preferred raw rank cap safe best) best edge) ↔
      Preferred raw rank cap safe best edge := by
  obtain ⟨witness, kept, chosen⟩ := preferred_exists raw rank cap safe best candidates covers present
  exact OutputPreference.maximum_iff raw _ candidates best upper (fun _ _ accepted => accepted.2.1)
    ⟨witness, kept, chosen⟩ edge member

/-- 親局面の視点でrankを引く。子局面の手番側のrankへ勝手に反転しない。 -/
theorem encoded_plan_lower [DecidableEq V] {G : ThresholdGame V}
    (table : G.ValueRankTable) (replies : table.AllReplies)
    (candidates : V → List E) (move : E → Move V)
    (raw : V → E → Int) (rank : V → E → Rank) (cap : Nat) (best : V → Int)
    (upper : ∀ vertex, G.owner vertex = G.player →
      ∀ edge ∈ candidates vertex, raw vertex edge ≤ best vertex)
    (available : ∀ vertex, G.owner vertex = G.player →
      ∃ edge ∈ candidates vertex, table.admissibleMove vertex (move edge) ∧ raw vertex edge = best vertex)
    (self opponent : G.MovePlan)
    (selected : ∀ history vertex, G.owner vertex = G.player →
      ∃ edge ∈ candidates vertex, self.choose history vertex = move edge ∧
        ∀ other ∈ candidates vertex,
          OutputPreference.encoded (raw vertex)
            (Preferred (raw vertex) (rank vertex) cap
              (fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)) (best vertex))
            (best vertex) other ≤
          OutputPreference.encoded (raw vertex)
            (Preferred (raw vertex) (rank vertex) cap
              (fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)) (best vertex))
            (best vertex) edge)
    (root : V) (payoff : Int)
    (result : G.TerminalResult (G.combinePlans self opponent) root payoff) : table.value root ≤ payoff := by
  apply table.terminal_lower replies self opponent _ root payoff result
  intro history vertex own
  let safe := fun e => e ∈ candidates vertex ∧ table.admissibleMove vertex (move e)
  obtain ⟨first, member, legal, same⟩ := available vertex own
  obtain ⟨edge, edgeMember, chosen, maximal⟩ := selected history vertex own
  have accepted := (encoded_maximum_iff (raw vertex) (rank vertex) cap safe (best vertex)
    (candidates vertex) (fun _ allowed => allowed.1) (upper vertex own)
    ⟨first, member, ⟨member, legal⟩, same⟩ edge edgeMember).mp maximal
  rw [chosen]
  exact accepted.1.2

/-- rankが無限でも安全な下限を破れない。端点-mate自体しか保証しない局面は含めない。 -/
theorem no_mate_loss [DecidableEq V] {G : ThresholdGame V}
    (table : G.ValueRankTable) (replies : table.AllReplies)
    (self opponent : G.MovePlan) (safe : table.AdmissiblePlan self)
    (root : V) (better : -G.mate < table.value root)
    (result : G.TerminalResult (G.combinePlans self opponent) root (-G.mate)) : False := by
  have lower := table.terminal_lower replies self opponent safe root (-G.mate) result
  omega

end PetaProof.PathRank
