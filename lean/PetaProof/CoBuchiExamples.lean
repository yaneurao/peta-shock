import PetaProof.CoBuchi

/-! 一時的な非王手は許される一方、非王手を含む循環は許されないことの検査。 -/
namespace PetaProof.CoBuchiExamples

def edge (_ w : Bool) : Prop := w = false
def bad (v _ : Bool) : Prop := v = true

def transientRanking : BadEdgeRanking edge bad where
  rank := fun v => if v then 1 else 0
  decreasing := by intro v w e; cases v <;> subst w <;> decide
  strict := by intro v w e hb; subst v; subst w; decide

theorem transient_edge_is_allowed :
    ∀ v w, edge v w → bad v w → ¬ Reachable edge w v := by
  intro v w e hb
  exact transientRanking.no_bad_cycle e hb

def oneBadEdge : Walk edge true false := .cons rfl (.nil false)

theorem one_bad_edge_count : oneBadEdge.badCount bad = 1 := by
  simp [oneBadEdge, Walk.badCount, bad]

theorem transient_then_forever_safe :
    ∃ n, ∀ i, n ≤ i → ¬ bad ((fun k => k == 0) i) ((fun k => k == 0) (i + 1)) := by
  apply transientRanking.eventually_no_bad [false, true] (by intro v; cases v <;> simp)
  intro i
  simp [edge]

/-- 自己循環に悪い辺があるなら、どんな自然数順位も証拠にならない。 -/
theorem bad_self_loop_rejected : ¬ Nonempty (BadEdgeRanking
    (fun _ _ : Unit => True) (fun _ _ => True)) := by
  rintro ⟨ranking⟩
  have decrease := ranking.strict () () trivial trivial
  omega

end PetaProof.CoBuchiExamples
