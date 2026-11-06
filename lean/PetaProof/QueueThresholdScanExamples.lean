import PetaProof.QueueThresholdScan
import PetaProof.QueueThresholdControlExamples

/-! AND残数の閾値間保持、leaf帯の端点、初回記録と反対視点の整数値。 -/
namespace PetaProof.QueueThresholdScanExamples

open ThresholdGame

/-- 相手の手番で利得30か20の二択。元プレイヤーが保証できる値は20である。 -/
def game : ThresholdGame Unit where
  legal := fun _ move => move = .leaf 30 ∨ move = .leaf 20
  owner := fun _ => true
  check := fun _ _ => False
  player := false
  threshold := 30
  mate := 40
  positive := by decide
  bounded := by decide
  alternating := by intro _ _ impossible; cases impossible <;> contradiction
  nonempty_moves := fun _ => ⟨.leaf 30, Or.inl rfl⟩
  no_mutual_cycle := by intro _ _ edge _; exact edge.2

def move (edge : Bool) : Move Unit := if edge then .leaf 20 else .leaf 30

def indexed : game.IndexedMoves Bool where
  outgoing := fun _ => [false, true]
  source := fun _ => ()
  move := move
  unique := fun _ => by decide
  at_source := by intro edge; cases edge <;> decide
  source_of_mem := by intro vertex _ _; cases vertex; rfl
  legal := by intro _ edge _; cases edge <;> simp [move, game]
  covers := by
    intro _ candidate legal
    rcases legal with same | same
    · exact ⟨false, by decide, same.symm⟩
    · exact ⟨true, by decide, same.symm⟩

def context : game.QueueContext Bool where
  vertices := [()]
  unique := by simp
  covered := by intro vertex; cases vertex; simp
  indexed := indexed
  parents := {
    incoming := fun _ => []
    unique := fun _ => by simp
    exact := by intro _ edge; cases edge <;> simp [indexed, move]
  }
  core := fun _ => false
  checked := fun _ _ => false
  check_correct := by intro _ _; simp [game]

def top := context.atLevel 40 (by decide) (by decide)
def at30 := top.atLevel 30 (by decide) (by decide)
def at20 := at30.atLevel 20 (by decide) (by decide)
def initial := top.seeded
def after30 := top.phase 30 (by decide) (by decide) initial
def after20 := at30.phase 20 (by decide) (by decide) after30
def after10 := at20.phase 10 (by decide) (by decide) after20

theorem first_band : top.leafBand 30 40 = [false] := by decide
theorem second_band : at30.leafBand 20 30 = [true] := by decide
theorem empty_same_level_band : at30.leafBand 30 30 = [] := by decide
theorem no_repeat_below_twenty : at20.leafBand 10 20 = [] := by decide

theorem initial_counter_two : (initial.counters ()).left = 2 ∧ initial.notified false = false ∧ initial.notified true = false := by decide

theorem nonempty_seed_notifies_once : (context.seeded.counters ()).left = 1 ∧
    context.seeded.notified false = true ∧ context.seeded.notified true = false := by decide

theorem first_equal_level_does_not_notify_twice :
    ((context.phase 30 (by decide) (by decide) context.seeded).counters ()).left = 1 ∧
    ((context.phase 30 (by decide) (by decide) context.seeded).counters ()).admitted = false := by decide

theorem and_partial_at_thirty : (after30.counters ()).left = 1 ∧
    (after30.counters ()).admitted = false ∧ after30.notified false = true ∧ after30.notified true = false := by decide

theorem and_finishes_at_twenty : (after20.counters ()).left = 0 ∧ (after20.counters ()).admitted = true ∧
    after20.notified false = true ∧ after20.notified true = true ∧ after20.queue.popped = [()] := by decide

theorem no_new_work_at_ten : after10 = after20 := rfl

theorem lower_leaf_is_fresh : after30.notified true = false := by
  obtain ⟨certificate⟩ := top.phase_certified initial top.seeded_certificate 30 (by decide) (by decide)
  exact at30.leafBand_fresh after30 certificate 20 true (by decide)

theorem boundary_generated_at_twenty : at20.Boundary after20 :=
  at30.phase_boundary after30 (top.phase_boundary initial top.seeded_boundary 30 (by decide) (by decide))
    20 (by decide) (by decide)

def levels : List Int := [40, 30, 20, 10]
theorem valid : ∀ t ∈ levels, 0 < t ∧ t ≤ game.mate := by
  intro t member
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same <;> subst t <;> decide

def result := scanQueues (game.retune 40 (by decide) (by decide)) top levels valid initial (fun _ => 0)

theorem first_record_is_twenty : result.2 () = 20 := by decide
theorem final_counter_kept : (result.1.counters ()).left = 0 ∧ result.1.queue.popped = [()] := by decide

def criticalLevels : List Int := [40, 30, 20]

theorem critical_iff (t : Int) : game.CriticalLevel t ↔ t = 40 ∨ t = 30 ∨ t = 20 := by
  constructor
  · rintro ⟨_, _, top | ⟨_, high | low⟩⟩
    · exact Or.inl top
    · exact Or.inr (Or.inl (Move.leaf.inj high))
    · exact Or.inr (Or.inr (Move.leaf.inj low))
  · rintro (same | same | same) <;> subst t
    · exact ⟨by decide, by decide, Or.inl rfl⟩
    · exact ⟨by decide, by decide, Or.inr ⟨(), Or.inl rfl⟩⟩
    · exact ⟨by decide, by decide, Or.inr ⟨(), Or.inr rfl⟩⟩

theorem critical_valid : ∀ t ∈ criticalLevels, game.CriticalLevel t := by
  intro t member
  apply (critical_iff t).mpr
  simpa [criticalLevels] using member

theorem bounded_leaves : game.BoundedLeaves := by
  intro _ score legal
  rcases legal with high | low
  · have := Move.leaf.inj high; change -40 ≤ score ∧ score ≤ 40; omega
  · have := Move.leaf.inj low; change -40 ≤ score ∧ score ≤ 40; omega

theorem no_own_cycles : ∀ vertex, CyclicVertex game.OpponentChecking vertex → context.core vertex = true := by
  intro _ ⟨_, edge, _⟩
  cases edge.1 <;> contradiction

theorem no_other_cycles : ∀ vertex, CyclicVertex game.opposite.OpponentChecking vertex → false = true := by
  intro _ ⟨_, edge, _⟩
  cases edge.1 <;> contradiction

theorem queue_scan_maximum : game.PositiveMaximum ()
    (context.positiveQueueValues criticalLevels (fun t member =>
      ⟨(critical_valid t member).1, (critical_valid t member).2.1⟩) ()) :=
  context.positiveQueueValues_correct bounded_leaves criticalLevels critical_valid
    (by intro t critical; simpa [criticalLevels] using (critical_iff t).mp critical) (by decide) no_own_cycles ()

theorem opposite_has_no_positive_leaves : (context.opposite (fun _ => false)).goodLeaves = [] := by decide

/-- 同じ通常状態での全閾値走査から、両側の合成までを最上位定理で検査する。 -/
theorem computed_integer_value : game.ExactValue () (context.computedQueueValue (fun _ => false) ()) :=
  context.computedQueueValue_exact (fun _ => false) bounded_leaves no_own_cycles no_other_cycles ()

theorem sparse_record_is_twenty : context.positiveQueueValues criticalLevels
    (fun t member => ⟨(critical_valid t member).1, (critical_valid t member).2.1⟩) () = 20 := by decide

theorem exact_twenty : game.ExactValue () 20 := by
  have maximum := queue_scan_maximum
  rw [sparse_record_is_twenty] at maximum
  exact PositiveMaximum.exact_of_positive game bounded_leaves context.vertices context.covered () maximum (by decide)

theorem computed_integer_is_twenty : context.computedQueueValue (fun _ => false) () = 20 :=
  ExactValue.unique game context.vertices context.covered () computed_integer_value exact_twenty

end PetaProof.QueueThresholdScanExamples
