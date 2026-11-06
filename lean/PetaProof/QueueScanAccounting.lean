import PetaProof.QueueScanLog

/-! 実際の全閾値走査から、通常popとleaf/内部辺通知の高々N+E回という会計を導く。 -/
namespace PetaProof.DistinctWork

universe u
variable {A : Type u} [DecidableEq A]

private theorem count_lt_two (items : List A) (unique : items.Nodup) (item : A) : items.count item < 2 := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = item
    · subst head
      simp [List.count_cons, List.count_eq_zero_of_not_mem parts.1]
    · simpa [List.count_cons, same, Ne.symm same] using ih parts.2

/-- 一意な作業対象が有限一覧に含まれれば、その一覧の長さで作業数を上から抑えられる。 -/
theorem length_le (items domain : List A) (unique : items.Nodup)
    (within : ∀ item ∈ items, item ∈ domain) : items.length ≤ domain.length := by
  have bound := history_length_bound domain items 2 within (fun item _ => count_lt_two items unique item)
  simpa using bound

end PetaProof.DistinctWork

namespace PetaProof.ThresholdGame

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def scanLeafLog : (G : ThresholdGame V) → (ctx : G.QueueContext E) →
    (levels : List Int) → (∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) → List E
  | _, _, [], _ => []
  | G, ctx, t :: rest, valid =>
    ctx.leafBand t G.threshold ++
      scanLeafLog (G.retune t (valid t (by simp)).1 (valid t (by simp)).2)
        (ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2) rest
        (fun s member => valid s (by simp [member]))

omit [DecidableEq V] [DecidableEq E] in
theorem scanLeafLog_below (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (edge : E) (member : edge ∈ scanLeafLog G ctx levels valid) :
    ∃ score, ctx.indexed.move edge = .leaf score ∧ score < G.threshold := by
  induction levels generalizing G with
  | nil => cases member
  | cons t rest ih =>
    rcases List.mem_append.mp member with head | tail
    · obtain ⟨score, same, _, upper⟩ := (ctx.leafBand_spec t G.threshold edge).mp head
      exact ⟨score, same, upper⟩
    · obtain ⟨score, same, upper⟩ := ih _ _ _ descending.of_cons
        (fun s present => Int.le_of_lt (List.rel_of_pairwise_cons descending present)) tail
      exact ⟨score, same, Int.lt_of_lt_of_le upper (below t (by simp))⟩

omit [DecidableEq V] [DecidableEq E] in
theorem scanLeafLog_unique (G : ThresholdGame V) (ctx : G.QueueContext E)
    (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (scanLeafLog G ctx levels valid).Nodup := by
  induction levels generalizing G with
  | nil => exact List.nodup_nil
  | cons t rest ih =>
    let H := G.retune t (valid t (by simp)).1 (valid t (by simp)).2
    let low := ctx.atLevel t (valid t (by simp)).1 (valid t (by simp)).2
    have tail_below : ∀ s ∈ rest, s ≤ H.threshold := fun s member =>
      Int.le_of_lt (List.rel_of_pairwise_cons descending member)
    apply List.pairwise_append.mpr
    refine ⟨ctx.leafBand_unique t G.threshold, ih H low _ descending.of_cons tail_below, ?_⟩
    intro a head b tail equal
    obtain ⟨highScore, highMove, lower, _⟩ := (ctx.leafBand_spec t G.threshold a).mp head
    obtain ⟨lowScore, lowMove, upper⟩ := scanLeafLog_below H low rest _ descending.of_cons tail_below b tail
    have same := Move.leaf.inj (highMove.symm.trans ((congrArg ctx.indexed.move equal).trans lowMove))
    change lowScore < t at upper
    omega

namespace QueueContext

variable {G : ThresholdGame V} (ctx : G.QueueContext E)

omit [DecidableEq V] [DecidableEq E] in
/-- 異なる子の逆辺列は、元辺の到着先の一意性から互いに素である。 -/
theorem incoming_flat_unique (pops : List V) (unique : pops.Nodup) :
    (pops.flatMap ctx.parents.incoming).Nodup := by
  induction pops with
  | nil => exact List.nodup_nil
  | cons child rest ih =>
    have parts := List.nodup_cons.mp unique
    apply List.pairwise_append.mpr
    refine ⟨ctx.parents.unique child, ih parts.2, ?_⟩
    intro a first b second equal
    obtain ⟨other, member, present⟩ := List.mem_flatMap.mp second
    have first_move := (ctx.parents.exact child a).mp first
    have second_move := (ctx.parents.exact other b).mp present
    have same := Move.node.inj (first_move.symm.trans ((congrArg ctx.indexed.move equal).trans second_move))
    exact parts.1 (same ▸ member)

theorem seeded_popped : ctx.seeded.queue.popped = [] := by
  unfold seeded
  rw [PropagationState.notifyMany_popped]
  rfl

def ordinaryLog (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : OrdinaryLog V E :=
  scanQueueLog G ctx levels valid ctx.seeded

def leafLog (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : List E :=
  ctx.goodLeaves ++ scanLeafLog G ctx levels valid

omit [DecidableEq V] [DecidableEq E] in
theorem leafLog_unique (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.leafLog levels valid).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨ctx.allEdges_unique.filter _, scanLeafLog_unique G ctx levels valid descending below, ?_⟩
  intro a first b second equal
  obtain ⟨highScore, highMove, lower⟩ := (ctx.goodLeaves_spec a).mp first
  obtain ⟨lowScore, lowMove, upper⟩ := scanLeafLog_below G ctx levels valid descending below b second
  have same := Move.leaf.inj (highMove.symm.trans ((congrArg ctx.indexed.move equal).trans lowMove))
  omega

omit [DecidableEq V] [DecidableEq E] in
theorem leafLog_is_leaf (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold)
    (edge : E) (member : edge ∈ ctx.leafLog levels valid) : ∃ score, ctx.indexed.move edge = .leaf score := by
  rcases List.mem_append.mp member with initial | later
  · obtain ⟨score, same, _⟩ := (ctx.goodLeaves_spec edge).mp initial
    exact ⟨score, same⟩
  · obtain ⟨score, same, _⟩ := scanLeafLog_below G ctx levels valid descending below edge later
    exact ⟨score, same⟩

/-- ログのpop数は、全閾値で引き継いだ最終の取り出し履歴の長さに等しい。 -/
theorem ordinaryLog_pops (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) :
    (ctx.ordinaryLog levels valid).pops = (scanQueues G ctx levels valid ctx.seeded (fun _ => 0)).1.queue.popped := by
  have logged := scanQueueLog_sound G ctx levels valid ctx.seeded (fun _ => 0)
  simpa only [ctx.seeded_popped, List.nil_append] using logged.1

theorem ordinaryLog_unique (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.ordinaryLog levels valid).pops.Nodup ∧ (ctx.ordinaryLog levels valid).callbacks.Nodup := by
  have final := scanQueue_final_invariant G ctx levels valid descending below ctx.seeded ctx.seeded_certificate (fun _ => 0)
  have pops : (ctx.ordinaryLog levels valid).pops.Nodup := by
    rw [ctx.ordinaryLog_pops]
    exact AdmissionQueue.popped_unique _ final
  refine ⟨pops, ?_⟩
  unfold ordinaryLog
  rw [(scanQueueLog_sound G ctx levels valid ctx.seeded (fun _ => 0)).2]
  exact ctx.incoming_flat_unique _ pops

def notificationLog (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : List E :=
  ctx.leafLog levels valid ++ (ctx.ordinaryLog levels valid).callbacks

/-- leafと内部辺も互いに素なので、通常の元辺走査全体で重複がない。 -/
theorem notificationLog_unique (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.notificationLog levels valid).Nodup := by
  have ordinary := ctx.ordinaryLog_unique levels valid descending below
  apply List.pairwise_append.mpr
  refine ⟨ctx.leafLog_unique levels valid descending below, ordinary.2, ?_⟩
  intro a first b second equal
  obtain ⟨score, leaf⟩ := ctx.leafLog_is_leaf levels valid descending below a first
  unfold ordinaryLog at second
  rw [(scanQueueLog_sound G ctx levels valid ctx.seeded (fun _ => 0)).2] at second
  obtain ⟨child, _, present⟩ := List.mem_flatMap.mp second
  have node := (ctx.parents.exact child b).mp present
  have impossible := leaf.symm.trans ((congrArg ctx.indexed.move equal).trans node)
  cases impossible

/-- 数えるのは通常FIFOのpopと元辺への通知試行。局所削除の内部作業は含めない。 -/
def ordinaryWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  (ctx.ordinaryLog levels valid).pops.length + (ctx.notificationLog levels valid).length

theorem ordinaryPops_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.ordinaryLog levels valid).pops.length ≤ ctx.vertices.length :=
  DistinctWork.length_le _ ctx.vertices (ctx.ordinaryLog_unique levels valid descending below).1
    (fun vertex _ => ctx.covered vertex)

theorem notificationLog_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    (ctx.notificationLog levels valid).length ≤ ctx.allEdges.length :=
  DistinctWork.length_le _ ctx.allEdges (ctx.notificationLog_unique levels valid descending below)
    (fun edge _ => ctx.allEdges_contains edge)

theorem ordinaryWork_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) (below : ∀ t ∈ levels, t ≤ G.threshold) :
    ctx.ordinaryWork levels valid ≤ ctx.vertices.length + ctx.allEdges.length := by
  exact Nat.add_le_add (ctx.ordinaryPops_bound levels valid descending below) (ctx.notificationLog_bound levels valid descending below)

/-- 主値計算と同じく上限で開始し、全閾値の通常イベントを数える。 -/
def positiveQueueWork (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate) : Nat :=
  (ctx.atLevel G.mate G.mate_positive (Int.le_refl _)).ordinaryWork levels valid

theorem positiveQueueWork_bound (levels : List Int) (valid : ∀ t ∈ levels, 0 < t ∧ t ≤ G.mate)
    (descending : levels.Pairwise (fun a b => b < a)) :
    ctx.positiveQueueWork levels valid ≤ ctx.vertices.length + ctx.allEdges.length :=
  (ctx.atLevel G.mate G.mate_positive (Int.le_refl _)).ordinaryWork_bound levels valid descending
    (fun t member => (valid t member).2)

theorem two_sides_work_bound (otherCore : V → Bool)
    (ownLevels : List Int) (ownValid : ∀ t ∈ ownLevels, 0 < t ∧ t ≤ G.mate)
    (ownDescending : ownLevels.Pairwise (fun a b => b < a))
    (otherLevels : List Int) (otherValid : ∀ t ∈ otherLevels, 0 < t ∧ t ≤ G.mate)
    (otherDescending : otherLevels.Pairwise (fun a b => b < a)) :
    ctx.positiveQueueWork ownLevels ownValid + (ctx.opposite otherCore).positiveQueueWork otherLevels otherValid ≤
      2 * (ctx.vertices.length + ctx.allEdges.length) := by
  have own := ctx.positiveQueueWork_bound ownLevels ownValid ownDescending
  have other := (ctx.opposite otherCore).positiveQueueWork_bound otherLevels otherValid otherDescending
  change (ctx.opposite otherCore).positiveQueueWork otherLevels otherValid ≤
    ctx.vertices.length + ctx.allEdges.length at other
  omega

end QueueContext
end PetaProof.ThresholdGame
