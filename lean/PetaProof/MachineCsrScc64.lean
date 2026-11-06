import PetaProof.RawCallbackDfs64

/-!
生フレーム第一DFSの終了配列を直接逆順に読み、UInt64 CSRの生callbackで第二DFSを実行する。
coreのフラグは計算した番号からの集合仕様。UInt8フラグとの単一状態化はまだ扱わない。
-/
namespace PetaProof.MachineCsrScc64

variable {n : Nat}

def step (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (state : ComponentResultArray.State (2 * n)) (root : Fin (2 * n)) : ComponentResultArray.State (2 * n) :=
  if ComponentLabels32.get state.result root = ComponentLabels32.unset then
    let report := RawCallbackDfs64.explore book seed allow state.roots.length state.result root
    ⟨report.result, state.roots ++ [root]⟩
  else state

theorem step_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (state : ComponentResultArray.State (2 * n)) (root : Fin (2 * n)) :
    step book seed allow state root = ComponentStackArray.step (MachineCsrParents64.parents book seed allow) state root := by
  unfold step ComponentStackArray.step
  rw [RawCallbackDfs64.explore_exact]

def loop (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (order : Array UInt32) : Nat → ComponentResultArray.State (2 * n) → ComponentResultArray.State (2 * n)
  | 0, state => state
  | remaining + 1, state =>
    match order[remaining]?.bind (VertexStack32.decode (2 * n)) with
    | none => loop book seed allow order remaining state
    | some root => loop book seed allow order remaining (step book seed allow state root)

theorem loop_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool)
    (order : Array UInt32) (remaining : Nat) (state : ComponentResultArray.State (2 * n)) :
    loop book seed allow order remaining state =
      ReverseOrderArray.loop order (MachineCsrParents64.parents book seed allow) remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    simp only [loop, ReverseOrderArray.loop]
    cases found : order[remaining]?.bind (VertexStack32.decode (2 * n)) <;>
      simp only [found] <;> rw [ih]
    rw [step_exact]

def labels (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) :
    ComponentResultArray.State (2 * n) :=
  let order := (ForwardDfsRaw32.finish (MachineFrameRows32.rows book allow) (List.finRange (2 * n))).finished
  loop book seed allow order order.size (ComponentResultArray.initial (2 * n))

/-- callback列を逐次処理した実結果は、同じ親列を渡す既証の配列実行に完全一致する。 -/
theorem labels_exact (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) :
    labels book seed allow = RawFrameScc32.labels (MachineFrameRows32.rows book allow)
      (MachineCsrParents64.parents book seed allow) :=
  loop_exact book seed allow _ _ _

theorem labels_seed_independent (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (first second : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) :
    labels book first allow = labels book second allow := by
  have same : MachineCsrParents64.parents book first allow = MachineCsrParents64.parents book second allow := by
    funext vertex
    simp only [MachineCsrParents64.parents, MachineCsrParents64.words,
      MachineCsrParents64.callbacks_seed_independent fits book counts first second]
  rw [labels_exact, labels_exact, same]

theorem labels_model (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) :
    labels book seed allow = ComponentResultArray.finish (MachineCsrParents64.parents book seed allow)
      (ForwardDfs.order (List.finRange (2 * n)) (List.finRange (2 * n))
        (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow))) := by
  rw [labels_exact, RawFrameScc32.labels_exact (MachineCsrParents64.word_capacity fits) _
    (MachineFrameRows32.counts_fit book counts allow), FrameArrayScc.labels_exact,
    ReverseOrderArray.labels_exact (MachineCsrParents64.word_capacity fits),
    ComponentStackArray.finish_exact (MachineCsrParents64.word_capacity fits)]

theorem final_labels (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    let state := labels book seed allow
    ComponentLabels32.get state.result vertex ≠ ComponentLabels32.unset ∧
      (ComponentLabels32.get state.result vertex).toNat = ComponentResultArray.component state vertex ∧
      ComponentResultArray.component state vertex < state.roots.length ∧
      ComponentResultArray.component state vertex < 2 * n := by
  dsimp only
  rw [labels_model fits book counts]
  exact ComponentResultArray.final_labels (MachineCsrParents64.label_capacity fits) _ _
    (ForwardDfs.order_covers _ (CoreEnumeration.finRange_unique _) (CoreEnumeration.finRange_covers _)
      _ (CoreEnumeration.finRange_covers _) _) vertex

theorem computed_component_iff (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (a b : Fin (2 * n)) :
    ComponentResultArray.component (labels book seed allow) a = ComponentResultArray.component (labels book seed allow) b ↔
      ForwardDfs.Mutual (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) a b := by
  rw [labels_exact]
  exact RawFrameScc32.computed_component_iff (MachineCsrParents64.label_capacity fits) _
    (MachineFrameRows32.counts_fit book counts allow) _ (MachineCsrParents64.parents_transpose fits book valid counts seed allow) a b

theorem reach_original_iff (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (allow : UInt32 → UInt32 → Bool) (a b : Fin (2 * n)) :
    ForwardDfs.Reach (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) a b ↔
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode a) (TurnEncoding.decode b)) := by
  constructor
  · rintro ⟨path⟩
    exact ⟨path.mapVertices TurnEncoding.decode (fun x y => (MachineFrameRows32.edge_exact fits book allow x y).mp)⟩
  · rintro ⟨path⟩
    have preserves : ∀ x y, MoveRows32.relation book allow x y →
        ForwardDfs.Edge (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) (TurnEncoding.encode x) (TurnEncoding.encode y) := by
      intro x y edge
      apply (MachineFrameRows32.edge_exact fits book allow _ _).mpr
      simpa only [TurnEncoding.decode_encode] using edge
    have mapped := path.mapVertices TurnEncoding.encode preserves
    rw [TurnEncoding.encode_decode, TurnEncoding.encode_decode] at mapped
    exact ⟨mapped⟩

theorem component_original_iff (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (a b : Fin (2 * n)) :
    ComponentResultArray.component (labels book seed allow) a = ComponentResultArray.component (labels book seed allow) b ↔
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode a) (TurnEncoding.decode b)) ∧
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode b) (TurnEncoding.decode a)) := by
  rw [computed_component_iff fits book valid counts seed allow, ForwardDfs.Mutual,
    reach_original_iff fits book allow, reach_original_iff fits book allow]

/-- 実際のUInt32ラベル同士の比較を、元の機械式許可辺上の相互到達へ直接接続する。 -/
theorem raw_labels_original_iff (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (a b : Fin (2 * n)) :
    ComponentLabels32.get (labels book seed allow).result a = ComponentLabels32.get (labels book seed allow).result b ↔
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode a) (TurnEncoding.decode b)) ∧
      Nonempty (Walk (MoveRows32.relation book allow) (TurnEncoding.decode b) (TurnEncoding.decode a)) := by
  have left := (final_labels fits book counts seed allow a).2.1
  have right := (final_labels fits book counts seed allow b).2.1
  constructor
  · intro same
    apply (component_original_iff fits book valid counts seed allow a b).mp
    rw [← left, ← right, same]
  · intro reachable
    have same := (component_original_iff fits book valid counts seed allow a b).mpr reachable
    rw [← left, ← right] at same
    simpa only [UInt32.ofNat_toNat] using congrArg UInt32.ofNat same

def partition (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) : SccPartition (ForwardDfs.Edge (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow))) where
  component := ComponentResultArray.component (labels book seed allow)
  ordered := by
    rw [labels_model fits book counts, ComponentResultArray.component_exact (MachineCsrParents64.label_capacity fits)]
    exact KosarajuStep.component_ordered _ (CoreEnumeration.finRange_unique _) (CoreEnumeration.finRange_covers _)
      _ (CoreEnumeration.finRange_covers _) _ _ (MachineCsrParents64.parents_transpose fits book valid counts seed allow)
  connected := fun a b same => ((computed_component_iff fits book valid counts seed allow a b).mp same).1

theorem self_loop_absent (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    ¬ ForwardDfs.Edge (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) vertex vertex := by
  rw [MachineFrameRows32.edge_exact fits book allow, MoveRows32.relation_exact fits book valid allow,
    ← SccIndexedView.outgoing_correct]
  exact TurnSharedGraph.no_expanded_self_edge _ _ _

/-- 番号表から循環頂点を選ぶ集合仕様。実行時の追加の成分数え直しではない。 -/
def core (book : MoveRows32.Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) : List (Fin (2 * n)) :=
  CoreEnumeration.core (ComponentCycleFlags.keep (List.finRange (2 * n))
    (ComponentResultArray.component (labels book seed allow)) (fun _ => false)) (List.finRange (2 * n))

theorem core_correct (fits : TurnEncoding32.Fits n) (book : MoveRows32.Book n)
    (valid : MoveRows32.Valid book) (counts : MoveRows32.CountsFit book) (seed : MoveRowsCsr32.Pair)
    (allow : UInt32 → UInt32 → Bool) (vertex : Fin (2 * n)) :
    vertex ∈ core book seed allow ↔ CyclicVertex (MoveRows32.relation book allow) (TurnEncoding.decode vertex) := by
  have bounded : ∀ v, (partition fits book valid counts seed allow).component v < (List.finRange (2 * n)).length := by
    intro v
    simpa only [List.length_finRange] using (final_labels fits book counts seed allow v).2.2.2
  have self : ∀ v, false = true ↔ ForwardDfs.Edge (ForwardDfsRaw32.outgoing (MachineFrameRows32.rows book allow)) v v :=
    fun v => iff_of_false Bool.false_ne_true (self_loop_absent fits book valid allow v)
  exact (ComponentCycleFlags.extracted_core_iff _ (CoreEnumeration.finRange_unique _) (CoreEnumeration.finRange_covers _)
    (partition fits book valid counts seed allow) bounded (fun _ => false) self vertex).trans
      (MachineFrameRows32.cyclic_exact fits book allow vertex)

end PetaProof.MachineCsrScc64
