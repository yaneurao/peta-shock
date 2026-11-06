import PetaProof.MoveRowsCsr

/-!
有限指し手配列と生の(v,j)の共有CSRから二状態SCCへ接続する。
許可判定には展開した親の番号と配列内の指し手番号を渡す。
-/
namespace PetaProof.MoveRowsScc

open IndexedMoveRows
open SccIndexedView
open TurnEncoding (State vertices vertices_unique vertices_cover)
variable {n : Nat}

def allowAt (rows : Rows n) (allow : Nat → Nat → Bool) (edge : Edge rows × Bool) : Bool :=
  allow (TurnEncoding.encode (edge.1.1, edge.2)).val edge.1.2.val

def incoming (rows : Rows n) (seed : Raw) (state : State n) : List (Edge rows × Bool) :=
  (MoveRowsCsr.incoming rows seed state.1).map (fun edge => (edge, !state.2))

theorem incoming_member (rows : Rows n) (seed : Raw) (state : State n) (edge : Edge rows × Bool) :
    edge ∈ incoming rows seed state ↔ (TurnSharedGraph.expanded (view rows)).child edge = some state := by
  rcases state with ⟨vertex, turn⟩
  rcases edge with ⟨edge, side⟩
  rw [TurnSharedGraph.child_correct]
  constructor
  · intro member
    obtain ⟨original, present, pair⟩ := List.mem_map.mp member
    have same := congrArg Prod.fst pair
    have turns := congrArg Prod.snd pair
    dsimp only at same turns
    subst original
    exact ⟨(MoveRowsCsr.incoming_member rows seed vertex edge).mp present, turns.symm⟩
  · rintro ⟨child, same⟩
    exact List.mem_map.mpr ⟨edge, (MoveRowsCsr.incoming_member rows seed vertex edge).mpr child, by rw [same]⟩

def parents (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) (state : State n) : List (State n) :=
  ((incoming rows seed state).filter (allowAt rows allow)).map (TurnSharedGraph.expanded (view rows)).source

theorem parents_transpose (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) (child parent : State n) :
    parent ∈ parents rows seed allow child ↔
      ForwardDfs.Edge (outgoing (TurnSharedGraph.expanded (view rows)) (allowAt rows allow)) parent child := by
  rw [outgoing_correct]
  simp only [parents, List.mem_map, List.mem_filter, incoming_member]
  constructor
  · rintro ⟨edge, ⟨found, permitted⟩, source⟩
    exact ⟨edge, source ▸ (TurnSharedGraph.expanded (view rows)).at_source edge, found, permitted⟩
  · rintro ⟨edge, member, found, permitted⟩
    exact ⟨edge, ⟨found, permitted⟩, (TurnSharedGraph.expanded (view rows)).source_of_mem parent edge member⟩

/-- 順方向も同じ配列内番号jを許可判定へ渡す。平行辺を同じ子番号で潰さない。 -/
theorem forward_meaning (rows : Rows n) (allow : Nat → Nat → Bool)
    (a b : Fin n) (turn side : Bool) :
    ForwardDfs.Edge (outgoing (TurnSharedGraph.expanded (view rows)) (allowAt rows allow)) (a, turn) (b, side) ↔
      ∃ move : Fin (rows a).size, (rows a)[move.val]'move.isLt = some b ∧
        side = (!turn) ∧ allow (TurnEncoding.encode (a, turn)).val move.val = true := by
  rw [TurnSharedGraph.forward_meaning]
  constructor
  · rintro ⟨edge, member, child, sides, permitted⟩
    obtain ⟨move, _, same⟩ := List.mem_map.mp member
    subst edge
    exact ⟨move, child, sides, permitted⟩
  · rintro ⟨move, child, sides, permitted⟩
    exact ⟨⟨a, move⟩, edge_at rows a move, child, sides, permitted⟩

def component (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) : State n → Nat :=
  ComponentNumbering.component (vertices n)
    (ForwardDfs.order (vertices n) (vertices n)
      (outgoing (TurnSharedGraph.expanded (view rows)) (allowAt rows allow))) (parents rows seed allow)

theorem component_eq_iff (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) (a b : State n) :
    component rows seed allow a = component rows seed allow b ↔
      ForwardDfs.Mutual (outgoing (TurnSharedGraph.expanded (view rows)) (allowAt rows allow)) a b :=
  KosarajuStep.component_eq_iff_mutual _ (vertices_unique n) (vertices_cover n) _ (vertices_cover n)
    _ _ (parents_transpose rows seed allow) a b

/-- 二状態では一手ごとに手番が反転するので、自己辺フラグは恒偽と同値。 -/
theorem selfLoop_correct (rows : Rows n) (allow : Nat → Nat → Bool) (state : State n) :
    false = true ↔
      ForwardDfs.Edge (outgoing (TurnSharedGraph.expanded (view rows)) (allowAt rows allow)) state state := by
  exact iff_of_false Bool.false_ne_true (TurnSharedGraph.no_expanded_self_edge _ _ state)

def core (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) : List (State n) :=
  CoreEnumeration.core
    (ComponentCycleFlags.keep (vertices n) (component rows seed allow) (fun _ => false)) (vertices n)

/-- 辺IDの所有条件を入力せず、生の番号対の構築から循環頂点の正確性まで導く。 -/
theorem core_correct (rows : Rows n) (seed : Raw) (allow : Nat → Nat → Bool) (state : State n) :
    state ∈ core rows seed allow ↔
      CyclicVertex (relation (TurnSharedGraph.expanded (view rows)) (allowAt rows allow)) state := by
  have actual := KosarajuStep.computed_core_correct _ (vertices_unique n) (vertices_cover n) _ (vertices_cover n)
    _ _ (parents_transpose rows seed allow) _ (selfLoop_correct rows allow) state
  exact actual.trans (SccIndexedView.cyclic_relation _ _ state)

end PetaProof.MoveRowsScc
