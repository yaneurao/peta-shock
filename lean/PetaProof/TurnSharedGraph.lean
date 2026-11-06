import PetaProof.TurnEncoding
import PetaProof.SccConstructedView

/-!
基礎局面ごとのCSRを共有し、callback時に反転した親手番を付ける。
展開した二状態グラフの逆辺を別に構築する必要がないことを示す。
-/
namespace PetaProof.TurnSharedGraph

universe u
variable {n : Nat} {E : Type u}
open SccIndexedView
open TurnEncoding (State)

theorem flip_eq_iff (a b : Bool) : ((!a) = b) ↔ a = (!b) := by cases a <;> cases b <;> decide

/-- 証明用の展開ビュー。辺IDへ親の手番を付けるが、本番の辺配列を複製する変更ではない。 -/
def expanded (view : View (Fin n) E) : View (State n) (E × Bool) where
  outgoing := fun state => (view.outgoing state.1).map (fun edge => (edge, state.2))
  source := fun edge => (view.source edge.1, edge.2)
  child := fun edge => (view.child edge.1).map (fun vertex => (vertex, !edge.2))
  at_source := by
    rintro ⟨edge, turn⟩
    exact List.mem_map.mpr ⟨edge, view.at_source edge, rfl⟩
  source_of_mem := by
    rintro ⟨vertex, turn⟩ ⟨edge, side⟩ member
    obtain ⟨original, present, pair⟩ := List.mem_map.mp member
    have same := congrArg Prod.fst pair
    have turns := congrArg Prod.snd pair
    dsimp only at same turns
    subst original
    subst side
    change (view.source edge, turn) = (vertex, turn)
    rw [view.source_of_mem vertex edge present]

theorem child_correct (view : View (Fin n) E) (edge : E) (turn : Bool) (vertex : Fin n) (side : Bool) :
    (expanded view).child (edge, turn) = some (vertex, side) ↔
      view.child edge = some vertex ∧ turn = (!side) := by
  cases found : view.child edge <;> simp [expanded, found, flip_eq_iff]

/-- 順方向の許可判定は、指した側の手番と元の辺IDについて行う。 -/
theorem forward_meaning (view : View (Fin n) E) (allow : E × Bool → Bool)
    (a b : Fin n) (turn side : Bool) :
    ForwardDfs.Edge (outgoing (expanded view) allow) (a, turn) (b, side) ↔
      ∃ edge, edge ∈ view.outgoing a ∧ view.child edge = some b ∧ side = (!turn) ∧ allow (edge, turn) = true := by
  rw [outgoing_correct]
  constructor
  · rintro ⟨⟨edge, original_turn⟩, member, child, permitted⟩
    obtain ⟨original, present, pair⟩ := List.mem_map.mp member
    have same := congrArg Prod.fst pair
    have turns := congrArg Prod.snd pair
    dsimp only at same turns
    subst original
    subst original_turn
    have reached := (child_correct view edge turn b side).mp child
    exact ⟨edge, present, reached.1, ((flip_eq_iff turn side).mpr reached.2).symm, permitted⟩
  · rintro ⟨edge, member, child, sides, permitted⟩
    refine ⟨(edge, turn), List.mem_map.mpr ⟨edge, member, rfl⟩, ?_, permitted⟩
    exact (child_correct view edge turn b side).mpr ⟨child, by rw [sides]; simp⟩

def baseIncoming (view : View (Fin n) E) (seed : E) (vertex : Fin n) : List E :=
  SccConstructedView.incoming view seed vertex

theorem baseIncoming_member (view : View (Fin n) E) (seed : E) (vertex : Fin n) (edge : E) :
    edge ∈ baseIncoming view seed vertex ↔ view.child edge = some vertex := by
  rw [baseIncoming, SccConstructedView.incoming_exact, SccArrayView.incoming_exact,
    SccCsrView.incoming_exact, SccIndexedView.incoming_member view _ (CoreEnumeration.finRange_covers n)]

/-- 基礎CSRの同じ区間を読み、親の手番だけをcallback時に補う。 -/
def incoming (view : View (Fin n) E) (seed : E) (state : State n) : List (E × Bool) :=
  (baseIncoming view seed state.1).map (fun edge => (edge, !state.2))

theorem incoming_member (view : View (Fin n) E) (seed : E) (state : State n) (edge : E × Bool) :
    edge ∈ incoming view seed state ↔ (expanded view).child edge = some state := by
  rcases state with ⟨vertex, turn⟩
  rcases edge with ⟨edge, side⟩
  rw [child_correct]
  constructor
  · rintro member
    obtain ⟨original, present, pair⟩ := List.mem_map.mp member
    have same := congrArg Prod.fst pair
    have turns := congrArg Prod.snd pair
    dsimp only at same turns
    subst original
    exact ⟨(baseIncoming_member view seed vertex edge).mp present, turns.symm⟩
  · rintro ⟨child, same⟩
    exact List.mem_map.mpr ⟨edge, (baseIncoming_member view seed vertex edge).mpr child, by rw [same]⟩

def parents (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) : List (State n) :=
  ((incoming view seed state).filter allow).map (expanded view).source

/-- 基礎CSRの共有から、展開グラフに必要な転置一致が得られる。 -/
theorem parents_transpose (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (child parent : State n) :
    parent ∈ parents view seed allow child ↔ ForwardDfs.Edge (outgoing (expanded view) allow) parent child := by
  rw [outgoing_correct]
  simp only [parents, List.mem_map, List.mem_filter, incoming_member]
  constructor
  · rintro ⟨edge, ⟨found, permitted⟩, source⟩
    exact ⟨edge, source ▸ (expanded view).at_source edge, found, permitted⟩
  · rintro ⟨edge, member, found, permitted⟩
    exact ⟨edge, ⟨found, permitted⟩, (expanded view).source_of_mem parent edge member⟩

def selfLoop (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) : Bool :=
  (incoming view seed state).any (fun edge => decide ((expanded view).source edge = state) && allow edge)

theorem selfLoop_correct (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) :
    selfLoop view seed allow state = true ↔ ForwardDfs.Edge (outgoing (expanded view) allow) state state := by
  rw [outgoing_correct]
  simp only [selfLoop, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, incoming_member]
  constructor
  · rintro ⟨edge, found, source, permitted⟩
    exact ⟨edge, source ▸ (expanded view).at_source edge, found, permitted⟩
  · rintro ⟨edge, member, found, permitted⟩
    exact ⟨edge, found, (expanded view).source_of_mem state edge member, permitted⟩

/-- 毎手手番が変わるので、基礎グラフに自己辺があっても二状態グラフには自己辺がない。 -/
theorem no_expanded_self_edge (view : View (Fin n) E) (allow : E × Bool → Bool) (state : State n) :
    ¬ForwardDfs.Edge (outgoing (expanded view) allow) state state := by
  rcases state with ⟨vertex, turn⟩
  rw [forward_meaning]
  rintro ⟨edge, member, child, impossible, permitted⟩
  cases turn <;> cases impossible

theorem selfLoop_false (view : View (Fin n) E) (seed : E) (allow : E × Bool → Bool) (state : State n) :
    selfLoop view seed allow state = false := by
  have not_true : selfLoop view seed allow state ≠ true :=
    fun found => no_expanded_self_edge view allow state ((selfLoop_correct view seed allow state).mp found)
  cases flag : selfLoop view seed allow state <;> simp_all

end PetaProof.TurnSharedGraph
