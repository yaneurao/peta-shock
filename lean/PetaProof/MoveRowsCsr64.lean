import PetaProof.CsrConstruct64

/-! UInt32対を格納し、UInt64 offset/cursorで構築した逆辺を両DFSへ接続する。 -/
namespace PetaProof.MoveRowsCsr64

open MoveRows32
variable {n : Nat}

def CapacityFits (book : Book n) : Prop := (MoveRowsCsr32.edges book).length < UInt64.size

private theorem flatMap_bound {V F : Type} (vertices : List V) (outgoing : V → List F) (limit : Nat)
    (bounded : ∀ vertex ∈ vertices, (outgoing vertex).length ≤ limit) :
    (vertices.flatMap outgoing).length ≤ vertices.length * limit := by
  induction vertices with
  | nil => simp
  | cons vertex rest ih =>
    have head := bounded vertex (by simp)
    have tail := ih (fun vertex member => bounded vertex (by simp [member]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- 局面数と各行長の既存上限だけで、総辺数が64-bit範囲に入ることを導く。 -/
theorem capacityFits_of_bounds (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book) : CapacityFits book := by
  let view := IndexedMoveRows.view (rows book)
  have all_bound : ((List.finRange n).flatMap view.outgoing).length ≤ n * UInt32.size := by
    have bound := flatMap_bound (List.finRange n) view.outgoing UInt32.size (fun vertex _ => by
      rw [IndexedMoveRows.degree, row_size]
      exact Nat.le_of_lt (counts vertex))
    simpa only [List.length_finRange] using bound
  have filtered : (MoveRowsCsr32.edges book).length ≤ ((List.finRange n).flatMap view.outgoing).length := by
    simp only [MoveRowsCsr32.edges, MoveRowsCsr.edges, List.length_map, SccCsrView.edges, SccIndexedView.allInternal]
    exact List.length_filter_le _ _
  have bound := Nat.le_trans filtered all_bound
  change n < 4294967295 / 2 at fits
  change (MoveRowsCsr32.edges book).length ≤ n * 4294967296 at bound
  change (MoveRowsCsr32.edges book).length < 18446744073709551616
  omega

def build (book : Book n) (seed : MoveRowsCsr32.Pair) : Csr64.Built MoveRowsCsr32.Pair :=
  Csr64.build n seed (MoveRowsCsr32.target book) (MoveRowsCsr32.edges book)

theorem build_refines (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) :
    Csr64.unpackBuilt (build book seed) = MoveRowsCsr32.build book seed :=
  Csr64.build_refines n seed _ _ (MoveRowsCsr32.bounded fits book counts) capacity

def incoming (book : Book n) (seed : MoveRowsCsr32.Pair) (vertex : Fin n) : List MoveRowsCsr32.Pair :=
  Csr64.row n seed (MoveRowsCsr32.target book) (MoveRowsCsr32.edges book) vertex.val

theorem incoming_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) (vertex : Fin n) :
    incoming book seed vertex = MoveRowsCsr32.incoming book seed vertex :=
  Csr64.row_refines n seed _ _ (MoveRowsCsr32.bounded fits book counts) capacity vertex.val vertex.isLt

def callbacks (book : Book n) (seed : MoveRowsCsr32.Pair) (state : TurnEncoding.State n) : List MoveRowsCsr32.Pair :=
  (incoming book seed state.1).map (fun edge =>
    (TurnEncoding32.flipIndex edge.1 (TurnEncoding32.encode state), edge.2))

theorem callbacks_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) (state : TurnEncoding.State n) :
    callbacks book seed state = MoveRowsCsr32.callbacks book seed state := by
  rw [callbacks, incoming_exact fits book counts capacity]
  rfl

def parents (book : Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    List (TurnEncoding.State n) :=
  (((callbacks book seed state).filter (fun edge => allow edge.1 edge.2)).map Prod.fst).filterMap (TurnEncoding32.decode n)

theorem parents_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    parents book seed allow state = MoveRowsCsr32.parents book seed allow state := by
  rw [parents, callbacks_exact fits book counts capacity]
  rfl

def component (book : Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) : TurnEncoding.State n → Nat :=
  ComponentNumbering.component (TurnEncoding.vertices n)
    (ForwardDfs.order (TurnEncoding.vertices n) (TurnEncoding.vertices n)
      (SccIndexedView.outgoing (TurnSharedGraph.expanded (IndexedMoveRows.view (rows book)))
        (MoveRowsScc.allowAt (rows book) (allowNat allow)))) (parents book seed allow)

theorem component_exact (fits : TurnEncoding32.Fits n) (book : Book n) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) :
    component book seed allow = MoveRowsCsr32.component book seed allow := by
  have same : parents book seed allow = MoveRowsCsr32.parents book seed allow := by
    funext state
    exact parents_exact fits book counts capacity seed allow state
  simp only [component, MoveRowsCsr32.component, same]

def core (book : Book n) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) : List (TurnEncoding.State n) :=
  CoreEnumeration.core (ComponentCycleFlags.keep (TurnEncoding.vertices n) (component book seed allow)
    (fun _ => false)) (TurnEncoding.vertices n)

theorem core_correct (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book) (counts : CountsFit book)
    (capacity : CapacityFits book) (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    state ∈ core book seed allow ↔ CyclicVertex (MoveRows32.relation book allow) state := by
  have same : core book seed allow = MoveRowsCsr32.core book seed allow := by
    simp only [core, component_exact fits book counts capacity, MoveRowsCsr32.core]
  rw [same]
  exact MoveRowsCsr32.core_correct fits book valid counts seed allow state

theorem core_correct_bounded (fits : TurnEncoding32.Fits n) (book : Book n) (valid : Valid book) (counts : CountsFit book)
    (seed : MoveRowsCsr32.Pair) (allow : UInt32 → UInt32 → Bool) (state : TurnEncoding.State n) :
    state ∈ core book seed allow ↔ CyclicVertex (MoveRows32.relation book allow) state :=
  core_correct fits book valid counts (capacityFits_of_bounds fits book counts) seed allow state

end PetaProof.MoveRowsCsr64
