import PetaProof.CsrFill

/-!
Nat番地のCSRから読み出した逆辺列を、辺ID付きView・SCC・循環coreへ接続する。
頂点番号はFin nで与える。先後二状態化やC++機械整数との対応は含めない。
-/
namespace PetaProof.SccCsrView

universe u
variable {n : Nat} {E : Type u}
open SccIndexedView

def edges (view : View (Fin n) E) : List E := allInternal view (List.finRange n)
def target (view : View (Fin n) E) (edge : E) : Nat := (SccIndexedView.target view edge).val

def incoming (view : View (Fin n) E) (vertex : Fin n) : List E :=
  Csr.row (target view) (edges view) vertex.val

/-- CSRの区間読出しは論理バケットと、順序・重複回数を含めて一致する。 -/
theorem incoming_exact (view : View (Fin n) E) (vertex : Fin n) :
    incoming view vertex = SccIndexedView.incoming view (List.finRange n) vertex := by
  rw [incoming, Csr.row_exact, SccIndexedView.incoming_spec]
  apply List.filter_congr
  intro edge _
  apply Bool.eq_iff_iff.mpr
  simp only [target, beq_iff_eq, Fin.val_inj]

theorem capacity_exact (view : View (Fin n) E) :
    Csr.offset (Csr.degrees (target view) (edges view)) n = (edges view).length :=
  Csr.total_capacity _ _ n (fun edge _ => (SccIndexedView.target view edge).isLt)

theorem writes_within (view : View (Fin n) E) :
    Csr.WritesWithin (edges view).length (target view) (edges view)
      (Csr.initial (Csr.degrees (target view) (edges view))) :=
  Csr.built_writes_within _ _ n (fun edge _ => (SccIndexedView.target view edge).isLt)

/-- 各区間の全読出し番地も確保容量未満になる。 -/
theorem read_within (view : View (Fin n) E) (vertex : Fin n) (index : Nat)
    (inside : index < Csr.degrees (target view) (edges view) vertex.val) :
    Csr.offset (Csr.degrees (target view) (edges view)) vertex.val + index < (edges view).length := by
  have ordered := Csr.offset_mono (Csr.degrees (target view) (edges view)) (vertex.val + 1) n (by omega)
  have capacity := capacity_exact view
  simp only [Csr.offset] at ordered
  omega

def parents (view : View (Fin n) E) (allow : E → Bool) (vertex : Fin n) : List (Fin n) :=
  ((incoming view vertex).filter allow).map view.source

theorem parents_exact (view : View (Fin n) E) (allow : E → Bool) :
    parents view allow = SccIndexedView.parents view (List.finRange n) allow := by
  funext vertex
  simp only [parents, SccIndexedView.parents, incoming_exact]

def selfLoop (view : View (Fin n) E) (allow : E → Bool) (vertex : Fin n) : Bool :=
  (incoming view vertex).any (fun edge => decide (view.source edge = vertex) && allow edge)

theorem selfLoop_exact (view : View (Fin n) E) (allow : E → Bool) :
    selfLoop view allow = SccIndexedView.selfLoop view (List.finRange n) allow := by
  funext vertex
  simp only [selfLoop, SccIndexedView.selfLoop, incoming_exact]

def component (view : View (Fin n) E) (allow : E → Bool) : Fin n → Nat :=
  ComponentNumbering.component (List.finRange n)
    (ForwardDfs.order (List.finRange n) (List.finRange n) (outgoing view allow)) (parents view allow)

theorem component_exact (view : View (Fin n) E) (allow : E → Bool) :
    component view allow = SccIndexedView.component view (List.finRange n) (List.finRange n) allow := by
  simp only [component, SccIndexedView.component, parents_exact]

theorem component_eq_iff (view : View (Fin n) E) (allow : E → Bool) (a b : Fin n) :
    component view allow a = component view allow b ↔ ForwardDfs.Mutual (outgoing view allow) a b := by
  rw [component_exact]
  exact SccIndexedView.component_eq_iff view _ (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) _ (CoreEnumeration.finRange_covers n) allow a b

def core (view : View (Fin n) E) (allow : E → Bool) : List (Fin n) :=
  CoreEnumeration.core (ComponentCycleFlags.keep (List.finRange n) (component view allow) (selfLoop view allow)) (List.finRange n)

theorem core_exact (view : View (Fin n) E) (allow : E → Bool) :
    core view allow = SccIndexedView.core view (List.finRange n) (List.finRange n) allow := by
  simp only [core, SccIndexedView.core, component_exact, selfLoop_exact]

/-- 転置一致を仮定せず、CSR格納と読出しから元の許可辺上の循環頂点を得る。 -/
theorem core_correct (view : View (Fin n) E) (allow : E → Bool) (vertex : Fin n) :
    vertex ∈ core view allow ↔ CyclicVertex (relation view allow) vertex := by
  rw [core_exact]
  exact SccIndexedView.core_relation_correct view _ (CoreEnumeration.finRange_unique n)
    (CoreEnumeration.finRange_covers n) _ (CoreEnumeration.finRange_covers n) allow vertex

end PetaProof.SccCsrView
