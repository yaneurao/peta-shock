import PetaProof.CsrPayloadArray
import PetaProof.SccCsrView

/-!
辺IDを直接格納する有限Arrayを経由した逆辺・SCC・循環core。
offset配列の生成は再帰的な累積和からのofFnであり、インプレースprefix loopではない。
-/
namespace PetaProof.SccArrayView

universe u
variable {n : Nat} {E : Type u}
open SccIndexedView

def incoming (view : View (Fin n) E) (seed : E) (vertex : Fin n) : List E :=
  CsrPayloadArray.row n seed (SccCsrView.target view) (SccCsrView.edges view) vertex.val

theorem incoming_exact (view : View (Fin n) E) (seed : E) (vertex : Fin n) :
    incoming view seed vertex = SccCsrView.incoming view vertex := by
  have bounded : ∀ edge ∈ SccCsrView.edges view, SccCsrView.target view edge < n :=
    fun edge _ => (SccIndexedView.target view edge).isLt
  rw [incoming, CsrPayloadArray.row_exact n seed (SccCsrView.target view) (SccCsrView.edges view) bounded vertex.val vertex.isLt,
    SccCsrView.incoming, Csr.row_exact]

theorem writes_safe (view : View (Fin n) E) (seed : E) :
    CsrPayloadArray.AllSafe (SccCsrView.target view) (SccCsrView.edges view)
      (CsrPayloadArray.initial n (SccCsrView.edges view).length
        (Csr.degrees (SccCsrView.target view) (SccCsrView.edges view)) seed) :=
  CsrPayloadArray.built_safe n seed _ _ (fun edge _ => (SccIndexedView.target view edge).isLt)

def parents (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) : List (Fin n) :=
  ((incoming view seed vertex).filter allow).map view.source

theorem parents_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    parents view seed allow = SccCsrView.parents view allow := by
  funext vertex
  simp only [parents, SccCsrView.parents, incoming_exact]

def selfLoop (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) : Bool :=
  (incoming view seed vertex).any (fun edge => decide (view.source edge = vertex) && allow edge)

theorem selfLoop_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    selfLoop view seed allow = SccCsrView.selfLoop view allow := by
  funext vertex
  simp only [selfLoop, SccCsrView.selfLoop, incoming_exact]

def component (view : View (Fin n) E) (seed : E) (allow : E → Bool) : Fin n → Nat :=
  ComponentNumbering.component (List.finRange n)
    (ForwardDfs.order (List.finRange n) (List.finRange n) (outgoing view allow)) (parents view seed allow)

theorem component_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    component view seed allow = SccCsrView.component view allow := by
  simp only [component, SccCsrView.component, parents_exact]

theorem component_eq_iff (view : View (Fin n) E) (seed : E) (allow : E → Bool) (a b : Fin n) :
    component view seed allow a = component view seed allow b ↔ ForwardDfs.Mutual (outgoing view allow) a b := by
  rw [component_exact]
  exact SccCsrView.component_eq_iff view allow a b

def core (view : View (Fin n) E) (seed : E) (allow : E → Bool) : List (Fin n) :=
  CoreEnumeration.core
    (ComponentCycleFlags.keep (List.finRange n) (component view seed allow) (selfLoop view seed allow)) (List.finRange n)

theorem core_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    core view seed allow = SccCsrView.core view allow := by
  simp only [core, SccCsrView.core, component_exact, selfLoop_exact]

/-- 有限配列で作った逆辺列を使っても、元の許可辺上の循環頂点を正確に得る。 -/
theorem core_correct (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) :
    vertex ∈ core view seed allow ↔ CyclicVertex (relation view allow) vertex := by
  rw [core_exact]
  exact SccCsrView.core_correct view allow vertex

end PetaProof.SccArrayView
