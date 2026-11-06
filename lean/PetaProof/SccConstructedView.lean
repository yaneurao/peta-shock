import PetaProof.CsrConstructArray
import PetaProof.SccArrayView

/-!
カウント・累積和・確保・格納を全て配列上で行った逆辺を、SCC/coreへ接続する。
自然数を要素とするLean Arrayのモデルであり、機械整数の精密化は含まない。
-/
namespace PetaProof.SccConstructedView

universe u
variable {n : Nat} {E : Type u}
open SccIndexedView

def incoming (view : View (Fin n) E) (seed : E) (vertex : Fin n) : List E :=
  CsrConstructArray.row n seed (SccCsrView.target view) (SccCsrView.edges view) vertex.val

theorem incoming_exact (view : View (Fin n) E) (seed : E) (vertex : Fin n) :
    incoming view seed vertex = SccArrayView.incoming view seed vertex := by
  have bounded : ∀ edge ∈ SccCsrView.edges view, SccCsrView.target view edge < n :=
    fun edge _ => (SccIndexedView.target view edge).isLt
  exact CsrConstructArray.row_eq_reference n seed _ _ bounded vertex.val

theorem construction_safe (view : View (Fin n) E) (seed : E) :
    CsrConstructArray.Safe n seed (SccCsrView.target view) (SccCsrView.edges view) :=
  CsrConstructArray.build_safe n seed _ _ (fun edge _ => (SccIndexedView.target view edge).isLt)

def parents (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) : List (Fin n) :=
  ((incoming view seed vertex).filter allow).map view.source

theorem parents_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    parents view seed allow = SccArrayView.parents view seed allow := by
  funext vertex
  simp only [parents, SccArrayView.parents, incoming_exact]

def selfLoop (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) : Bool :=
  (incoming view seed vertex).any (fun edge => decide (view.source edge = vertex) && allow edge)

theorem selfLoop_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    selfLoop view seed allow = SccArrayView.selfLoop view seed allow := by
  funext vertex
  simp only [selfLoop, SccArrayView.selfLoop, incoming_exact]

def component (view : View (Fin n) E) (seed : E) (allow : E → Bool) : Fin n → Nat :=
  ComponentNumbering.component (List.finRange n)
    (ForwardDfs.order (List.finRange n) (List.finRange n) (outgoing view allow)) (parents view seed allow)

theorem component_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    component view seed allow = SccArrayView.component view seed allow := by
  simp only [component, SccArrayView.component, parents_exact]

theorem component_eq_iff (view : View (Fin n) E) (seed : E) (allow : E → Bool) (a b : Fin n) :
    component view seed allow a = component view seed allow b ↔ ForwardDfs.Mutual (outgoing view allow) a b := by
  rw [component_exact]
  exact SccArrayView.component_eq_iff view seed allow a b

def core (view : View (Fin n) E) (seed : E) (allow : E → Bool) : List (Fin n) :=
  CoreEnumeration.core
    (ComponentCycleFlags.keep (List.finRange n) (component view seed allow) (selfLoop view seed allow)) (List.finRange n)

theorem core_exact (view : View (Fin n) E) (seed : E) (allow : E → Bool) :
    core view seed allow = SccArrayView.core view seed allow := by
  simp only [core, SccArrayView.core, component_exact, selfLoop_exact]

/-- 構築したoffsetや逆辺の正しさを仮定せず、元の許可辺上の循環性を導く。 -/
theorem core_correct (view : View (Fin n) E) (seed : E) (allow : E → Bool) (vertex : Fin n) :
    vertex ∈ core view seed allow ↔ CyclicVertex (relation view allow) vertex := by
  rw [core_exact]
  exact SccArrayView.core_correct view seed allow vertex

end PetaProof.SccConstructedView
