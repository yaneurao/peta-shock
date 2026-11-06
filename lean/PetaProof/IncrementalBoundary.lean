import PetaProof.TerminalPlay

/-! 差分領域の構造条件。値の局所方程式を正当性の根拠にはしない。 -/
namespace PetaProof.IncrementalBoundary

universe u
variable {V : Type u}

/-- 旧辺と新辺の和集合を用い、変更元へ到達できる祖先を全て含む。 -/
structure Region (oldEdge newEdge : V → V → Prop) (changed affected : V → Prop) : Prop where
  contains : ∀ vertex, changed vertex → affected vertex
  ancestors : ∀ source child, (oldEdge source child ∨ newEdge source child) →
    affected child → affected source

/-- 経路の存在で影響集合を定義する。実装で全経路を列挙するという意味ではない。 -/
def affectedBy (oldEdge newEdge : V → V → Prop) (changed : V → Prop) (source : V) : Prop :=
  ∃ target, changed target ∧ Nonempty (Walk (fun v w => oldEdge v w ∨ newEdge v w) source target)

def reachabilityRegion (oldEdge newEdge : V → V → Prop) (changed : V → Prop) :
    Region oldEdge newEdge changed (affectedBy oldEdge newEdge changed) where
  contains := fun vertex change => ⟨vertex, change, ⟨.nil vertex⟩⟩
  ancestors := by
    rintro source child edge ⟨target, change, ⟨back⟩⟩
    exact ⟨target, change, ⟨.cons edge back⟩⟩

variable {oldEdge newEdge : V → V → Prop} {changed affected : V → Prop}
variable (region : Region oldEdge newEdge changed affected)
include region

/-- 逆向きに閉じた任意の候補集合は、全ての変更祖先を含む。 -/
theorem affectedBy_least (source : V) (member : affectedBy oldEdge newEdge changed source) : affected source := by
  obtain ⟨target, change, ⟨trace⟩⟩ := member
  have atEnd := region.contains target change
  induction trace with
  | nil => exact atEnd
  | cons edge _ ih => exact region.ancestors _ _ edge (ih change atEnd)

theorem outside_successor (source child : V) (outside : ¬ affected source)
    (edge : oldEdge source child ∨ newEdge source child) : ¬ affected child :=
  fun inside => outside (region.ancestors source child edge inside)

/-- 外へ出た後は、旧新いずれの辺を混ぜても影響領域へ戻れない。 -/
theorem outside_walk {source child : V}
    (trace : Walk (fun v w => oldEdge v w ∨ newEdge v w) source child)
    (outside : ¬ affected source) : ¬ affected child := by
  induction trace with
  | nil => exact outside
  | cons edge _ ih => exact ih (outside_successor region _ _ outside edge)

theorem changed_unreachable {source child : V}
    (trace : Walk (fun v w => oldEdge v w ∨ newEdge v w) source child)
    (outside : ¬ affected source) : ¬ changed child :=
  fun change => outside_walk region trace outside (region.contains child change)

/-- 境界出口から中へ帰る経路は存在しないため、境界を跨ぐ反復区間も存在しない。 -/
theorem no_return (source exit : V) (inside : affected source) (outside : ¬ affected exit)
    (back : Walk (fun v w => oldEdge v w ∨ newEdge v w) exit source) : False :=
  outside_walk region back outside inside

/-- 外側で全手が不変なら、履歴による選択の合法性も同じ。辺削除にも双方向条件を課す。 -/
theorem outside_legal_iff (oldGame newGame : ThresholdGame V)
    (unchanged : ∀ vertex, ¬ changed vertex → ∀ move, oldGame.legal vertex move ↔ newGame.legal vertex move)
    (vertex : V) (outside : ¬ affected vertex) (move : Move V) :
    oldGame.legal vertex move ↔ newGame.legal vertex move :=
  unchanged vertex (fun change => outside (region.contains vertex change)) move

end PetaProof.IncrementalBoundary
