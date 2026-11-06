import PetaProof.SelectedDepthRun
import PetaProof.DepthWriter

/-! 計算したdepthを最終候補検査と保存規則に接続する。
以前のselectedDepth前提を、全走査の出力の正しさから導く。 -/
namespace PetaProof.SelectedDepth

universe u v
variable {V : Type u} {E : Type v}

/-- 保存する手のdepth。leaf手は0、内部手は子のdepthに1を加えて飽和。 -/
def edgeDepth (next : V → Option V) (cap : Nat) : Option V → Nat
  | none => 0
  | some child => bump cap (computed next cap child)

theorem selected_edge_depth (next : V → Option V) (cap : Nat) (vertex : V) :
    edgeDepth next cap (next vertex) = computed next cap vertex := by
  rw [equation next cap vertex]
  cases next vertex <;> rfl

theorem writer_selected_depth (I : DepthWriter.Input V E) (next : V → Option V) (cap : Nat)
    (target : E → Option V) (choice : ∀ vertex, target (I.selected vertex) = next vertex)
    (depthSpec : ∀ edge, I.depth edge = edgeDepth next cap (target edge)) (vertex : V) :
    I.depth (I.selected vertex) = computed next cap vertex := by
  rw [depthSpec, choice]
  exact selected_edge_depth next cap vertex

/-- 正しい親depthを仮定せず、再構築実行から選択手との一致を得る。 -/
theorem reconstructed_selected_depth [DecidableEq V] (I : DepthWriter.Input V E)
    (next : V → Option V) (cap : Nat) (vertices : List V) (covered : ∀ x, x ∈ vertices)
    (target : E → Option V) (choice : ∀ vertex, target (I.selected vertex) = next vertex)
    (depthSpec : ∀ edge, I.depth edge = edgeDepth next cap (target edge))
    (table : V → Nat) (found : reconstruct next cap vertices = some table) (vertex : V) :
    I.depth (I.selected vertex) = table vertex := by
  have exactRun := reconstruct_exact next cap vertices covered
  rw [found] at exactRun
  have same : table = computed next cap := Option.some.inj exactRun
  rw [same]
  exact writer_selected_depth I next cap target choice depthSpec vertex

/-- 再構築した親depthを用いる最終検査と、保存最大手の条件が一致する。 -/
theorem reconstructed_maximum_iff_checked [DecidableEq V] [DecidableEq E]
    (I : DepthWriter.Input V E) (next : V → Option V) (cap : Nat)
    (vertices : List V) (covered : ∀ x, x ∈ vertices)
    (target : E → Option V) (choice : ∀ vertex, target (I.selected vertex) = next vertex)
    (depthSpec : ∀ edge, I.depth edge = edgeDepth next cap (target edge))
    (table : V → Nat) (found : reconstruct next cap vertices = some table)
    (shrink : Bool) (vertex : V) (edge : E) (member : edge ∈ I.outputRows shrink vertex) :
    (∀ other ∈ I.outputRows shrink vertex, I.saved vertex other ≤ I.saved vertex edge) ↔
      if I.keepTies vertex = true then
        I.raw vertex edge = I.best vertex ∧ I.depth edge = table vertex
      else edge = I.selected vertex := by
  rw [I.output_maximum_iff shrink vertex edge member]
  exact I.allowed_iff_checked vertex edge (table vertex)
    (reconstructed_selected_depth I next cap vertices covered target choice depthSpec table found vertex)

/-- 保存側で用いるdepthを、実際に再構築した子の表から組み立てる。 -/
def withTableDepth (I : DepthWriter.Input V E) (cap : Nat)
    (target : E → Option V) (table : V → Nat) : DepthWriter.Input V E :=
  { I with depth := fun edge => match target edge with
      | none => 0
      | some child => bump cap (table child) }

/-- 正しいdepth表やdepthSpecを入力せず、実行出力から必要な一致を導く。 -/
theorem actual_selected_depth [DecidableEq V] (I : DepthWriter.Input V E)
    (next : V → Option V) (cap : Nat) (vertices : List V) (covered : ∀ x, x ∈ vertices)
    (target : E → Option V) (choice : ∀ vertex, target (I.selected vertex) = next vertex)
    (table : V → Nat) (found : reconstruct next cap vertices = some table) (vertex : V) :
    (withTableDepth I cap target table).depth (I.selected vertex) = table vertex := by
  change (match target (I.selected vertex) with
    | none => 0
    | some child => bump cap (table child)) = table vertex
  rw [choice]
  exact (reconstructed_equation next cap vertices covered table found vertex).symm

/-- 再構築と保存を合成した入口。以前のselectedDepth前提とdepthSpec前提の双方を除く。 -/
theorem actual_maximum_iff_checked [DecidableEq V] [DecidableEq E]
    (I : DepthWriter.Input V E) (next : V → Option V) (cap : Nat)
    (vertices : List V) (covered : ∀ x, x ∈ vertices)
    (target : E → Option V) (choice : ∀ vertex, target (I.selected vertex) = next vertex)
    (table : V → Nat) (found : reconstruct next cap vertices = some table)
    (shrink : Bool) (vertex : V) (edge : E)
    (member : edge ∈ (withTableDepth I cap target table).outputRows shrink vertex) :
    (∀ other ∈ (withTableDepth I cap target table).outputRows shrink vertex,
      (withTableDepth I cap target table).saved vertex other ≤
        (withTableDepth I cap target table).saved vertex edge) ↔
      if I.keepTies vertex = true then
        I.raw vertex edge = I.best vertex ∧
          (withTableDepth I cap target table).depth edge = table vertex
      else edge = I.selected vertex := by
  rw [(withTableDepth I cap target table).output_maximum_iff shrink vertex edge member]
  exact (withTableDepth I cap target table).allowed_iff_checked vertex edge (table vertex)
    (actual_selected_depth I next cap vertices covered target choice table found vertex)

end PetaProof.SelectedDepth
