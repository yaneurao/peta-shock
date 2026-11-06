import PetaProof.EscapeOptimal

/-! 成分ごとの最短選択を一つの戦略へまとめても、各成分の脱出保証を保つ。 -/
namespace PetaProof.HistoryArena

universe u v
variable {V : Type u} {I : Type v} (A : HistoryArena V)

/-- 目標に着く前の自分の手が同じなら、目標への保証手数も同じになる。 -/
theorem escapeWithin_transfer (target : V → Prop) (first second : A.Strategy)
    (agree : ∀ past vertex, ¬ target vertex → A.owner vertex = A.player →
      first.choose past vertex = second.choose past vertex)
    (past : List V) (n : Nat) (vertex : V)
    (guaranteed : A.escapeWithin target first past n vertex) :
    A.escapeWithin target second past n vertex := by
  induction n generalizing past vertex with
  | zero => exact guaranteed
  | succ n ih =>
    by_cases goal : target vertex
    · exact Or.inl goal
    · right
      have replies := guaranteed.resolve_left goal
      intro child edge follows
      apply ih (past ++ [vertex]) child
      apply replies child edge
      intro own
      exact (follows own).trans (agree past vertex goal own).symm

/-- noneは成分外または終端。そこではfallbackを使い、成分内では対応する戦略を使う。 -/
def partitionStrategy (label : V → Option I) (family : I → A.Strategy)
    (fallback : A.Strategy) : A.Strategy where
  choose := fun past vertex => match label vertex with
    | none => fallback.choose past vertex
    | some key => (family key).choose past vertex
  legal := by
    intro past vertex own
    cases found : label vertex with
    | none => simpa only [found] using fallback.legal past vertex own
    | some key => simpa only [found] using (family key).legal past vertex own

theorem partitionStrategy_choose (label : V → Option I) (family : I → A.Strategy)
    (fallback : A.Strategy) (key : I) (past : List V) (vertex : V)
    (inside : label vertex = some key) :
    (A.partitionStrategy label family fallback).choose past vertex = (family key).choose past vertex := by
  simp only [partitionStrategy, inside]

/-- 一度成分外へ出た後は、別成分の戦略へ切り替わってよい。最初の脱出手数には影響しない。 -/
theorem partitionStrategy_within (label : V → Option I) (family : I → A.Strategy)
    (fallback : A.Strategy) (key : I) (past : List V) (n : Nat) (vertex : V)
    (guaranteed : A.escapeWithin (fun v => label v ≠ some key) (family key) past n vertex) :
    A.escapeWithin (fun v => label v ≠ some key)
      (A.partitionStrategy label family fallback) past n vertex := by
  classical
  apply A.escapeWithin_transfer _ (family key) _ _ past n vertex guaranteed
  intro history state notGoal _
  exact (A.partitionStrategy_choose label family fallback key history state
    (Classical.not_not.mp notGoal)).symm

/-- 各成分の最短候補を現在成分で選び分ければ、全成分について同時に最短選択となる。 -/
theorem partitionStrategy_optimal (label : V → Option I) (family : I → A.Strategy)
    (fallback : A.Strategy) (vertices : List V)
    (optimal : ∀ key, A.EscapeOptimal (fun v => label v ≠ some key) vertices (family key)) :
    ∀ key, A.EscapeOptimal (fun v => label v ≠ some key) vertices
      (A.partitionStrategy label family fallback) := by
  classical
  intro key past vertex reached notGoal own
  rw [A.partitionStrategy_choose label family fallback key past vertex (Classical.not_not.mp notGoal)]
  exact optimal key past vertex reached notGoal own

theorem partitionStrategy_guarantees (label : V → Option I) (family : I → A.Strategy)
    (fallback : A.Strategy) (vertices : List V) (covered : ∀ vertex, vertex ∈ vertices)
    (optimal : ∀ key, A.EscapeOptimal (fun v => label v ≠ some key) vertices (family key))
    (key : I) (past : List V) (n : Nat) (vertex : V)
    (inside : A.escapeLayer (fun v => label v ≠ some key) vertices.length vertex)
    (bound : A.escapeRank (fun v => label v ≠ some key) vertices.length vertex ≤ n) :
    A.escapeWithin (fun v => label v ≠ some key)
      (A.partitionStrategy label family fallback) past n vertex :=
  A.escapeOptimal_guarantees _ vertices covered _
    (A.partitionStrategy_optimal label family fallback vertices optimal key) past n vertex inside bound

/-- 正しい成分別戦略を外部から仮定せず、既証の到達層から構成して合成する。 -/
noncomputable def partitionEscapeStrategy (label : V → Option I) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (fallback : A.Strategy) : A.Strategy :=
  A.partitionStrategy label
    (fun key => A.escapeStrategy (fun v => label v ≠ some key) vertices covered) fallback

theorem partitionEscapeStrategy_optimal (label : V → Option I) (vertices : List V)
    (covered : ∀ vertex, vertex ∈ vertices) (fallback : A.Strategy) :
    ∀ key, A.EscapeOptimal (fun v => label v ≠ some key) vertices
      (A.partitionEscapeStrategy label vertices covered fallback) :=
  A.partitionStrategy_optimal label _ fallback vertices
    (fun key => A.escapeStrategy_optimal (fun v => label v ≠ some key) vertices covered)

end PetaProof.HistoryArena
