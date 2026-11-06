import PetaProof

/-! 距離最適化の技術補足資料に対応する入口。主論文の主張とは区別する。 -/

-- A1: 到達層による最短保証。
#check PetaProof.HistoryArena.escape_minimax
#check PetaProof.HistoryArena.EscapeInput.minimizing_choices_optimal
-- A2: 固定した安全候補内の距離と主値保証。
#check PetaProof.ThresholdGame.SafeEscapeInput.distance_and_score
-- A3: 独立距離検査の必要十分性。
#check PetaProof.HistoryArena.EscapeInput.tableCheck_iff_exact
-- A4: 実FIFOのnone出力の健全性。
#check PetaProof.EscapePropagation.State.runLabels_none_spoiler
-- A5: 実FIFO全出力の正確さ、受理を仮定しない受理、候補選択。
#check PetaProof.EscapePropagation.State.runLabels_exact
#check PetaProof.EscapePropagation.State.runLabels_checked
#check PetaProof.EscapePropagation.State.runLabels_minimax
#check PetaProof.EscapePropagation.State.minimizing_choices_optimal

-- A6: 成分別の最短戦略を同時に使い、元の手へ戻しても脱出と評価値の保証を保つ。
#check PetaProof.HistoryArena.escapeWithin_transfer
#check PetaProof.HistoryArena.partitionStrategy_choose
#check PetaProof.HistoryArena.partitionStrategy_within
#check PetaProof.HistoryArena.partitionStrategy_optimal
#check PetaProof.HistoryArena.partitionStrategy_guarantees
#check PetaProof.ThresholdGame.SafeEscapeInput.partition_target
#check PetaProof.ThresholdGame.SafeEscapeInput.partitionPlan_safe
#check PetaProof.ThresholdGame.SafeEscapeInput.partition_distance_and_score
#check PetaProof.HistoryArena.partitionEscapeStrategy_optimal
#check PetaProof.ThresholdGame.SafeEscapeInput.shortestPartitionPlan_safe
#check PetaProof.ThresholdGame.SafeEscapeInput.shortestPartitionPlan_distance_and_score

-- A7: 符号別のmin/maxを計算前に固定した有限・無限rankとFIFOとの一致。
#check PetaProof.SignedRankGraph.Input.rank_bound
#check PetaProof.SignedRankGraph.Input.fifo_rank
#check PetaProof.SignedRankGraph.Input.rank_table
#check PetaProof.SignedRankGraph.Input.preferred_rank
#check PetaProof.SignedRankGraph.Input.preferred_finite
#check PetaProof.SignedRankGraph.Input.preferred_infinite
-- A8: 無限rankの順序、符号別の候補選別と安全性優先。
#check PetaProof.PathRank.code_le_iff
#check PetaProof.PathRank.preferred_exists
#check PetaProof.PathRank.preferred_direction
#check PetaProof.PathRank.negative_prefers_infinite
#check PetaProof.ThresholdGame.SignedRank.Input.negative_plan_infinite
#check PetaProof.ThresholdGame.SignedRank.Input.plan_direction
-- A9: 元の出辺から安全なbestを残し、入力からrank計画の値を保証する。
#check PetaProof.ThresholdGame.SignedRank.ofIndexed
#check PetaProof.ThresholdGame.SignedRank.Input.plan_admissible
#check PetaProof.ThresholdGame.SignedRank.Input.plan_lower
#check PetaProof.ThresholdGame.QueueContext.generated_signed_rank_lower
#check PetaProof.PathRank.no_mate_loss
-- A10: 有限rankの脱出上界と、実際の選択に両立する無限の延長機会。
#check PetaProof.ThresholdGame.SignedRank.Input.plan_rank
#check PetaProof.ThresholdGame.SignedRank.Input.plan_within
#check PetaProof.ThresholdGame.SignedRank.Input.plan_distance_and_score
#check PetaProof.ThresholdGame.SignedRank.Input.prolong_legal
#check PetaProof.ThresholdGame.SignedRank.Input.plan_infinite_opportunity
-- A11: 保存最大手の特徴付けと、元の全出辺の出力選択までの下限保証。
#check PetaProof.PathRank.encoded_maximum_iff
#check PetaProof.PathRank.encoded_plan_lower
#check PetaProof.ThresholdGame.SignedRank.Input.encoded_plan_lower
#check PetaProof.ThresholdGame.QueueContext.generated_signed_rank_output_lower

namespace DistanceReviewExamples

/-- 真の目標が空なら、片方向の「網羅」は余分な目標を排除しない。 -/
theorem one_way_coverage_not_exact :
    (∀ vertex : PetaProof.EscapeExamples.Node, False → vertex ∈ [PetaProof.EscapeExamples.Node.exit]) ∧
    ¬ (∀ vertex : PetaProof.EscapeExamples.Node, vertex ∈ [PetaProof.EscapeExamples.Node.exit] → False) := by
  constructor
  · intro vertex impossible
    cases impossible
  · intro extra
    exact extra .exit (by simp)

/-- 非目標exitを誤って目標一覧へ入れると、0を返すが真の全none表とは一致しない。 -/
theorem false_goal_changes_output :
    PetaProof.EscapePropagation.State.runLabels PetaProof.EscapePropagationExamples.Trap.indexed
      [PetaProof.EscapeExamples.Node.exit] PetaProof.EscapeExamples.vertices .exit = some 0 ∧
    PetaProof.EscapeAdmissionExamples.Trap.noGoalInput.computedDistance
      PetaProof.EscapeExamples.vertices.length .exit = none := by
  constructor
  · exact PetaProof.EscapePropagation.State.runLabels_goal_zero _ _ _ _ (by simp)
  · exact PetaProof.HistoryArena.empty_target_exact _ (fun _ impossible => impossible)
      PetaProof.EscapeExamples.vertices PetaProof.EscapeExamples.covered .exit

end DistanceReviewExamples

#print axioms DistanceReviewExamples.one_way_coverage_not_exact
#print axioms DistanceReviewExamples.false_goal_changes_output
