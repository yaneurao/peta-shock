import PetaProof

-- Main: 数値の正しさ、安全なbest、任意切替、符号別優先出力をまとめた論文の主定理。
#check PetaProof.ThresholdGame.QueueContext.main_correctness

/-! 論文の定理番号から、前提を含むLeanの命題型を確認するための入口。
これは対応名の検査であり、論文の自然言語を自動的に形式化する検査ではない。 -/

-- T01: 方策検査の条件付き保証。Outcomeと実終局の対応もレビューする。
#check PetaProof.Certificate.sound
#check PetaProof.Certificate.opposite_guarantees
-- T02: 初期分類からの局所キュー解法。
#check PetaProof.SafetyClassification.initialized_solves
-- T03: 停止点と四回出現ゲーム。
#check PetaProof.ThresholdGame.stopped_exact_for_fourfold
-- T04: 正値二側から整数値への合成。
#check PetaProof.ThresholdGame.exact_from_processed_executions
-- T05: 全閾値キュー制御と、入力から構成する主値。
#check PetaProof.ThresholdGame.QueueContext.computedQueueValue_exact
#check PetaProof.ThresholdGame.CoreGraphInput.valueRows_exact
-- T06: 通常イベント。
#check PetaProof.ThresholdGame.QueueContext.two_sides_work_bound
-- T07: 局所呼出し。
#check PetaProof.ThresholdGame.QueueContext.scanLocalCalls_bound
-- T08: 局所削除内部。
#check PetaProof.ThresholdGame.QueueContext.scanLocalWork_bound
-- T09: 候補だけの準備と会計。
#check PetaProof.ThresholdGame.QueueContext.preparedLocalWork_bound
#check PetaProof.ThresholdGame.QueueContext.preparedPropagationWork_bound
-- T10: バケットの安定性と主走査。
#check PetaProof.StableBuckets.build_spec
#check PetaProof.ThresholdGame.bucketedScan_eq
#check PetaProof.ThresholdGame.QueueContext.leafBatches_notifications_bound
-- T11: 整数キー配列。
#check PetaProof.ThresholdKeys.dense_eq
#check PetaProof.ThresholdKeys.dense_at
#check PetaProof.ThresholdKeys.dense_comparisons_bound
-- T12: pop時の記録。
#check PetaProof.ThresholdGame.QueueContext.streamingResult_eq
#check PetaProof.ThresholdGame.QueueContext.streaming_two_sides_bound
-- T13: 主値計算のイベント合成。
#check PetaProof.ThresholdGame.QueueContext.computedRows_and_work
-- T14: 閾値生成。
#check PetaProof.ThresholdGame.QueueContext.generatedRows_and_work
-- T15: 逆辺構築。
#check PetaProof.ReverseAdjacency.build_row
#check PetaProof.ReverseAdjacency.constructionWork_bound
-- T16: SCCからの王手循環候補と主値。
#check PetaProof.ThresholdGame.CoreGraphInput.ownCore_correct
#check PetaProof.ThresholdGame.CoreGraphInput.otherCore_correct
#check PetaProof.ThresholdGame.CoreGraphInput.rows_correct
-- T17: 第二DFSの全根会計。
#check PetaProof.ReverseDfsWork.finish_work
-- T18: 逆辺選別と自己辺。
#check PetaProof.ThresholdGame.CoreGraphInput.rows_and_row_work
-- T19: 書込と固定長格納。
#check PetaProof.ThresholdGame.QueueContext.fixed_outputs_safe
#check PetaProof.ThresholdGame.CoreGraphInput.rows_and_stored_work
-- T20: 初回発見と枠生成。
#check PetaProof.ForwardDiscoveryCharge.finish_charge
#check PetaProof.ThresholdGame.CoreGraphInput.rows_and_generated_work
-- T21: フレーム操作と主値の統合イベント上界。
#check PetaProof.ThresholdGame.QueueContext.forwardFrameWork_eq
#check PetaProof.ThresholdGame.QueueContext.reverseStackWork_eq
#check PetaProof.ThresholdGame.CoreGraphInput.rows_and_stack_work
-- T22: 正の領域の複数候補。
#check PetaProof.RankedMoveFilter.Input.filtered_plan_guarantee
-- T23: 非正の下限の複数候補。
#check PetaProof.RefutationMoveFilter.Input.filtered_plan_opposite_lower
-- T24: 共通順位の証拠族を入力した候補表。証拠族を全走査で生成する定理ではない。
#check PetaProof.ThresholdGame.ValueRankTable.terminal_lower
#check PetaProof.ThresholdGame.StratumFamily.candidates_nonempty
#check PetaProof.ThresholdGame.StratumFamily.exact_values
-- T25: 単一phaseの同じ返却集合から正負の共通証拠。
#check PetaProof.ThresholdGame.QueueContext.phase_regions
#check PetaProof.ThresholdGame.QueueContext.phase_generated_regions

/-! 自然言語の前提を弱めてはいけないことの小さな回帰例。 -/
-- T26: 同じ全走査のphase返却列と各閾値の順位証拠。
#check PetaProof.ThresholdGame.phaseStates_final
#check PetaProof.ThresholdGame.generated_phase_regions
-- T27: 符号別depthと保存最大手を候補表の保証へ接続する。
#check PetaProof.OutputPreference.preferred_exists
#check PetaProof.OutputPreference.maximum_iff
#check PetaProof.OutputPreference.encoded_plan_lower
-- T28: 変更祖先、外側への閉性、四回出現保証の一致。
#check PetaProof.IncrementalBoundary.affectedBy_least
#check PetaProof.IncrementalBoundary.no_return
#check PetaProof.IncrementalBoundary.Agreement.fourfold_iff
#check PetaProof.IncrementalBoundary.Agreement.retune
#check PetaProof.IncrementalBoundary.Agreement.opposite

-- T29: 未処理閾値を、合否が同じ代表閾値の記録へ移す。
#check PetaProof.ThresholdGame.QueueContext.witnessLevel_spec
#check PetaProof.ThresholdGame.QueueContext.witnessLevel_cut
#check PetaProof.ThresholdGame.QueueContext.witnessLevel_recorded
#check PetaProof.ThresholdGame.QueueContext.generated_cut_regions
-- T30: 証拠族を入力せず、安全な元辺候補と符号別優先出力を構成する。
#check PetaProof.ThresholdGame.QueueContext.generatedFamily
#check PetaProof.ThresholdGame.QueueContext.generated_kept_nonempty
#check PetaProof.ThresholdGame.QueueContext.generated_kept_lower
#check PetaProof.ThresholdGame.QueueContext.generatedStoredRows_length
#check PetaProof.ThresholdGame.QueueContext.generatedTable_rank_independent
#check PetaProof.ThresholdGame.QueueContext.generated_safe_best
#check PetaProof.ThresholdGame.QueueContext.generatedOutputPlan_lower
#check PetaProof.ThresholdGame.QueueContext.generatedOutputPlan_maximum
#check PetaProof.ThresholdGame.QueueContext.generatedOutputPlans_exact

-- T31: 代表閾値を一回構築した配列で正確に参照する。
#check PetaProof.ThresholdGame.QueueContext.witnessIndex_eq
#check PetaProof.ThresholdGame.QueueContext.witnessIndex_size
#check PetaProof.DenseWitnessIndex.buildWork_exact
-- T32: payload条件を満たす取得器のN要素保存と候補集合への接続。
#check PetaProof.SelectiveRankCapture.routed_unique
#check PetaProof.SelectiveRankCapture.reads_bound
#check PetaProof.SelectiveRankCapture.run_state
#check PetaProof.SelectiveRankCapture.run_size
#check PetaProof.SelectiveRankCapture.run_complete
#check PetaProof.SelectiveRankCapture.streamed_admissible
#check PetaProof.SelectiveRankCapture.streamed_plan_lower
#check PetaProof.ThresholdGame.StratumFamily.bottom_diagonal_rank

-- T33: 処理閾値ごとに共通証拠を固定し、同じ代表と取得先の順位を一致させる。
#check PetaProof.ThresholdGame.SharedPhaseWitness.fromRecords
#check PetaProof.ThresholdGame.SharedPhaseWitness.fromRecords_local
#check PetaProof.ThresholdGame.SharedPhaseWitness.same_positive_rank
#check PetaProof.ThresholdGame.SharedPhaseWitness.same_negative_rank
#check PetaProof.ThresholdGame.SharedRankFamily.fromGenerated
#check PetaProof.ThresholdGame.SharedRankFamily.target_payload
-- T34: 一回分配の要求表と共有証拠から保存までを追加のpayload一致仮定なしで接続。
#check PetaProof.RankRequestBuckets.build_member
#check PetaProof.ThresholdGame.SharedRankFamily.Requests.get_iff
#check PetaProof.ThresholdGame.SharedRankFamily.captured_correct
#check PetaProof.ThresholdGame.SharedRankFamily.captured_reads_bound
#check PetaProof.ThresholdGame.SharedRankFamily.captured_admissible
#check PetaProof.ThresholdGame.SharedRankFamily.generated_capture_lower
-- T35: 構築済みの両視点索引で取得先を計算しても要求配列全体は同一。
#check PetaProof.ThresholdGame.SharedRankFamily.buildWitnessIndices_sizes
#check PetaProof.ThresholdGame.SharedRankFamily.indexedTarget_eq
#check PetaProof.ThresholdGame.SharedRankFamily.indexedRoute_eq
#check PetaProof.ThresholdGame.SharedRankFamily.buildRequests_buckets_eq
-- T36: 有限隣接リストから削除順位と反証応手を計算し、検査成功を完全に特徴付ける。
#check PetaProof.HistoryArena.DeletionInput.run_sizes
#check PetaProof.HistoryArena.DeletionInput.run_alive
#check PetaProof.HistoryArena.DeletionInput.run_rank
#check PetaProof.HistoryArena.DeletionInput.final_rank
#check PetaProof.HistoryArena.DeletionInput.rank_stable_after_empty
#check PetaProof.HistoryArena.DeletionInput.response_sound
#check PetaProof.HistoryArena.DeletionInput.counter_rank_bound
#check PetaProof.HistoryArena.DeletionInput.checkedCounter_iff
-- T37: 単一目標への到達へ帰着し、実FIFOの距離を同期削除順位へ接続する。
#check PetaProof.HistoryArena.DeletionInput.reach_layer_iff
#check PetaProof.HistoryArena.DeletionInput.reach_edges_count
#check PetaProof.HistoryArena.DeletionInput.reach_distance_eq
#check PetaProof.HistoryArena.DeletionInput.fifoTable_size
#check PetaProof.HistoryArena.DeletionInput.fifo_events_bound
#check PetaProof.HistoryArena.DeletionInput.fifo_events_input_bound
#check PetaProof.HistoryArena.DeletionInput.fifoTable_exact
#check PetaProof.HistoryArena.DeletionInput.fifoRanks_reference
#check PetaProof.HistoryArena.DeletionInput.fifoCheckedCounter_iff
#check PetaProof.HistoryArena.DeletionInput.fifoCheckedCounter_agrees
-- T38: 有限出辺からCSR索引とID数を構成し、外部の索引一致仮定なしで反証生成へ接続。
#check PetaProof.HistoryArena.DeletionInput.builtIndex_matches
#check PetaProof.HistoryArena.DeletionInput.incoming_member
#check PetaProof.HistoryArena.DeletionInput.edges_length
#check PetaProof.HistoryArena.DeletionInput.reverse_construction_safe
#check PetaProof.HistoryArena.DeletionInput.reverse_reads_safe
#check PetaProof.HistoryArena.DeletionInput.reverse_sizes
#check PetaProof.HistoryArena.DeletionInput.built_labels_exact
#check PetaProof.HistoryArena.DeletionInput.builtCounter_iff
#check PetaProof.HistoryArena.DeletionInput.builtCounter_agrees
#check PetaProof.HistoryArena.DeletionInput.built_events_bound
-- T39: 確定集合のBool補集合から有限残余を作り、元の領域へ反証を戻す。
#check PetaProof.HistoryArena.DeletionInput.residual_edge
#check PetaProof.HistoryArena.DeletionInput.removed_cannot_stay
#check PetaProof.HistoryArena.DeletionInput.residual_empty_at_size
#check PetaProof.HistoryArena.DeletionInput.solved_residual_success
#check PetaProof.HistoryArena.DeletionInput.solvedComplement_refutes
-- T40: 吸収状態の有限ID化と実phaseからの残余・反証生成。
#check PetaProof.ThresholdGame.absorbed_left
#check PetaProof.ThresholdGame.absorbed_right
#check PetaProof.ThresholdGame.QueueContext.absorbedNext_correct
#check PetaProof.ThresholdGame.QueueContext.absorbedBad_correct
#check PetaProof.ThresholdGame.QueueContext.phase_finite_solved
#check PetaProof.ThresholdGame.QueueContext.phaseResidual_success
#check PetaProof.ThresholdGame.QueueContext.phaseOriginalCounter
#check PetaProof.ThresholdGame.QueueContext.phaseOriginal_refutes


namespace PaperReviewExamples

/-- 異なる二つの下限では、5と7の両方が可能であり値は一意に定まらない。 -/
theorem incompatible_lower_bounds : ∃ first second : Int, first ≠ second ∧
    0 ≤ first ∧ -10 ≤ -first ∧ 0 ≤ second ∧ -10 ≤ -second := by
  exact ⟨5, 7, by decide⟩


end PaperReviewExamples

#print axioms PaperReviewExamples.incompatible_lower_bounds

-- 定理41: depth方式の最終検査から保存最大手と厳密なゲーム値まで。
#check PetaProof.DepthWriter.Input.saved_formula
#check PetaProof.DepthWriter.Input.allowed_iff_checked
#check PetaProof.DepthWriter.Input.output_maximum_iff
#check PetaProof.DepthCheckedOutput.Input.output_lower
#check PetaProof.DepthCheckedOutput.Input.output_positive_no_draw
#check PetaProof.DepthCheckedOutput.Input.output_no_mate_loss
#check PetaProof.DepthCheckedOutput.Input.output_positive_terminates
#check PetaProof.DepthCheckedOutput.Input.exact_value
#check PetaProof.DepthCheckedOutput.Input.opposite_outputs_exact

-- 定理42: 固定した選択手の飽和depthは一意で、有限leaf経路・循環の意味が確定する。
#check PetaProof.SelectedDepth.unique_of_equation
#check PetaProof.SelectedDepth.leaf_distance
#check PetaProof.SelectedDepth.below_cap_has_leaf
#check PetaProof.SelectedDepth.saturated_iff
#check PetaProof.SelectedDepth.cycle_saturated
#check PetaProof.SelectedDepth.reaches_saturated

-- 定理43: 実際の収集・pop・全走査から、親depthと保存条件の一致まで。
#check PetaProof.SelectedDepth.discover_exists
#check PetaProof.SelectedDepth.path_sweep_correct
#check PetaProof.SelectedDepth.scan_total_correct
#check PetaProof.SelectedDepth.reconstruct_exact
#check PetaProof.SelectedDepth.order_independent
#check PetaProof.SelectedDepth.actual_selected_depth
#check PetaProof.SelectedDepth.actual_maximum_iff_checked
