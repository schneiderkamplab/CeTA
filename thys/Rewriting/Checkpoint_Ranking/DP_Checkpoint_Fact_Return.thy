theory DP_Checkpoint_Fact_Return
 imports DP_Checkpoint_Fact_Structural
begin

lemma checked_checkpoint_pending_arguments_return:
 assumes checked: "check_checkpoint_argument_summary C N Z S ain aout resume support witnesses"
 and leaf: "L\<notin>{N,Z,S}"
 and pending: "checkpoint_pending_arguments C N (set support) ain old (Fun aout [copied,result])"
 shows "checkpoint_forest_less L (checkpoint_forest N Z S (checkpoint_skeleton C result)) old"
proof -
 obtain children tail where old: "old=Fun N [checkpoint_skeleton C children]#tail"
 and success: "(Fun ain [children],Fun aout [copied,result])\<in>(Trs.rstep (set support))\<^sup>*"
 using pending by (auto simp: checkpoint_pending_arguments_def)
 obtain xs where raw: "checkpoint_raw_children Z S (checkpoint_skeleton C children)=Some xs"
 and result: "checkpoint_skeleton C result=checkpoint_encoded_list N Z S xs"
 using checked_checkpoint_argument_success[OF checked success] by blast
 have decrease: "checkpoint_forest_less L xs (Fun N [checkpoint_skeleton C children]#tail)"
 using checkpoint_forest_head_descent[where N=N and L=L and tail="checkpoint_encoded_list N Z S tail", OF raw] leaf
 by (auto simp: checkpoint_forest_less_def)
 show ?thesis using decrease by (simp add: old result)
qed

lemma checked_checkpoint_pending_ground_return:
 assumes checked: "check_checkpoint_ground_summary C N Z S gin gout spine_in sout resume head tail support witnesses"
 and leaf: "L\<notin>{N,Z,S}"
 and pending: "checkpoint_pending_ground C (set support) gin (Fun gout outputs) param"
 shows "checkpoint_guard C L param"
proof -
 obtain initial where equal: "checkpoint_skeleton C initial=checkpoint_skeleton C param"
 and success: "(Fun gin [initial],Fun gout outputs)\<in>(Trs.rstep (set support))\<^sup>*"
 using pending by (auto simp: checkpoint_pending_ground_def)
 show ?thesis using checked_checkpoint_ground_leaf_free[OF checked success leaf] equal
 by (auto simp: checkpoint_guard_def)
qed

lemma checked_checkpoint_pending_list_return:
 assumes checked: "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses"
 and domain: "check_checkpoint_list_domain C N Z S lin lout lhead ltail ein eout support domain_witnesses"
 and pending: "checkpoint_pending_list C L N Z S (set support) lin old (Fun lout [copied,result,returned_param]) h"
 shows "checkpoint_forest_less L (checkpoint_forest N Z S (checkpoint_skeleton C result)) old"
proof -
 obtain initial param where old: "old=checkpoint_skeleton C h#checkpoint_forest N Z S (checkpoint_skeleton C initial)"
 and guard: "checkpoint_guard C L param"
 and success: "(Fun lin [initial,param],Fun lout [copied,result,returned_param])\<in>(Trs.rstep (set support))\<^sup>*"
 using pending by (auto simp: checkpoint_pending_list_def)
 have closed: "vars_term (checkpoint_skeleton C param)={}"
 and free: "L\<notin>funs_term (checkpoint_skeleton C param)"
 using guard by (auto simp: checkpoint_guard_def)
 obtain xs ys where before: "checkpoint_skeleton C initial=checkpoint_encoded_list N Z S xs"
 and after: "checkpoint_skeleton C result=checkpoint_encoded_list N Z S ys"
 and related: "list_all2 (checkpoint_leaf_relation L) xs ys"
 using checked_checkpoint_composed_list_return[OF checked domain success closed free] by blast
 have decrease: "checkpoint_forest_less L ys (checkpoint_skeleton C h#xs)"
 unfolding checkpoint_forest_less_def by (simp only: list.map; rule checkpoint_rank_forest_return[OF related])
 show ?thesis using decrease by (simp add: old before after)
qed

definition check_checkpoint_fact_arguments_return where
 "check_checkpoint_fact_arguments_return ain aout copied result src_claim dst_claim =
 (src_claim=(CP_Arguments ain 0,[Fun aout [copied,result]]) \<and> dst_claim=(CP_Strict 0,[result]))"

definition check_checkpoint_fact_ground_return where
 "check_checkpoint_fact_ground_return gin gout copied param src_claim dst_claim =
 (src_claim=(CP_Ground gin 0 1,[Fun gout [copied],param]) \<and> dst_claim=(CP_Guard 0,[param]))"

definition check_checkpoint_fact_list_return where
 "check_checkpoint_fact_list_return lin lout copied result returned_param h src_claim dst_claim =
 (src_claim=(CP_List lin 0 1,[Fun lout [copied,result,returned_param],h]) \<and> dst_claim=(CP_Strict 0,[result]))"

lemma checked_checkpoint_fact_arguments_return:
 assumes summary: "check_checkpoint_argument_summary C N Z S ain aout resume support witnesses"
 and leaf: "L\<notin>{N,Z,S}"
 and checked: "check_checkpoint_fact_arguments_return ain aout copied result src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst_claim"
 using checked holds checked_checkpoint_pending_arguments_return[OF summary leaf]
 by (auto simp: check_checkpoint_fact_arguments_return_def checkpoint_fact_holds_def)

lemma checked_checkpoint_fact_ground_return:
 assumes summary: "check_checkpoint_ground_summary C N Z S gin gout spine_in sout resume head tail support witnesses"
 and leaf: "L\<notin>{N,Z,S}"
 and checked: "check_checkpoint_fact_ground_return gin gout copied param src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst_claim"
 using checked holds checked_checkpoint_pending_ground_return[OF summary leaf]
 by (auto simp: check_checkpoint_fact_ground_return_def checkpoint_fact_holds_def)

lemma checked_checkpoint_fact_list_return:
 assumes summary: "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses"
 and domain: "check_checkpoint_list_domain C N Z S lin lout lhead ltail ein eout support domain_witnesses"
 and checked: "check_checkpoint_fact_list_return lin lout copied result returned_param h src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst_claim"
 using checked holds checked_checkpoint_pending_list_return[OF summary domain]
 by (auto simp: check_checkpoint_fact_list_return_def checkpoint_fact_holds_def)

ML \<open>
val thms = @{thms checked_checkpoint_pending_arguments_return checked_checkpoint_pending_ground_return checked_checkpoint_pending_list_return checked_checkpoint_fact_arguments_return checked_checkpoint_fact_ground_return checked_checkpoint_fact_list_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted return fact checker" else ();
\<close>
end
