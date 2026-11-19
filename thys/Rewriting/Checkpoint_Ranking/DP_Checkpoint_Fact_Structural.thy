theory DP_Checkpoint_Fact_Structural
 imports DP_Checkpoint_Fact
begin

text \<open>Witness terms are certificate data. Each executable test binds them
to the exact src_claim and dst_claim claims; supplying a term alone establishes no
observation. Every soundness conclusion uses the same arbitrary substitution.\<close>
definition check_checkpoint_fact_split where
 "check_checkpoint_fact_split N Z S h t src_claim dst_claim =
 (src_claim=(CP_Exact 0,[checkpoint_list_cons N Z S h t]) \<and>
 dst_claim=(CP_Split 0 1,[h,t]))"

definition check_checkpoint_fact_prefix where
 "check_checkpoint_fact_prefix h t src_claim dst_claim =
 (src_claim=(CP_Split 0 1,[h,t]) \<and> dst_claim=(CP_Prefix 0,[h]))"

definition check_checkpoint_fact_arguments_start where
 "check_checkpoint_fact_arguments_start N f children src_claim dst_claim =
 (src_claim=(CP_Prefix 0,[Fun N [children]]) \<and>
 dst_claim=(CP_Arguments f 0,[Fun f [children]]))"

definition check_checkpoint_fact_ground_start where
 "check_checkpoint_fact_ground_start f param dst_claim =
 (dst_claim=(CP_Ground f 0 1,[Fun f [param],param]))"

definition check_checkpoint_fact_list_start where
 "check_checkpoint_fact_list_start f h t param shape guard_claim dst_claim =
 (shape=(CP_Split 0 1,[h,t]) \<and> guard_claim=(CP_Guard 0,[param]) \<and>
 dst_claim=(CP_List f 0 1,[Fun f [t,param],h]))"

lemma checked_checkpoint_fact_split:
 assumes constructors: "{N,Z,S}\<subseteq>C"
 and checked: "check_checkpoint_fact_split N Z S h t src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S R old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
 using assms by (auto simp: check_checkpoint_fact_split_def checkpoint_fact_holds_def checkpoint_list_cons_def)

lemma checked_checkpoint_fact_prefix:
 assumes checked: "check_checkpoint_fact_prefix h t src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S R old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
 using assms by (auto simp: check_checkpoint_fact_prefix_def checkpoint_fact_holds_def)

lemma checked_checkpoint_fact_arguments_start:
 assumes constructor: "N\<in>C"
 and checked: "check_checkpoint_fact_arguments_start N f children src_claim dst_claim"
 and holds: "checkpoint_fact_holds C L N Z S R old sigma src_claim"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
proof -
 obtain tail where old: "old=Fun N [checkpoint_skeleton C (children\<cdot>sigma)]#tail"
 using assms by (auto simp: check_checkpoint_fact_arguments_start_def checkpoint_fact_holds_def)
 show ?thesis using checked old
 unfolding check_checkpoint_fact_arguments_start_def checkpoint_fact_holds_def
 apply simp
 unfolding checkpoint_pending_arguments_def
 by (rule exI[of _ "children\<cdot>sigma"], rule exI[of _ tail]) simp
qed

lemma checked_checkpoint_fact_ground_start:
 assumes checked: "check_checkpoint_fact_ground_start f param dst_claim"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
 using checked unfolding check_checkpoint_fact_ground_start_def checkpoint_fact_holds_def
 apply simp
 unfolding checkpoint_pending_ground_def
 by (rule exI[of _ "param\<cdot>sigma"]) simp

lemma checked_checkpoint_fact_list_start:
 assumes checked: "check_checkpoint_fact_list_start f h t param shape guard_claim dst_claim"
 and shape: "checkpoint_fact_holds C L N Z S R old sigma shape"
 and guard_claim: "checkpoint_fact_holds C L N Z S R old sigma guard_claim"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
proof -
 have old: "old=checkpoint_skeleton C (h\<cdot>sigma)#checkpoint_forest N Z S (checkpoint_skeleton C (t\<cdot>sigma))"
 and param: "checkpoint_guard C L (param\<cdot>sigma)"
 using assms by (auto simp: check_checkpoint_fact_list_start_def checkpoint_fact_holds_def)
 show ?thesis using checked old param
 unfolding check_checkpoint_fact_list_start_def checkpoint_fact_holds_def
 apply simp
 unfolding checkpoint_pending_list_def
 by (rule exI[of _ "t\<cdot>sigma"], rule exI[of _ "param\<cdot>sigma"]) simp
qed

ML \<open>
val thms = @{thms checked_checkpoint_fact_split checked_checkpoint_fact_prefix checked_checkpoint_fact_arguments_start checked_checkpoint_fact_ground_start checked_checkpoint_fact_list_start};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted structural fact checker" else ();
\<close>
end
