theory LP_Cut_Domain_SEG_Projected_Graph
 imports LP_Cut_Domain_SEG_Observed_Region_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_projected_component_checked_lower:
  assumes checked: "lpc_seg_check_projected_component fuel P roots Fs entry_root F filtering is_cont c d R component"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>us v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta),v)
      \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      precise_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
      precise_return_contract P us (lpc_seg_projected_rel filtering R) v out"
  shows "precise_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))"
proof (cases component)
  case (LPCSEGFreeRegion region Ls)
  show ?thesis by (rule precise_seg_observed_region_checked_lower[OF _ program known free finite ambient lower])
    (use checked in \<open>simp add: LPCSEGFreeRegion\<close>)
next
  case (LPCSEGFreeSplit receipt)
  show ?thesis by (rule precise_seg_projected_split_checked_lower[OF _ program known free finite ambient lower])
    (use checked in \<open>simp add: LPCSEGFreeSplit\<close>)
qed



theorem precise_seg_projected_checked_graph_contract:
  assumes checked: "lpc_seg_check_projected_graph fuel P roots Fs regions q modes filtering is_cont c d R"
    and sn: "SN (rstep (af_rule filtering ` R))"
    and rep: "precise_seg_projected_root_rep filtering roots Fs is_cont c d ss t ret"
  shows "precise_return_contract P ss (lpc_seg_projected_rel filtering R) t ret"
proof (rule precise_seg_projected_graph_contract[OF sn rep])
  fix i eta A
  assume index: "i<length roots"
    and known: "knowledge (set (lpcn_ground (lpcsr_node (roots!i)))) (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>us v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta),v)
      \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      precise_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
      precise_return_contract P us (lpc_seg_projected_rel filtering R) v out"
  have local: "lpc_seg_check_projected_component fuel P roots Fs (roots!i) (Fs!i) filtering is_cont c d R (regions!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpc_seg_check_projected_graph_def list_all_iff)
  show "precise_return_contract P (lpc_return_eval eta (lpc_seg_root_state (roots!i))) (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho))"
    by (rule precise_seg_projected_component_checked_lower[OF local program known free finite ambient lower])
qed


theorem precise_seg_projected_graph_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpc_seg_check_projected_graph fuel P roots Fs regions q modes filtering is_cont c d R"
    and sn: "SN (rstep (af_rule filtering ` R))"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and domains: "list_all D ts"
  shows "SN_on (precise_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpcsr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and shape: "lpc_seg_role_shape 1 is_cont (lpcsr_input ?entry)"
    and vars: "vars_term (af_term filtering (lpc_seg_role_term 1 is_cont c d (lpcsr_input ?entry))) \<subseteq> set (lpcn_ground ?nd)"
    using checked by (auto simp: lpc_seg_check_projected_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have envD: "\<forall>x. D (?eta x)"
    by (intro allI; rule query_env_domain) (use domains in \<open>auto simp: list_all_iff\<close>)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root finite_values envD by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input ?entry) ?eta)"
    by (rule lpc_seg_projected_query[OF shape vars]) (use known in \<open>simp add: knowledge_def\<close>)
  have index: "0<length roots" using nonempty by simp
  have free: "lpc_free_knowledge (set (Fs!0)) ?eta"
    using checked by (simp add: lpc_seg_check_projected_graph_def lpc_free_knowledge_def)
  have represented: "precise_seg_projected_root_rep filtering roots Fs is_cont c d
      (lpc_return_eval ?eta (lpc_seg_root_state ?entry))
      ((\<lambda>x. x) (lpc_seg_runtime_value is_cont c d (lpcsr_input ?entry) ?eta))
      (\<lambda>rho. (\<lambda>x. x) (lpc_seg_runtime_value is_cont c d (lpcsr_output ?entry) rho))"
    by (rule precise_seg_projected_root_repI[OF index known free finite lpc_seg_projection_context.hole])
  have contract: "precise_return_contract P (lpc_return_eval ?eta (lpc_seg_root_state ?entry)) (lpc_seg_projected_rel filtering R)
      ((\<lambda>x. x) (lpc_seg_runtime_value is_cont c d (lpcsr_input ?entry) ?eta))
      (\<lambda>rho. (\<lambda>x. x) (lpc_seg_runtime_value is_cont c d (lpcsr_output ?entry) rho))"
    by (rule precise_seg_projected_checked_graph_contract[OF checked sn represented])
  have source: "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using contract by (simp add: precise_return_contract_def lpc_return_eval_erases lpc_seg_root_state_def map_map o_def)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


end
end
