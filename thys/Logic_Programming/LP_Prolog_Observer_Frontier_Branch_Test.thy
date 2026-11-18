theory LP_Prolog_Observer_Frontier_Branch_Test
 imports LP_Prolog_Observer_Frontier_Unification_Check LP_Prolog_Observer_Frontier_Is_Check
begin

lemma lpp_frontier_both_requires_failure:
 "lpcl_target no\<notin>frontier_nodes \<Longrightarrow>
  \<not>lpp_check_frontier_branches frontier_nodes LPCBoth yes no"
 by (simp add: lpp_check_frontier_branches_def)

lemma lpp_frontier_both_requires_success:
 "lpcl_target yes\<notin>frontier_nodes \<Longrightarrow>
  \<not>lpp_check_frontier_branches frontier_nodes LPCBoth yes no"
 by (simp add: lpp_check_frontier_branches_def)

lemma lpp_frontier_both_covered:
 "lpcl_target yes\<in>frontier_nodes \<Longrightarrow> lpcl_target no\<in>frontier_nodes \<Longrightarrow>
  lpp_check_frontier_branches frontier_nodes LPCBoth yes no"
 by (simp add: lpp_check_frontier_branches_def)

lemma lpp_frontier_success_placeholder:
 "lpp_check_frontier_branches frontier_nodes LPCAlwaysSuccess yes no = (lpcl_target yes\<in>frontier_nodes)"
 by (simp add: lpp_check_frontier_branches_def)

lemma lpp_frontier_failure_placeholder:
 "lpp_check_frontier_branches frontier_nodes LPCAlwaysFailure yes no = (lpcl_target no\<in>frontier_nodes)"
 by (simp add: lpp_check_frontier_branches_def)

end
