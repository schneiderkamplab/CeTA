theory LP_Cut_Return_Control
  imports LP_Cut_Return_Models
begin

text \<open>Successful-return models may overapproximate equality goals while
retaining their actual substitution in the shared answer semantics. This
control cover is separate from the termination residual control cover.\<close>

fun lpc_return_control_goal where
  "lpc_return_control_goal F (LPCUnify a b) = True"
| "lpc_return_control_goal F g = lpc_control_goal F g"

fun lpc_return_control_igoal where
  "lpc_return_control_igoal F (LPCUnify a b) = True"
| "lpc_return_control_igoal F g = lpc_control_igoal F g"

lemma lpc_return_control_goal_iff:
  "lpc_return_control_goal F g \<longleftrightarrow> lpc_control_goal F g \<or> (\<exists>a b. g=LPCUnify a b)"
  by (cases g) auto

lemma lpc_return_control_igoal_iff:
  "lpc_return_control_igoal F g \<longleftrightarrow> lpc_control_igoal F g \<or> (\<exists>a b. g=LPCUnify a b)"
  by (cases g) auto

lemma lpc_return_control_bind:
  assumes "list_all (lpc_return_control_goal F) gs"
  shows "list_all (lpc_return_control_igoal F) (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) gs)"
  using assms by (induct gs)
    (auto simp: lpc_return_control_goal_iff lpc_control_goal_iff)

lemma lpc_return_control_subst:
  assumes "list_all (lpc_return_control_igoal F) gs"
  shows "list_all (lpc_return_control_igoal F) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
  using assms by (induct gs)
    (auto simp: lpc_return_control_igoal_iff lpc_control_igoal_iff)

lemma lpc_return_control_safe:
  "list_all (lpc_return_control_goal F) gs \<Longrightarrow> list_all lpc_model_safe_goal gs"
  by (auto simp: list_all_iff lpc_return_control_goal_iff lpc_control_goal_iff)

end
