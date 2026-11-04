theory LP_Cut_Rational_Goals
  imports LP_Cut_Rational_Graph_MGU LP_Rational_Graph_Clash
begin

fun lpc_rational_goal_match where
  "lpc_rational_goal_match fuel G env (LPCAtom t) (LPCAtom i) = lp_rational_match fuel G env t i"
| "lpc_rational_goal_match fuel G env (LPCUnify a b) (LPCUnify i j) =
    (lp_rational_match fuel G env a i \<and> lp_rational_match fuel G env b j)"
| "lpc_rational_goal_match fuel G env (LPCMeta t) (LPCMeta i) = lp_rational_match fuel G env t i"
| "lpc_rational_goal_match fuel G env (LPCExpand t m) (LPCExpand i n) =
    (m=n \<and> lp_rational_match fuel G env t i)"
| "lpc_rational_goal_match fuel G env (LPCCut m) (LPCCut n) = (m=n)"
| "lpc_rational_goal_match fuel G env LPCTrue LPCTrue = True"
| "lpc_rational_goal_match fuel G env LPCFail LPCFail = True"
| "lpc_rational_goal_match fuel G env a b = False"

lemma lpc_rational_goal_match_sound:
  "lpc_rational_goal_match fuel G env a b \<Longrightarrow>
   lp_cut_map (\<lambda>t. lp_ieval t (lp_rational_match_env G rho env)) a =
   lp_cut_map (lp_rational_graph_value G rho) b"
  by (cases a; cases b) (auto dest: lp_rational_match_sound)

lemma lpc_rational_body_match_sound:
  assumes "list_all2 (lpc_rational_goal_match fuel G env)
    (map (lp_cut_bind m id) body) refs"
  shows "map (lp_cut_bind m (\<lambda>t. lp_ieval t (lp_rational_match_env G rho env))) body =
    map (lp_cut_map (lp_rational_graph_value G rho)) refs"
proof -
  have "map (lp_cut_map (\<lambda>t. lp_ieval t (lp_rational_match_env G rho env)))
      (map (lp_cut_bind m id) body) = map (lp_cut_map (lp_rational_graph_value G rho)) refs"
    using assms by (induction rule: list_all2_induct) (auto dest: lpc_rational_goal_match_sound)
  then show ?thesis by (simp add: map_map o_def lp_cut_map_bind)
qed
end
