theory LP_Cut_Return_Steps
  imports LP_Cut_Return_State
begin

theorem lpc_return_resolution_success:
  assumes resolve: "lp_cut_check_resolution P fuel k l G A guards a gs c m (map fst saved) next anchors"
    and known: "lp_cut_knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_ieval (fst (P!c)) rho"
    and payload: "lpc_check_return_values fuel k G
      (lp_cut_resolution_equations k l G a (fst (P!c))) active (concat (map snd saved)) result"
    and saved: "lpc_return_short k saved"
  shows "lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,result)#saved) =
    (LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs),
      (\<lambda>n. lp_isubst (lpc_return_env active eta n) sigma)) # lpc_return_eval eta saved"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  have entry: "lp_cut_entry_map (\<lambda>t. lp_ieval t ?env) (LPCGoals next) =
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)"
    using lp_cut_check_resolution_success(1)[OF resolve known unifier]
    by (simp add: lp_cut_state_map_def)
  have answer: "lpc_return_env result ?env = (\<lambda>n. lp_isubst (lpc_return_env active eta n) sigma)"
    by (rule lpc_return_env_active, rule lpc_resolution_return_values(1)[OF resolve known unifier payload])
  have bounds: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
  have tail: "lpc_return_eval ?env saved = lpc_return_eval eta saved"
    by (rule lpc_return_eval_saved[OF saved bounds])
  show ?thesis using entry answer tail by (simp add: lpc_return_eval_def)
qed

theorem lpc_return_unification_success:
  assumes unify: "lp_cut_check_unify fuel k l G guards a b gs (map fst saved) next"
    and known: "lp_cut_knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma"
    and payload: "lpc_check_return_values fuel k G
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))] active (concat (map snd saved)) result"
    and saved: "lpc_return_short k saved"
  shows "lpc_return_eval (lp_cut_resolution_env k l eta sigma eta) ((LPCGoals next,result)#saved) =
    (LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs),
      (\<lambda>n. lp_isubst (lpc_return_env active eta n) sigma)) # lpc_return_eval eta saved"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma eta"
  have entry: "lp_cut_entry_map (\<lambda>t. lp_ieval t ?env) (LPCGoals next) =
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)"
    using lp_cut_checked_unify_success(1)[OF unify known unifier]
    by (simp add: lp_cut_state_map_def)
  have answer: "lpc_return_env result ?env = (\<lambda>n. lp_isubst (lpc_return_env active eta n) sigma)"
    by (rule lpc_return_env_active, rule lpc_unification_return_values(1)[OF unify known unifier payload])
  have bounds: "k\<le>l" using unify by (auto simp: lp_cut_check_unify_def)
  have tail: "lpc_return_eval ?env saved = lpc_return_eval eta saved"
    by (rule lpc_return_eval_saved[OF saved bounds])
  show ?thesis using entry answer tail by (simp add: lpc_return_eval_def)
qed

end
