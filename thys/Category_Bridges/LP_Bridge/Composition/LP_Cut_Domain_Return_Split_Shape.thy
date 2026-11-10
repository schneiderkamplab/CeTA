theory LP_Cut_Domain_Return_Split_Shape
  imports LP_Cut_Domain_Return_Continuation
begin

context cut_runtime_domain
begin

theorem precise_return_split_shape_contract:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and domains: "\<And>x. D (eta x)"
    and continuation: "\<And>rho. (\<And>x. D (rho x)) \<Longrightarrow> (t,ret rho)\<in>R\<^sup>* \<Longrightarrow>
      precise_return_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)] R (ret rho) extended"
    and bridge: "\<And>rho. (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_return_eval eta original) R t final"
proof -
  have composed: "precise_return_contract P
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
      (lpc_return_eval eta [(LPCGoals pre,interface)])) R t extended"
    by (rule precise_return_contract_compose_domain[OF program prefix precise_environments_eval[OF domains]])
      (use continuation in \<open>auto simp: lpc_return_eval_def\<close>)
  have projected: "precise_return_contract P
    (lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
        (lpc_return_eval eta [(LPCGoals pre,interface)]))) R t final"
    by (rule precise_return_contract_project[OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta] by simp
qed


end
end
