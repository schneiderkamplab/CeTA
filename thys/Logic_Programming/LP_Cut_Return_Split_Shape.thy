theory LP_Cut_Return_Split_Shape
  imports LP_Cut_Return_Routing
begin

definition lpc_check_return_split_shape where
  "lpc_check_return_split_shape bindings indices pre rest interface original =
    (lpc_check_return_route_goals bindings interface rest \<and>
     lpc_check_return_projection indices [(LPCGoals (pre@rest),interface)] original)"

lemma lpc_return_split_shape_sound:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
  shows "lpc_return_eval eta original =
    lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
        (lpc_return_eval eta [(LPCGoals pre,interface)]))"
proof -
  have route: "lpc_check_return_route_goals bindings interface rest"
    and projection: "lpc_check_return_projection indices [(LPCGoals (pre@rest),interface)] original"
    using checked by (auto simp: lpc_check_return_split_shape_def)
  have attach: "lpc_attach_answers
      (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
      (lpc_return_eval eta [(LPCGoals pre,interface)]) =
    lpc_return_eval eta [(LPCGoals (pre@rest),interface)]"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis using lpc_check_return_projection_sound[OF projection, of eta]
    by (simp add: attach)
qed

theorem lpc_return_split_shape_contract:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and continuation: "\<And>rho. (t,ret rho)\<in>R\<^sup>* \<Longrightarrow>
      lpc_return_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)] R (ret rho) extended"
    and bridge: "\<And>rho. (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_return_eval eta original) R t final"
proof -
  have composed: "lpc_return_contract P
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
      (lpc_return_eval eta [(LPCGoals pre,interface)])) R t extended"
    by (rule lpc_return_contract_compose[OF program prefix])
      (use continuation in \<open>auto simp: lpc_return_eval_def\<close>)
  have projected: "lpc_return_contract P
    (lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
        (lpc_return_eval eta [(LPCGoals pre,interface)]))) R t final"
    by (rule lpc_return_contract_project[OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta] by simp
qed

end
