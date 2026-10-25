theory LP_Cut_Projected_Split_Shape
  imports LP_Cut_Projected_Semantic LP_Cut_Return_Split_Shape
begin

theorem lpc_return_contract_project_reachable:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_return_contract P ss R t ret"
    and bridge: "\<And>eta. (t,ret eta)\<in>R\<^sup>* \<Longrightarrow> (ret eta,final (F eta))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_reinterface F ss) R t final"
proof (unfold lpc_return_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst (lpc_reinterface F ss)}"
    using contract by (simp add: lpc_return_contract_def)
next
  fix us tail rho
  assume path: "(lpc_reinterface F ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) tail"
  obtain vs where reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpc_reinterface_path_reflect[OF commute path] by blast
  have actual: "lpc_answer_transition P (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where local: "lpc_answer_transition P vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpc_reinterface_reflect[OF commute actual] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have output_path: "(t,ret eta)\<in>R\<^sup>*"
    using contract reached local ev unfolding lpc_return_contract_def by blast
  show "(t,final rho)\<in>R\<^sup>*"
    unfolding rho by (rule rtrancl_trans[OF output_path bridge[OF output_path]])
qed

theorem lpc_return_split_shape_reachable_contract:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and continuation: "\<And>rho. (t,ret rho)\<in>R\<^sup>* \<Longrightarrow>
      lpc_return_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)] R (ret rho) extended"
    and bridge: "\<And>rho. (t,extended rho)\<in>R\<^sup>* \<Longrightarrow> (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
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
    by (rule lpc_return_contract_project_reachable[OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta] by simp
qed

end
