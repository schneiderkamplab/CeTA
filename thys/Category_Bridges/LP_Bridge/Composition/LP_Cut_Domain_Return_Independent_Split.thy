theory LP_Cut_Domain_Return_Independent_Split
 imports LP_Cut_Domain_Return_Entry_Certificate
begin

context cut_runtime_domain
begin

theorem precise_return_ground_split_independent_SN:
  assumes shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and ground_check: "lpc_check_return_output_groundness P pre G interface positions groundQ Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and domains: "\<And>x. D (eta x)"
    and continuation: "\<And>rho. (\<And>x. D (rho x)) \<Longrightarrow> (\<forall>i\<in>set positions. lp_seg_ground (rho i)) \<Longrightarrow>
      SN_on (precise_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest))]}"
  shows "SN_on (precise_source P) {map fst (lpc_return_eval eta original)}"
proof -
  let ?ss = "lpc_return_eval eta [(LPCGoals pre,interface)]"
  let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  have next_sn: "SN_on (precise_source P)
      {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?gs)]}"
    if actual: "precise_actual_return P ?ss rho" for rho
    by (rule continuation[OF precise_actual_return_domain[OF precise_environments_eval[OF domains] actual] precise_return_output_groundness_sound[OF ground_check known actual]])
  have attached: "SN_on (precise_source P) {lpc_attach ?gs ?ss}"
    by (rule precise_return_source_SN_actual[OF program prefix])
      (use next_sn in \<open>auto simp: lpc_return_eval_def\<close>)
  have source_shape: "map fst (lpc_return_eval eta original)=lpc_attach ?gs ?ss"
    using lpc_return_split_shape_sound[OF shape, of eta]
    by (metis lpc_reinterface_erases lpc_attach_answers_erases)
  show ?thesis using attached source_shape by simp
qed



end
end
