theory LP_Cut_Return_Independent_Split
 imports LP_Cut_Return_Ground_Continuation LP_Cut_Return_Output_Groundness
begin

text \<open>Prefix and continuation termination may be discharged independently.
The prefix still needs an answer-sensitive source contract, but the continuation
need not share its abstract residual relation or its argument filtering.\<close>

theorem lpc_return_ground_split_independent_SN:
  assumes shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and ground_check: "lpc_check_return_output_groundness P pre G interface positions groundQ Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and continuation: "\<And>rho. (\<forall>i\<in>set positions. lp_seg_ground (rho i)) \<Longrightarrow>
      SN_on (lp_cut_mgu_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest))]}"
  shows "SN_on (lp_cut_mgu_source P) {map fst (lpc_return_eval eta original)}"
proof -
  let ?ss = "lpc_return_eval eta [(LPCGoals pre,interface)]"
  let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  have next_sn: "SN_on (lp_cut_mgu_source P)
      {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?gs)]}"
    if actual: "lpc_actual_return P ?ss rho" for rho
    by (rule continuation[OF lpc_return_output_groundness_sound[OF ground_check known actual]])
  have attached: "SN_on (lp_cut_mgu_source P) {lpc_attach ?gs ?ss}"
    by (rule lpc_return_source_SN_actual[OF program prefix])
      (use next_sn in \<open>auto simp: lpc_return_eval_def\<close>)
  have source_shape: "map fst (lpc_return_eval eta original)=lpc_attach ?gs ?ss"
    using lpc_return_split_shape_sound[OF shape, of eta]
    by (metis lpc_reinterface_erases lpc_attach_answers_erases)
  show ?thesis using attached source_shape by simp
qed

end
