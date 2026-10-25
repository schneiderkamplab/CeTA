theory LP_Cut_SEG_Triple_Split
  imports LP_Cut_SEG_Triple_Observed
begin

text \<open>Checked continuation descent for recursive Split. Both the call
receipt and success receipt are actual members/instances of the extracted D/P
problem. The prefix fact is retained through the second child's substitutions,
so the final success clause cannot combine incompatible answers.\<close>

theorem lpc_triple_split_checked_continuation:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and prefix: "lpc_triple_answer_contract P ss Q (lp_atom_eval first_out)"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and call: "lpc_triple_check_call D [first_out] inp next_in dc db"
    and success: "lpc_triple_check_model_clause Q [next_out,first_out] final pc pb"
    and lower: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      (a,lp_atom_eval next_in eta)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpc_triple_answer_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval next_out)"
  shows "lpc_triple_answer_contract P (lpc_attach_answers rest ss) Q (lp_atom_eval final)"
proof (rule lpc_triple_answer_split[OF program prefix valid separated])
  fix eta assume actual: "lpc_actual_return P ss eta"
    and model: "lp_answer_model Q (lp_atom_eval first_out eta)"
  have match: "\<exists>sigma. lp_iatom_subst a sigma=lp_atom_eval inp eta"
  proof (rule lpc_actual_return_substitution_property[OF _ actual
      invariant[unfolded lpc_triple_instance_invariant_def]])
    fix rho sigma
    assume "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp rho"
    then obtain tau where match: "lp_iatom_subst a tau=lp_atom_eval inp rho" by blast
    have "lp_iatom_subst a (\<lambda>x. lp_isubst (tau x) sigma)=
      lp_atom_eval inp (\<lambda>x. lp_isubst (rho x) sigma)"
      using arg_cong[OF match, of "\<lambda>b. lp_iatom_subst b sigma"]
      by (simp add: lp_iatom_subst_def lp_atom_eval_def lp_seg_isubst_comp
        lp_ieval_subst map_map o_def)
    then show "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp (\<lambda>x. lp_isubst (rho x) sigma)" by blast
  qed
  obtain sigma where matching: "lp_iatom_subst a sigma=lp_atom_eval inp eta" using match by blast
  have edge: "(a,lp_atom_eval next_in eta)\<in>lp_triple_calls (set D) Q"
    by (rule lpc_triple_checked_call[OF call matching]) (use model in auto)
  have child: "lpc_triple_answer_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval next_out)"
    by (rule lower[OF actual edge])
  show "lpc_triple_answer_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval final)"
    by (rule lpc_triple_answer_extend_facts[where facts="[first_out]", OF child _ success])
      (simp add: model)
qed

end
