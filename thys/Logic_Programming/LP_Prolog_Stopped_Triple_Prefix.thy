theory LP_Prolog_Stopped_Triple_Prefix
 imports LP_Prolog_Stopped_Triple_Interface LP_Prolog_Stable_Triple_Prefix
begin


lemma lpp_stopped_actual_return_preserves_model:
  assumes actual: "lpp_stopped_actual_return operation P ss eta"
    and known: "list_all (\<lambda>e. lp_answer_model Q (lp_atom_eval a (snd e))) ss"
  shows "lp_answer_model Q (lp_atom_eval a eta)"
proof (rule lpp_actual_return_substitution_property[OF _ lp_answer_stop_actual[OF actual] known])
  fix rho sigma assume model: "lp_answer_model Q (lp_atom_eval a rho)"
  show "lp_answer_model Q (lp_atom_eval a (\<lambda>x. lp_isubst (rho x) sigma))"
    using lp_answer_model_subst[OF model, of sigma]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def lp_ieval_subst map_map o_def)
qed

theorem lpp_stopped_triple_answer_extend_facts:
  assumes child: "lpp_stopped_triple_answer_contract operation P ss Q (lp_atom_eval out)"
    and known: "list_all (\<lambda>e. list_all (\<lambda>a. lp_answer_model Q (lp_atom_eval a (snd e))) facts) ss"
    and receipt: "lpc_triple_check_model_clause Q (out#facts) final c bindings"
  shows "lpp_stopped_triple_answer_contract operation P ss Q (lp_atom_eval final)"
proof (unfold lpp_stopped_triple_answer_contract_characterization, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))) {ss}"
    using child by (simp add: lpp_stopped_triple_answer_contract_characterization)
next
  fix eta assume actual: "lpp_stopped_actual_return operation P ss eta"
  have result_model: "lp_answer_model Q (lp_atom_eval out eta)"
    by (rule lpp_stopped_triple_answer_contract_return[OF child actual])
  have preserved: "lp_answer_model Q (lp_atom_eval a eta)" if "a\<in>set facts" for a
    by (rule lpp_stopped_actual_return_preserves_model[OF actual])
      (use known that in \<open>auto simp: list_all_iff\<close>)
  show "lp_answer_model Q (lp_atom_eval final eta)"
    by (rule lpc_triple_checked_model_clause[OF receipt]) (use result_model preserved in auto)
qed




text \<open>Checked continuation descent for recursive Split. Both the call
receipt and success receipt are actual members/instances of the extracted D/P
problem. The prefix fact is retained through the second child's substitutions,
so the final success clause cannot combine incompatible answers.\<close>

theorem lpp_stopped_triple_split_checked_continuation:
  fixes P :: "(string,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and prefix: "lpp_stopped_triple_answer_contract operation P ss Q (lp_atom_eval first_out)"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and call: "lpc_triple_check_call D [first_out] inp next_in dc db"
    and success: "lpc_triple_check_model_clause Q [next_out,first_out] final pc pb"
    and lower: "\<And>eta. lpp_stopped_actual_return operation P ss eta \<Longrightarrow>
      (a,lp_atom_eval next_in eta)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_stopped_triple_answer_contract operation P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval next_out)"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_attach_answers rest ss) Q (lp_atom_eval final)"
proof (rule lpp_stopped_triple_answer_split[OF program prefix valid separated])
  fix eta assume actual: "lpp_stopped_actual_return operation P ss eta"
    and model: "lp_answer_model Q (lp_atom_eval first_out eta)"
  have match: "\<exists>sigma. lp_iatom_subst a sigma=lp_atom_eval inp eta"
  proof (rule lpp_actual_return_substitution_property[OF _ lp_answer_stop_actual[OF actual]
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
  have child: "lpp_stopped_triple_answer_contract operation P
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval next_out)"
    by (rule lower[OF actual edge])
  show "lpp_stopped_triple_answer_contract operation P
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q (lp_atom_eval final)"
    by (rule lpp_stopped_triple_answer_extend_facts[where facts="[first_out]", OF child _ success])
      (simp add: model)
qed




lemma lpp_stopped_seg_captured_term:
  assumes actual: "lpp_stopped_actual_return operation P ss eta"
    and ground: "\<forall>x\<in>vars_term t. lp_seg_ground (initial_env x)"
    and known: "list_all (\<lambda>e. \<forall>x\<in>vars_term t. snd e x=initial_env x) ss"
  shows "lp_ieval t eta=lp_ieval t initial_env"
proof (rule lp_ieval_cong)
  fix x assume x: "x\<in>vars_term t"
  have finite: "lp_seg_ground (initial_env x)" using ground x by blast
  have initialized: "list_all (\<lambda>e. snd e x=initial_env x) ss"
    using known x by (auto simp: list_all_iff)
  show "eta x=initial_env x"
    by (rule lpp_actual_return_preserves_finite_value[OF finite lp_answer_stop_actual[OF actual] initialized])
qed

lemma lpp_stopped_seg_observed_actual:
  assumes actual: "lpp_stopped_actual_return operation P (lpc_return_eval eta [(e,map Var vs)]) rho"
  obtains theta where
    "lpp_stopped_actual_return operation P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    "rho=lpc_return_env (map Var vs) theta"
proof -
  have shape: "lpc_return_eval eta [(e,map Var vs)] =
    lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have observed: "lpp_stopped_actual_return operation P
    (lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]) rho"
    using actual by (simp only: shape)
  show ?thesis
    using lpp_stopped_actual_return_reinterface[where F="lpc_return_env (map Var vs)",
      OF lpc_return_env_commutes observed] that by blast
qed

lemma lpp_stopped_seg_observed_captured_term:
  assumes actual: "lpp_stopped_actual_return operation P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and finite: "lp_seg_ground (lp_ieval t eta)"
  shows "lp_ieval (lpc_seg_position_template vs t) rho = lp_ieval t eta"
proof -
  obtain theta where source: "lpp_stopped_actual_return operation P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stopped_seg_observed_actual[OF actual] by blast
  have known: "\<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
    using finite by (simp only: lp_seg_ground_eval)
  have preserved: "lp_ieval t theta=lp_ieval t eta"
    by (rule lpp_stopped_seg_captured_term[OF source known]) simp
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed


ML \<open>
val checked = [@{thm lpp_stopped_actual_return_preserves_model}, @{thm lpp_stopped_triple_answer_extend_facts},
  @{thm lpp_stopped_triple_split_checked_continuation}, @{thm lpp_stopped_seg_captured_term},
  @{thm lpp_stopped_seg_observed_actual}, @{thm lpp_stopped_seg_observed_captured_term}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped prefix dependency" else ();
\<close>
end
