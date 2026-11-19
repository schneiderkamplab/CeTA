theory LP_Prolog_Observer_Runtime_Parameter_Equality
 imports LP_Prolog_Observer_Parameter_Equality_Contract LP_Prolog_Parameter_Var_Branch
begin

text \<open>The selected free variable is obtained from the actual positive var
branch. It is not inferred from an opaque guard or the retained free table.
The restricted invariant and the recursive lower contract remain explicit.\<close>

lemma lpp_checked_observer_runtime_parameter_equality_contract:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs helper_payload helper_saved k l next mode outputs source_context source_functors yes no"
    and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpcl_target yes<length separation_contexts \<and>
      lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
        (lp_cut_instance_subst (lpcl_bindings yes))"
    and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpcl_target no<length separation_contexts \<and>
      lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
        (lp_cut_instance_subst (lpcl_bindings no))"
    and success_separation: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
    and failure_separation: "list_all (lpp_separation_holds eta) no_separation"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and ground: "vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
 and binding: "lpp_check_parameter_replacement parameter f g b"
 and selected_free: "lp_ieval a eta=LPIVar x"
 and tracked_parameter: "lpp_runtime_parameter initial_parameter (eta parameter)"
 and shape: "runtime=(LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),helper_payload)#helper_saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 obtain current_parameter where parameter: "eta parameter=lp_ieval current_parameter LPIVar"
 and returned_parameter: "lpp_parameter_return initial_parameter current_parameter"
 and ground_parameter: "vars_term initial_parameter={}"
  using tracked_parameter by (auto simp: lpp_runtime_parameter_def)
 obtain replacement_template where replacement: "lp_ieval b eta=lp_ieval replacement_template LPIVar"
 and allowed: "replacement_template\<in>lpp_parameter_leaf_templates f g initial_parameter"
  using lpp_checked_parameter_replacement_sound[where eta=eta and d=current_parameter and c=initial_parameter, OF binding parameter returned_parameter] by blast
 have ground_templates: "vars_term v={}" if "v\<in>lpp_parameter_leaf_templates f g initial_parameter" for v
  by (rule lpp_parameter_leaf_templates_ground[OF ground_parameter that])
 show ?thesis by (rule lpp_checked_observer_allowed_equality_contract[OF
  compatible program checked success_transport failure_transport success_separation failure_separation
  known free observed functors ground selected_free replacement allowed ground_templates
  shape represented covered invariant lower])
qed

ML \<open>
val checked = @{thms lpp_checked_observer_runtime_parameter_equality_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted runtime parameter equality" else ();
\<close>
end
