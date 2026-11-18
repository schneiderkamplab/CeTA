theory LP_Prolog_Observer_Univ_Module_Block
 imports LP_Prolog_Observer_Equality_Check
begin

lemma lpp_checked_univ_module_block:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport initialized_separation
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 and separation_initialized: "\<And>f ts. lp_ieval input_template eta=LPIFun f ts \<Longrightarrow>
   list_all (lpp_separation_holds
     (eta(value_variable:=LPIFun f ts,name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)))
     initialized_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"

 and domain: "lpp_univ_view_domain (lp_ieval input_template eta) (lp_ieval requested eta)"
 and finite: "lpp_finite_execution (lpc_return_eval eta ss)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) event result"
 and source_program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 shows "event=None \<and> (result=[] \<or> (\<exists>u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result u))"
proof (rule lpp_checked_univ_source_block[OF compatible program checked separation_bound separation_transport
 separation_initialized known free context_held functors domain finite step])
 fix xs t ev ys
 assume rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) xs t"
 and finite: "lpp_finite_execution xs"
 and frame: "lpp_observer_equality_frame xs"
 and step: "lpc_answer_transition P xs ev ys"
 show "\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u \<and> lpp_finite_execution ys"
 proof -
  have simulated: "ev=None \<and> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u \<and> lpp_finite_execution ys)"
   apply (rule lpp_observer_equality_module_step[OF source_program _ rep finite frame step])
   subgoal for i eta by (rule coverage[of i eta]) assumption+
   done
  show ?thesis using simulated by blast
 qed
qed

ML \<open>
val checked = @{thms lpp_checked_univ_module_block lpp_checked_separation_reflexive_node_simulation
 lpp_checked_separation_pair_node_simulation lpp_separation_pair_missing_context_rejected
 lpp_separation_pair_missing_fact_rejected lpp_separation_pair_missing_failure_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked univ module block" else ();
\<close>
end
