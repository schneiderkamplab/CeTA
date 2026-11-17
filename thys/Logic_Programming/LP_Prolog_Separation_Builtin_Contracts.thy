theory LP_Prolog_Separation_Builtin_Contracts
 imports LP_Prolog_Separation_Empty_Test LP_Prolog_Functor_Simple_Control
begin

theorem lpp_separation_control_test_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"

 and empty_targets: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a) \<Longrightarrow>
   lpcl_target (if holds then yes else no)<length separation_contexts \<and>
   separation_contexts!lpcl_target (if holds then yes else no)=[]"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) ev ys \<Longrightarrow> J (lpc_return_eval eta ss) \<Longrightarrow> J ys"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts
   nd F ss source_context source_functors f a gs active saved yes no"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix ev ys assume step: "?T (lpc_return_eval eta ss) ev ys"
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta ss))"
   by (rule lpp_functor_term_test_domain[OF check])
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    (lpc_return_eval eta ss) ev ys"
   using step supported by (simp add: lpp_domain_answers_def)
  obtain v swaps where silent: "ev=None" and strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
   and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) v"
   using lpp_empty_separation_term_test_sound[OF compatible transfer check empty_targets known free observed functors actual] by blast
  have child: "lp_answer_contract ?T ys (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lower[OF strict _ stable[OF step invariant]])
    (use rep in \<open>auto simp: lpp_premised_functor_module_rep_def\<close>)
  have lifted: "lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  show "(\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   using silent lifted by simp
 qed
qed

theorem lpp_separation_control_is_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFIs result_var middle facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"

 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_empty: "separation_contexts!lpcl_target middle=[]"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and normalized: "\<And>f. J (lpc_return_eval eta ss) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_observed_functor_link T facts fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors a e gs active saved result_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
  by (rule lpp_functor_is_check_domain[OF checked[unfolded shape] known observed])
 have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
  using check by (auto simp: lpp_check_observed_functor_link_def lpp_check_evaluation_functor_link_def
    lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 show ?thesis
 proof (rule lpp_functor_observed_is_domain_contract[OF compatible transfer check domain known free observed functors invariant normalized])
  fix rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  let ?v = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  assume strict: "(?t,?v)\<in>(lp_ild Q)\<^sup>+"
   and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
  have child_conditions: "lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
   using separation_bound separation_empty by (simp add: lpp_separation_node_conditions_def)
  have rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
    (lpc_return_eval rho (states!lpcl_target middle)) ?v"
   by (rule lpp_premised_functor_module_intro[where node_conditions="lpp_separation_node_conditions separation_contexts", OF bounds child_known child_free child_observed child_conditions child_functors])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep child_invariant]])
 qed
qed

lemma lpp_separation_test_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"
 and empty_targets: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground (nds!i)) a) \<Longrightarrow>
   lpcl_target (if holds then yes else no)<length separation_contexts \<and>
   separation_contexts!lpcl_target (if holds then yes else no)=[]"
 and stable: "\<And>eta ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow> J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"

 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) J returned arity i"
 unfolding lpp_premised_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_separation_control_test_contract[where J=J, OF compatible transfer checked shape empty_targets])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by (rule stable; assumption)
 subgoal by blast
 done

lemma lpp_separation_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFIs result_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_empty: "separation_contexts!lpcl_target middle=[]"
 and normalized: "\<And>eta f. J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"

 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) J returned arity i"
 unfolding lpp_premised_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_separation_control_is_contract[where J=J, OF compatible transfer checked shape separation_bound separation_empty])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by (rule normalized; assumption)
 subgoal by blast
 done

ML \<open>
val checked = @{thms lpp_separation_control_test_contract lpp_separation_control_is_contract
 lpp_separation_test_node_contract lpp_separation_is_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation builtin contracts" else ();
\<close>
end
