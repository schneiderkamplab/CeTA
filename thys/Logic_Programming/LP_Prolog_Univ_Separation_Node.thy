theory LP_Prolog_Univ_Separation_Node
 imports LP_Prolog_Univ_Separation_Contract
begin

lemma lpp_finite_univ_separation_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts)"
 and shape: "states!i=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved)"
 and incoming: "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
 and bound: "lpcl_target middle<length separation_contexts"
 and transport: "lpp_check_separation_transport
   [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
 unfolding lpp_premised_functor_node_contract_def
proof (intro allI impI)
 fix eta
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and sn: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) vs v \<longrightarrow> lpp_finite_execution vs \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 have init: "lpp_check_univ_initialization value_var name_var args_var a (states!i) (contexts!i) (functor_contexts!i)"
   using checked by (auto simp: shape lpp_check_functor_source_action_def lpp_check_univ_evaluation_context_def)
 have separated: "list_all (lpp_separation_holds eta) [LPPSeparate a output_name,LPPSeparate a output_args]"
   using incoming conditions unfolding lpp_separation_node_conditions_def list_all_iff by blast
 have initialized: "list_all (lpp_separation_holds
     (eta(value_var:=LPIFun f ts,name_var:=LPIFun (names f) [],args_var:=lpp_argument_list ts)))
     [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]"
   if input: "lp_ieval a eta=LPIFun f ts" for f ts
   using lpp_univ_initializes_pair_separation[OF init[unfolded shape] input observed functors separated] by simp
 show "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
   (\<lambda>rho. [(returned,map rho [0..<arity])])"
 apply (rule lpp_univ_separation_control_contract[where J=lpp_finite_execution and eta=eta and names=names, OF compatible transfer checked shape bound transport initialized
   known free observed functors finite])
 subgoal by assumption
 subgoal by (rule lpp_finite_execution_univ_normalization) (use shape in auto)
 subgoal using lower by blast
 done
qed

ML \<open>
val checked = @{thms lpp_finite_univ_separation_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ separation node contract" else ();
\<close>
end
