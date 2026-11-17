theory LP_Prolog_Univ_Separation_Contract
 imports LP_Prolog_Univ_Separation_Initialization LP_Prolog_Finite_Functor_Normalization
begin

theorem lpp_univ_separation_control_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFUniv value_var name_var args_var middle facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),active)#saved)"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport initialized_separation
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 and separation_initialized: "\<And>f ts. lp_ieval a eta=LPIFun f ts \<Longrightarrow>
   list_all (lpp_separation_holds
     (eta(value_var:=LPIFun f ts,name_var:=LPIFun (names f) [],args_var:=lpp_argument_list ts)))
     initialized_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and normalized: "\<And>f ts. lp_ieval a eta=LPIFun f ts \<Longrightarrow> J (lpc_return_eval eta ss) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval b eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_univ_evaluation_context T facts fuel Q nds states contexts functor_contexts Fs nd F ss
   source_context source_functors a b gs active saved value_var name_var args_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
  using check by (auto simp: lpp_check_univ_evaluation_context_def lpp_check_evaluation_functor_link_def
    lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 show ?thesis
 proof (rule lpp_univ_separation_context_contract[OF compatible transfer check separation_bound separation_transport separation_initialized known free observed functors _ _ _ invariant normalized])
  show "(''2:=..'',2)\<in>lpp_builtin_signature" by (simp add: lpp_builtin_signature_def)
  show "\<And>x y. lpp_univ_view_domain x y \<Longrightarrow> lpp_univ_source_domain ''2:=..'' [x,y]"
   by (rule lpp_univ_source_domain_covered)
  show "\<And>x y out. lpp_univ_view_domain x y \<Longrightarrow>
    lpp_univ_source_builtin names operation ''2:=..'' [x,y] out \<Longrightarrow> lpp_univ_view_outcome names x y out"
   by (rule lpp_univ_source_outcome_covered)
 next
  fix rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  let ?v = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  assume edge: "(?t,?v)\<in>lp_ild Q"
   and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and child_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
   and child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
  have strict: "(?t,?v)\<in>(lp_ild Q)\<^sup>+" by (rule r_into_trancl[OF edge])
  have rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
    (lpc_return_eval rho (states!lpcl_target middle)) ?v"
   by (rule lpp_premised_functor_module_intro[where node_conditions="lpp_separation_node_conditions separation_contexts", OF bounds child_known child_free child_observed child_separation child_functors])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep child_invariant]])
 qed
qed

ML \<open>
val checked = @{thms lpp_univ_separation_control_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ separation control contract" else ();
\<close>
end
