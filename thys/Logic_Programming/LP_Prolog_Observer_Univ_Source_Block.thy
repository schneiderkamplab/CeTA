theory LP_Prolog_Observer_Univ_Source_Block
 imports LP_Prolog_Observer_Fresh_Univ_Contract
begin

fun lpp_observer_equality_frame where
 "lpp_observer_equality_frame ((LPCGoals (LPCUnify a b#gs),env)#saved) = True"
| "lpp_observer_equality_frame ss = False"

lemma lpp_checked_univ_source_block:
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
 and equalities: "\<And>xs t ev ys.
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) xs t \<Longrightarrow>
   lpp_finite_execution xs \<Longrightarrow> lpp_observer_equality_frame xs \<Longrightarrow>
   lpc_answer_transition P xs ev ys \<Longrightarrow>
   \<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u \<and> lpp_finite_execution ys"
 shows "event=None \<and> (result=[] \<or> (\<exists>u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result u))"
proof -
 let ?C = "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)"
 let ?start = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
 have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved"
  using checked by (simp add: lpp_check_univ_evaluation_context_def)
 have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
  using checked by (auto simp: lpp_check_univ_evaluation_context_def lpp_check_evaluation_functor_link_def
   lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 have actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [lp_ieval input_template eta,lp_ieval requested eta])#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event result"
  using step by (simp add: shape lpc_return_eval_def)
 have silent: "event=None"
  using lpp_observer_univ_actual_normalized_path[OF domain actual] by blast
 have finish: "\<exists>u. (?start,u)\<in>(lp_ild Q)\<^sup>+ \<and> ?C result u" if nonempty: "result\<noteq>[]"
 proof -
  obtain f ts where input: "lp_ieval input_template eta=LPIFun f ts"
  and first: "lpc_answer_transition P
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) None
   ((LPCGoals (LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
  and second: "lpc_answer_transition P
   ((LPCGoals (LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) None result"
   using lpp_observer_univ_actual_normalized_path[OF domain actual] nonempty by blast
  let ?normalized = "((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
  let ?pair = "((LPCGoals (LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
  obtain rho where exact: "?normalized=lpc_return_eval rho (states!lpcl_target middle)"
  and edge: "(?start,[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
  and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
  and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
  and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
  and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
  and child_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
   using lpp_checked_univ_normalization_witness[OF compatible program checked separation_bound
    separation_transport separation_initialized known free context_held functors input] by blast
  let ?initial_subject = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  have rep: "?C ?normalized ?initial_subject"
   unfolding exact by (rule lpp_premised_functor_module_intro[where node_conditions="lpp_separation_node_conditions separation_contexts", OF bounds child_known child_free child_observed child_separation child_functors])
  have finite_normalized: "lpp_finite_execution ?normalized"
   by (rule lpp_finite_execution_univ_normalization[OF input finite[unfolded shape]])
  have first_frame: "lpp_observer_equality_frame ?normalized" by simp
  obtain t where first_path: "(?initial_subject,t)\<in>(lp_ild Q)\<^sup>+"
  and pair_rep: "?C ?pair t" and finite_pair: "lpp_finite_execution ?pair"
   using equalities[OF rep finite_normalized first_frame first] by blast
  have pair_frame: "lpp_observer_equality_frame ?pair" by simp
  obtain u where second_path: "(t,u)\<in>(lp_ild Q)\<^sup>+" and final_rep: "?C result u"
   using equalities[OF pair_rep finite_pair pair_frame second] by blast
  have strict: "(?start,u)\<in>(lp_ild Q)\<^sup>+"
   using edge first_path second_path by (meson r_into_trancl trancl_trans)
  show ?thesis using strict final_rep by blast
 qed
 show ?thesis using silent finish by blast
qed

ML \<open>
val checked = @{thms lpp_checked_univ_source_block};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked univ source block" else ();
\<close>
end
