theory LP_Prolog_Observer_Univ_Witness
 imports LP_Prolog_Observer_Arithmetic_Normalization
begin

text \<open>Expose the same initialized univ link witness used by the established
source contract. The target valuation jointly satisfies ordinary context,
functor observation and separation facts. The reflexive equality and requested
pair equality both remain in the normalized source state.\<close>

lemma lpp_checked_univ_normalization_witness:
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
 and input: "lp_ieval input_template eta=LPIFun f ts"
 shows "\<exists>rho.
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)
      =lpc_return_eval rho (states!lpcl_target middle) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<and>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<and>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<and>
   lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
proof -
 let ?synthetic = "lpp_univ_projected_state input_template requested gs active saved value_variable name_variable arguments_variable"
 let ?observed = "LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors"
 let ?G = "lpp_univ_projected_ground (lpcn_ground nd) input_template name_variable arguments_variable"
 have shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved)"
 and init: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors"
 and dom_check: "lpp_check_univ_view_domain F input_template requested"
 and fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
      x\<notin>set (lpcn_vars nd) \<and> x\<notin>set (lpcn_ground nd) \<and> x\<notin>set F \<and>
      list_all (lpp_fresh_guard x) (lpcn_guards nd)"
 and swaps: "lpcl_swaps middle=[]"
 and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ?synthetic ?G
    (lpcn_guards nd) [] F (lpp_context_with_equations source_context [(input_template,Var value_variable)]) ?observed middle"
  using checked by (auto simp: lpp_check_univ_evaluation_context_def)
  let ?nu = "eta(value_variable:=LPIFun f ts,name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
  have distinct: "name_variable\<noteq>arguments_variable" using init by (simp add: lpp_check_univ_initialization_def)
  have knowledge_fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
      x\<notin>set (lpcn_ground nd) \<and> x\<notin>set F \<and> list_all (lpp_fresh_guard x) (lpcn_guards nd)"
   using fresh by auto
  have base_known: "lp_cut_knowledge (insert name_variable (set (lpcn_ground nd))) (lpcn_guards nd) ?nu"
  and base_free: "lpc_free_knowledge (set F) ?nu"
   using lpp_univ_initialization_knowledge[OF knowledge_fresh distinct known free, of f ts names] by auto
  have extended_known: "lp_cut_knowledge (set ?G) (lpcn_guards nd) ?nu"
  proof (cases "vars_term input_template \<subseteq> set (lpcn_ground nd)")
   case True
   have ground_input: "lp_seg_ground (lp_ieval input_template eta)"
    using known True by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
   have ground: "lp_seg_ground (LPIFun f ts)" using ground_input input by simp
   show ?thesis using lpp_univ_initialization_ground_arguments[OF knowledge_fresh distinct known free ground, of names]
    by (simp add: lpp_univ_projected_ground_def True insert_commute)
  next
   case False then show ?thesis using base_known by (simp add: lpp_univ_projected_ground_def)
  qed
  have old: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
   using fresh by (auto intro!: map_cong)
  have context_extended: "lpp_stable_context_holds operation SP source_context ?nu"
   by (rule lpp_univ_stable_initialization_sound(2)[OF init input context_held functors])
  have initialized_equality: "lp_ieval input_template ?nu=lp_ieval (Var value_variable) ?nu"
   by (rule lpp_univ_stable_initialization_sound(4)[OF init input context_held functors])
  have initialized_context: "lpp_stable_context_holds operation SP
    (lpp_context_with_equations source_context [(input_template,Var value_variable)]) ?nu"
   using context_extended initialized_equality
   by (cases source_context) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)
  have observed_extended: "list_all (lpp_functor_fact_holds names ?nu) ?observed"
   by (rule lpp_univ_stable_initialization_sound(3)[OF init input context_held functors])
  have enriched_context: "lpp_stable_context_holds operation SP (lpp_functor_shape_context
    (lpp_context_with_equations source_context [(input_template,Var value_variable)]) ?observed) ?nu"
    by (rule lpp_functor_shape_context_stable[OF initialized_context observed_extended])
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  have base_link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?synthetic ?G
    (lpcn_guards nd) [] F (lpp_functor_shape_context
      (lpp_context_with_equations source_context [(input_template,Var value_variable)]) ?observed) middle"
    using link by (simp add: lpp_check_evaluation_functor_link_def)
  have transported_functors: "list_all (lpp_functor_fact_holds names
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings middle) x) ?nu))
      (functor_contexts!lpcl_target middle)"
    by (rule lpp_check_functor_equation_transport_sound[where fuel=fuel, OF _ equations observed_extended])
      (use link in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
  have transported_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target middle)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings middle) x) ?nu)"
    by (rule lpp_separation_node_transport[OF separation_bound separation_transport separation_initialized[OF input]])
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
   and target_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and target_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and target_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and target_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and target_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
   and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
   using lpp_stable_link_witness_with_observation[where J="\<lambda>rho.
      list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<and>
      lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho",
      OF compatible program base_link equations old extended_known base_free enriched_context
        conjI[OF transported_functors transported_separation]]
   by (simp add: swaps) blast
  have represented: "lpc_return_eval ?nu ?synthetic =
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
   by (rule lpp_univ_stable_initialized_state[OF init[unfolded shape] input context_held functors])
 note exact = HOL.trans[OF represented[symmetric] same]
 show ?thesis by (rule exI[of _ rho])
  (use exact edge target_known target_free target_context target_functors target_separation in \<open>blast\<close>)
qed

ML \<open>
val checked = @{thms lpp_checked_univ_normalization_witness};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer univ witness" else ();
\<close>
end
