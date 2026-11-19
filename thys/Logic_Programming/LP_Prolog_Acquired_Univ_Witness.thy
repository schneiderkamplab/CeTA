theory LP_Prolog_Acquired_Univ_Witness
 imports LP_Prolog_Acquired_Univ_Entry LP_Prolog_Univ_Separation_Initialization
begin

text \<open>Initialize free outputs and pair separation from actual matching
acquisition, then use the checked normalization link to obtain one common target
valuation. Source knowledge, contexts and the coordinate identities remain
explicit assembly obligations.\<close>

lemma lpp_acquired_univ_normalization_witness:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport [LPPSeparate (Fun pair_symbol [Var output_name,Var output_args])
     (Fun pair_symbol [Var name_variable,Var arguments_variable])]
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 and acquired: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve call pending h bs sigma acquired_env"
 and matching: "lp_ieval h witness=call"
 and finite_call: "lpp_finite_term call"
 and input_coordinate: "lp_ieval input_template eta=acquired_env x"
 and name_coordinate: "eta output_name=acquired_env y"
 and args_coordinate: "eta output_args=acquired_env z"
 and free_coverage: "set F \<subseteq> {output_name,output_args}"
 and requested: "requested=Fun pair_symbol [Var output_name,Var output_args]"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
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
 have finite_head: "lpp_finite_term (lp_ieval h acquired_env)"
  by (rule lpp_matching_head_finite_instance[OF mgu matching finite_call])
 have finite_subst: "lpp_finite_term (lp_isubst call sigma)"
  using finite_head mgu by (simp add: lpc_mgu_resolve_def)
 obtain u v where vars: "acquired_env y=LPIVar u" "acquired_env z=LPIVar v"
 and distinct: "u\<noteq>v"
 and fresh: "u\<notin>set2_lp_iterm (acquired_env x)" "v\<notin>set2_lp_iterm (acquired_env x)"
  using lpp_check_fresh_univ_clause_sound[OF acquired mgu finite_subst] by blast
 have free_pair: "lpc_free_knowledge {output_name,output_args} eta"
  using vars name_coordinate args_coordinate distinct
  by (auto simp: lpc_free_knowledge_def inj_on_def)
 have free: "lpc_free_knowledge (set F) eta"
  using free_pair free_coverage unfolding lpc_free_knowledge_def
  by (meson subsetD inj_on_subset)
 have separated: "list_all (lpp_separation_holds eta)
   [LPPSeparate input_template (Var output_name),LPPSeparate input_template (Var output_args)]"
  using fresh vars by (auto simp: input_coordinate name_coordinate args_coordinate)
 have shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
   [input_template,Fun pair_symbol [Var output_name,Var output_args]])#gs),active)#saved)"
 and init: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
   [input_template,Fun pair_symbol [Var output_name,Var output_args]])#gs),active)#saved)
   source_context source_functors"
  using checked by (auto simp: lpp_check_univ_evaluation_context_def requested)
 have initialized: "list_all (lpp_separation_holds
   (eta(value_variable:=LPIFun g us,name_variable:=LPIFun (names g) [],arguments_variable:=lpp_argument_list us)))
   [LPPSeparate (Fun pair_symbol [Var output_name,Var output_args])
     (Fun pair_symbol [Var name_variable,Var arguments_variable])]"
  if val_eq: "lp_ieval input_template eta=LPIFun g us" for g us
  using lpp_univ_initializes_pair_separation[OF init val_eq context_held functors separated] by simp
 show ?thesis
  by (rule lpp_checked_univ_normalization_witness[OF compatible program checked separation_bound
    separation_transport initialized known free context_held functors input])
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_normalization_witness};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired normalization witness" else ();
val _ = writeln "ACQUIRED_UNIV_WITNESS_KERNEL_CHECKED";
\<close>
end
