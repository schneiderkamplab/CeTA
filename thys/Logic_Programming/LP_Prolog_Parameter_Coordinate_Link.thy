theory LP_Prolog_Parameter_Coordinate_Link
 imports LP_Prolog_Stable_Functor_Link LP_Prolog_Runtime_Parameter
begin

text \<open>Preserve additional parameter and positive-branch facts in the same
valuation as the ordinary context and functor observations. Coordinate checks
justify the extra premise; no annotation is discharged by a module reference.\<close>

lemma lpp_checked_parameter_branch_coordinates:
 assumes parameter_map: "lpp_check_parameter_coordinate before_parameter after_parameter bindings"
 and free_map: "lpp_check_parameter_coordinate before_selected after_selected bindings"
 and tracked: "lpp_runtime_parameter c (lp_ieval before_parameter eta)"
 and selected: "\<exists>x. lp_ieval before_selected eta=LPIVar x"
 shows "lpp_runtime_parameter c
    (lp_ieval after_parameter (\<lambda>x. lp_ieval (bindings x) eta)) \<and>
  (\<exists>x. lp_ieval after_selected (\<lambda>x. lp_ieval (bindings x) eta)=LPIVar x)"
 using lpp_checked_parameter_coordinate[OF parameter_map tracked]
  lpp_checked_parameter_coordinate_value[OF free_map, of eta] selected by auto

lemma lpp_stable_functor_link_with_parameter_facts:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
    and extra: "J (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_stable_context_holds operation SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q \<and>
    list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e) \<and> J nu"
proof -
 have enriched: "lpp_stable_context_holds operation SP (lpp_functor_shape_context source_context source_functors) eta'"
  by (rule lpp_functor_shape_context_stable[OF observed functors])
 have base: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F
    (lpp_functor_shape_context source_context source_functors) e"
  using checked by (simp add: lpp_check_evaluation_functor_link_def)
 have transported: "list_all (lpp_functor_fact_holds names
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'))
    (functor_contexts!lpcl_target e)"
  by (rule lpp_check_functor_equation_transport_sound[where fuel=fuel, OF _ equations functors])
   (use checked in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
 show ?thesis
  by (rule lpp_stable_link_witness_with_observation[where J="\<lambda>nu. list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e) \<and> J nu",
    OF compatible program base equations old known free enriched])
    (use transported extra in blast)
qed

ML \<open>
val checked = @{thms lpp_checked_parameter_branch_coordinates
 lpp_stable_functor_link_with_parameter_facts};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter coordinate link" else ();
\<close>
end
