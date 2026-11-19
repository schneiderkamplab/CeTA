theory LP_Prolog_Acquired_Univ_Link
 imports LP_Prolog_Acquired_Univ_Witness_Product LP_Prolog_Parameter_Coordinate_Link
begin

text \<open>Transport the complete acquired runtime through a checked link.
State equality supplies all normalization entry coordinates in the same target
valuation; payload and saved correspondence are not separate assumptions. The
source evaluation identity remains an acquisition-resolution obligation.\<close>

lemma lpp_acquired_univ_link_correspondence:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functors
   nd ss G K eqs F source_context source_functors link"
 and equations: "lp_equations eqs source_env"
 and old: "map source_env (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K source_env"
 and free: "lpc_free_knowledge (set F) source_env"
 and observed: "lpp_stable_context_holds operation SP source_context source_env"
 and functor_facts: "list_all (lpp_functor_fact_holds names source_env) source_functors"
 and swaps: "lpcl_swaps link=[]"
 and source_shape: "lpc_return_eval source_env ss=
   (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'')
     [rho x,LPIFun pair_symbol [rho y,rho z]])#pending),helper_env)#helper_saved"
 and target_shape: "states!lpcl_target link=
   (LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
     [input_template,Fun pair_symbol [Var output_name,Var output_args]])#source_goals),source_active)#source_saved"
 shows "\<exists>nu.
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target link)) nu \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target link) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target link) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q \<and>
   lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z \<and>
   pending=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals \<and>
   helper_env=lpc_return_env source_active nu \<and> helper_saved=lpc_return_eval nu source_saved"
proof -
 obtain nu where exact: "lpc_return_eval source_env ss=lpc_return_scope_word (lpcl_swaps link)
   (lpc_return_eval nu (states!lpcl_target link))"
 and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu"
 and child_free: "lpc_free_knowledge (set (Fs!lpcl_target link)) nu"
 and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target link) nu"
 and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
 and child_functors: "list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target link)"
  using lpp_stable_functor_link_with_parameter_facts[where J="\<lambda>_. True",
   OF compatible program checked equations old known free observed functor_facts] by blast
 have correspondence: "lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z \<and>
   pending=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals \<and>
   helper_env=lpc_return_env source_active nu \<and> helper_saved=lpc_return_eval nu source_saved"
  using exact[unfolded source_shape swaps target_shape] by (auto simp: lpc_return_eval_def)
 show ?thesis by (rule exI[of _ nu])
  (use child_known child_free child_context child_functors edge correspondence in blast)
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_link_correspondence};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired link correspondence" else ();
val _ = writeln "ACQUIRED_UNIV_LINK_KERNEL_CHECKED";
\<close>
end
