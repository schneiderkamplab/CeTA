theory LP_Prolog_Checked_Univ_Caller_Path
 imports LP_Prolog_Checked_Caller_Separation
begin

text \<open>The successful local path retains the resolution substitution and
both normalized unifiers. This theorem supplies the caller effect for that
path; failed alternatives and complete source routing remain separate checks.\<close>

lemma lpp_checked_fresh_univ_caller_leaf:
 fixes SP :: "string lpp_success_clause list"
 and tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and fresh: "lpp_check_fresh_decomposition (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and resolution: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) resolution_subst rho"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_resolved: "lpp_finite_term (lp_isubst (lp_ieval a eta) resolution_subst)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and leaf: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
 and input: "rho input_variable=LPIFun f ts"
 and finite_arguments: "list_all lpp_finite_term ts"
 and first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>v. lp_isubst (ret v) resolution_subst))) rest)) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending_goals @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t (\<lambda>v. lp_isubst (ret v) resolution_subst)) sigma)) rest) tau"
 shows "lpp_runtime_leaf_effect {u. vars_term u={}} shape
   (lp_isubst (lp_isubst (lp_isubst (ret slot) resolution_subst) sigma) tau)"
proof -
 obtain n r where output_name: "rho name_variable=LPIVar n"
 and output_arguments: "rho arguments_variable=LPIVar r"
 and distinct: "n\<noteq>r"
 and avoid: "{n,r}\<inter>set2_lp_iterm (rho input_variable)={}"
 and protected: "{n,r}\<inter>set2_lp_iterm (lp_isubst (ret slot) resolution_subst)={}"
 and preserved: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) resolution_subst)"
  using lpp_checked_fresh_pair_avoids_caller[
    OF checked fresh known observed resolution finite_call finite_resolved finite_rest live leaf] by blast
 have first_actual: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar n,LPIVar r])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>v. lp_isubst (ret v) resolution_subst))) rest)) sigma"
  using first by (simp only: output_name output_arguments)
 have second_actual: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar n,LPIVar r]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending_goals @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t (\<lambda>v. lp_isubst (ret v) resolution_subst)) sigma)) rest) tau"
  using second by (simp only: output_name output_arguments)
 show ?thesis
  apply (rule lpp_attached_normalized_univ_preserves_return_slot[
    where eta="\<lambda>v. lp_isubst (ret v) resolution_subst" and v=slot and gs=rest
    and pending_goals=pending_goals and sigma=sigma and tau=tau and names=names
    and f=f and ts=ts and x=n and y=r,
    OF first_actual second_actual preserved finite_arguments distinct _ _ protected live])
  using avoid input by auto
qed

ML \<open>
val checked = @{thms lpp_checked_fresh_univ_caller_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked univ caller path" else ();
\<close>
end
