theory LP_Prolog_Checked_Caller_Separation
 imports LP_Prolog_Attached_Pair_Intermediate
begin

text \<open>Fresh body variables are separated from observed caller slots by
actual resolution. Both matching heads and checked ground-head effects are
covered. The caller environment is distinct from the source clause valuation.\<close>

lemma lpp_checked_head_acquires_caller_separation:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and body: "x\<in>lpc_body_only_variables (fst (P!c)) (snd (P!c))"
 and leaf: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
 shows "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) sigma) \<and>
   set2_lp_iterm (rho x)\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={}"
proof -
 have effect: "(\<exists>nu. lp_ieval (fst (P!c)) nu=lp_ieval a eta) \<or>
   lp_seg_ground (lp_ieval (fst (P!c)) rho)"
  by (rule lpp_checked_head_actual_return_effect[OF checked known observed mgu])
 show ?thesis
 proof (cases "\<exists>nu. lp_ieval (fst (P!c)) nu=lp_ieval a eta")
  case True
  then obtain nu where matching: "lp_ieval (fst (P!c)) nu=lp_ieval a eta" by blast
  show ?thesis by (rule lpp_attached_matching_acquires_leaf_separation[
    OF mgu matching finite_call finite_rest live body leaf])
 next
  case False
  have ground: "lp_seg_ground (lp_ieval (fst (P!c)) rho)" using effect False by blast
  have support: "set2_lp_iterm (ret slot) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest).
     \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   by (rule lpp_attached_slot_runtime_coverage[OF live])
  have bounded: "lpp_bounded_images {u. vars_term u={}} sigma (set2_lp_iterm (ret slot))"
   by (rule lpp_runtime_ground_head_bounded_images[OF mgu finite_call finite_rest
     lpp_ground_finite_term[OF ground] ground]) (use support in blast)
  have result: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) sigma)"
   by (rule lpp_runtime_leaf_effect_substitute[OF leaf bounded]) simp
  have separation: "set2_lp_iterm (rho x)\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={}"
   by (rule lpp_runtime_fresh_body_separates_observer[OF mgu body finite_rest
      lpp_runtime_leaf_effect_finite[OF leaf] lpp_runtime_leaf_effect_finite[OF result] support])
  show ?thesis using result separation by simp
 qed
qed

lemma lpp_checked_fresh_pair_avoids_caller:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and fresh: "lpp_check_fresh_decomposition (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_resolved: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and leaf: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
 shows "\<exists>n r. rho name_variable=LPIVar n \<and> rho arguments_variable=LPIVar r \<and>
   n\<noteq>r \<and> {n,r}\<inter>set2_lp_iterm (rho input_variable)={} \<and>
   {n,r}\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={} \<and>
   lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) sigma)"
proof -
 obtain n r where runtime_values: "rho name_variable=LPIVar n" "rho arguments_variable=LPIVar r"
 and distinct: "n\<noteq>r"
 and avoid: "n\<notin>set2_lp_iterm (rho input_variable)" "r\<notin>set2_lp_iterm (rho input_variable)"
  using lpp_check_fresh_decomposition_sound[OF fresh mgu finite_resolved] by blast
 have name_body: "name_variable\<in>lpc_body_only_variables (fst (P!c)) (snd (P!c))"
 and args_body: "arguments_variable\<in>lpc_body_only_variables (fst (P!c)) (snd (P!c))"
  using fresh by (auto simp: lpp_check_fresh_decomposition_def)
 have name: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) sigma) \<and>
   set2_lp_iterm (rho name_variable)\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={}"
  by (rule lpp_checked_head_acquires_caller_separation[
    OF checked known observed mgu finite_call finite_rest live name_body leaf])
 have args: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (ret slot) sigma) \<and>
   set2_lp_iterm (rho arguments_variable)\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={}"
  by (rule lpp_checked_head_acquires_caller_separation[
    OF checked known observed mgu finite_call finite_rest live args_body leaf])
 show ?thesis by (intro exI[of _ n] exI[of _ r]) (use runtime_values distinct avoid name args in auto)
qed

ML \<open>
val checked = @{thms lpp_checked_head_acquires_caller_separation lpp_checked_fresh_pair_avoids_caller};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked caller separation" else ();
\<close>
end
