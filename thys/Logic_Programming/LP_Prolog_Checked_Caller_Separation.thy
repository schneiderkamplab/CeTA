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

ML \<open>
val checked = @{thms lpp_checked_head_acquires_caller_separation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked caller separation" else ();
\<close>
end
