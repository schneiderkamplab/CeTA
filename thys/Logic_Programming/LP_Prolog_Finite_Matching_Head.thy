theory LP_Prolog_Finite_Matching_Head
 imports LP_Prolog_Finite_Anchored_Head
begin

text \<open>Resolution against a head that already matches the selected call
has a finite comparison unifier. This covers observed constructor arguments
without requiring their elements to be ground. Matching is an explicit premise:
finiteness of the call alone does not justify arbitrary rational unification.\<close>

lemma lpp_matching_head_finite_instance:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and matching: "lp_ieval h nu = a"
   and finite: "lpp_finite_term a"
 shows "lpp_finite_term (lp_ieval h rho)"
proof -
 have comparison: "lp_isubst a LPIVar = lp_ieval h nu"
   using matching by simp
 obtain delta where raw: "lp_isubst (lp_isubst a sigma) delta = lp_isubst a LPIVar"
   using mgu comparison unfolding lpc_mgu_resolve_def by blast
 have factor: "lp_isubst (lp_isubst a sigma) delta = a" using raw by simp
 have "lpp_finite_term (lp_isubst a sigma)"
   by (rule lpp_finite_term_substitution_reflects[OF finite factor[symmetric]])
 then show ?thesis using mgu unfolding lpc_mgu_resolve_def by simp
qed

lemma lpp_matching_head_resolution_finite:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and matching: "lp_ieval h nu = a"
   and finite: "lpp_finite_term a"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?nu = "\<lambda>x. if lpp_finite_term (nu x) then nu x else LPIVar x"
 have head: "lpp_finite_term (lp_ieval h nu)" using matching finite by simp
 have comparison: "lp_isubst a LPIVar = lp_ieval h ?nu"
   using lpp_finite_evaluation_restrict[OF head] matching by simp
 have images: "lpp_finite_term (?nu x)" for x by simp
 have body: "lpp_finite_term (lp_ieval t rho)"
   if "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_finite_term_eval)
  fix x assume x: "x\<in>vars_term t"
  show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu comparison that x images])
 qed
 have rest: "lpp_finite_term (lp_isubst t sigma)"
   if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_mgu_continuation_finite[OF mgu comparison _ that])
  fix g t assume "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
  then show "lpp_finite_term (lp_isubst t LPIVar)"
   using continuation by (auto simp: lpp_finite_goals_def list_all_iff)
 qed
 show ?thesis using body rest
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms
     lpp_finite_goal_map list_all_iff)
qed


lemma lpp_checked_matching_head_resolution_finite:
 assumes checked: "lp_cut_check_match a h bindings"
   and mgu: "lpc_mgu_resolve (lp_ieval a eta) gs h bs sigma rho"
   and finite: "lpp_finite_term (lp_ieval a eta)"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have matching: "lp_ieval h (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta) = lp_ieval a eta"
   using checked unfolding lp_cut_check_match_def
   by (simp add: lp_ieval_finite_subst[symmetric])
 show ?thesis by (rule lpp_matching_head_resolution_finite[OF mgu matching finite continuation])
qed

lemma lpp_matching_head_observed_constructor:
 "lp_cut_check_match
   (Fun f [Fun c [Var ''x'', Var ''tail''], Var ''n'', Var ''out''])
   (Fun f [Fun c [Var ''head'', Var ''rest''], Var ''counter'', Var ''result''])
   [(''head'', Var ''x''), (''rest'', Var ''tail''),
    (''counter'', Var ''n''), (''result'', Var ''out'')]"
 by (simp add: lp_cut_check_match_def lp_cut_match_subst_def)

lemma lpp_matching_head_rejects_repeated_alias:
 "\<not> lp_cut_check_match
   (Fun f [Var ''x'', Fun g [Var ''x'']])
   (Fun f [Var ''h'', Var ''h'']) [(''h'', Var ''x'')]"
 by (simp add: lp_cut_check_match_def lp_cut_match_subst_def)

ML \<open>
val checked = [@{thm lpp_matching_head_finite_instance}, @{thm lpp_matching_head_resolution_finite},
 @{thm lpp_checked_matching_head_resolution_finite},
 @{thm lpp_matching_head_observed_constructor},
 @{thm lpp_matching_head_rejects_repeated_alias}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite matching head" else ();
\<close>
end
