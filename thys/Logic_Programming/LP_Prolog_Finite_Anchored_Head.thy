theory LP_Prolog_Finite_Anchored_Head
 imports LP_Prolog_Finite_Ground_Template
begin

lemma lpp_finite_evaluation_restrict:
 assumes finite: "lpp_finite_term (lp_ieval h rho)"
 shows "lp_ieval h (\<lambda>x. if lpp_finite_term (rho x) then rho x else LPIVar x) = lp_ieval h rho"
 using finite by (induct h) (auto simp: list_all_iff intro!: map_cong)

lemma lpp_finite_instance_resolution_finite:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and head: "lpp_finite_term (lp_ieval h rho)"
   and finite: "lpp_finite_term a"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?tau = "\<lambda>x. if lpp_finite_term (sigma x) then sigma x else LPIVar x"
 let ?nu = "\<lambda>x. if lpp_finite_term (rho x) then rho x else LPIVar x"
 have images: "lpp_finite_term (?tau x)" "lpp_finite_term (?nu x)" for x by simp_all
 have equation: "lp_isubst a sigma=lp_ieval h rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have substituted: "lpp_finite_term (lp_isubst a sigma)" using equation head by simp
 have comparison: "lp_isubst a ?tau=lp_ieval h ?nu"
   using lpp_finite_substitution_restrict[OF finite substituted]
     lpp_finite_evaluation_restrict[OF head] equation by simp
 have body: "lpp_finite_term (lp_ieval t rho)" if "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_finite_term_eval)
  fix x assume x: "x\<in>vars_term t"
  show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu comparison that x images(2)])
 qed
 have rest: "lpp_finite_term (lp_isubst t sigma)" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_mgu_continuation_finite[OF mgu comparison _ that])
  fix g t assume "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
  then have "lpp_finite_term t" using continuation by (auto simp: lpp_finite_goals_def list_all_iff)
  then show "lpp_finite_term (lp_isubst t ?tau)" by (rule lpp_finite_term_substitute[OF _ images(1)])
 qed
 show ?thesis using body rest
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms lpp_finite_goal_map list_all_iff)
qed

definition lpp_check_anchored_head where
 "lpp_check_anchored_head G actuals hs =
   (\<Union>(vars_term ` set hs) \<subseteq>
    \<Union>(vars_term ` set (map (\<lambda>i. hs!i)
      (filter (\<lambda>i. vars_term (actuals!i) \<subseteq> set G) [0..<length hs]))))"

lemma lpp_checked_anchored_head_ground:
 fixes eta :: "'v \<Rightarrow> ('f,string) lp_iterm"
   and rho sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes checked: "lpp_check_anchored_head G actuals hs"
   and lengths: "length actuals=length hs"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
 shows "lp_seg_ground (lp_ieval (Fun f hs) rho)"
proof (simp only: lp_seg_ground_eval, intro ballI)
 fix x assume "x\<in>vars_term (Fun f hs)"
 then obtain i where i: "i < length hs" "vars_term (actuals ! i) \<subseteq> set G" "x \<in> vars_term (hs ! i)"
   using checked by (auto simp: lpp_check_anchored_head_def)
 have actual: "lp_seg_ground (lp_ieval (actuals!i) eta)"
   using known i(2) by (auto simp: lp_seg_ground_eval)
 have eq: "lp_isubst (lp_ieval (actuals!i) eta) sigma=lp_ieval (hs!i) rho"
   using arg_cong[OF equation, of "\<lambda>xs. xs!i"] i(1) lengths by simp
 have "lp_seg_ground (lp_ieval (hs!i) rho)"
   using eq actual by (metis lp_seg_ground_subst)
 then show "lp_seg_ground (rho x)" using i(3) by (simp add: lp_seg_ground_eval)
qed

ML \<open>
val checked = [@{thm lpp_finite_instance_resolution_finite}, @{thm lpp_checked_anchored_head_ground}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite anchored head transport" else ();
\<close>
end
