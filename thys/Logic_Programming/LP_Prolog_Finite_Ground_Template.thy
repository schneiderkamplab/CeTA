theory LP_Prolog_Finite_Ground_Template
 imports LP_Prolog_Finite_Partial_Head LP_Prolog_Finite_Direct_State
begin

lemma lpp_finite_substitution_restrict:
 assumes "lpp_finite_term t" "lpp_finite_term (lp_isubst t sigma)"
 shows "lp_isubst t (\<lambda>x. if lpp_finite_term (sigma x) then sigma x else LPIVar x) = lp_isubst t sigma"
 using assms
 by (induct rule: lpp_finite_term.induct)
    (auto simp: list_all_iff intro!: map_cong)

lemma lpp_ground_template_resolution_finite:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and head: "ground h"
   and finite: "lpp_finite_term a"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?tau = "\<lambda>x. if lpp_finite_term (sigma x) then sigma x else LPIVar x"
 have images: "lpp_finite_term (?tau x)" for x by simp
 have head_equal: "lp_ieval h rho=lp_ieval h LPIVar"
   by (rule lp_ieval_cong) (use head in \<open>auto simp: ground_vars_term_empty\<close>)
 have equation: "lp_isubst a sigma=lp_ieval h LPIVar"
   using mgu head_equal by (simp add: lpc_mgu_resolve_def)
 have substituted: "lpp_finite_term (lp_isubst a sigma)"
   by (simp add: equation lpp_finite_term_initial)
 have comparison: "lp_isubst a ?tau=lp_ieval h LPIVar"
   using lpp_finite_substitution_restrict[OF finite substituted] equation by simp
 have body: "lpp_finite_term (lp_ieval t rho)" if "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_finite_term_eval)
  fix x assume x: "x\<in>vars_term t"
  show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu comparison that x]) simp
 qed
 have rest: "lpp_finite_term (lp_isubst t sigma)" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_mgu_continuation_finite[OF mgu comparison _ that])
  fix g t assume "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
  then have "lpp_finite_term t" using continuation by (auto simp: lpp_finite_goals_def list_all_iff)
  then show "lpp_finite_term (lp_isubst t ?tau)" by (rule lpp_finite_term_substitute[OF _ images])
 qed
 show ?thesis using body rest
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms lpp_finite_goal_map list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_ground_template_resolution_finite}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite ground template transport" else ();
\<close>
end
