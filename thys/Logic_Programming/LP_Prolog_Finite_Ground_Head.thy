theory LP_Prolog_Finite_Ground_Head
 imports LP_Prolog_Finite_Variable_Head
begin

text \<open>Ground selected calls admit arbitrary constructor and repeated-variable
heads. Only variables occurring in the head inherit its ground values. Fresh
body-only variables remain finite variables in the comparison unifier.\<close>

definition lpp_ground_head_comparison where
 "lpp_ground_head_comparison h rho x =
   (if x\<in>vars_term h then rho x else LPIVar x)"

lemma lpp_ground_head_comparison_equal:
 "lp_ieval h (lpp_ground_head_comparison h rho)=lp_ieval h rho"
 by (rule lp_ieval_cong) (simp add: lpp_ground_head_comparison_def)

lemma lpp_ground_head_comparison_finite:
 assumes "lp_seg_ground (lp_ieval h rho)"
 shows "lpp_finite_term (lpp_ground_head_comparison h rho x)"
 using assms by (auto simp: lpp_ground_head_comparison_def lp_seg_ground_eval
   intro: lpp_ground_finite_term)

lemma lpp_ground_head_finite_body:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and ground: "lp_seg_ground a"
   and member: "g\<in>set bs" "t\<in>set (lp_cut_terms g)"
 shows "lpp_finite_term (lp_ieval t rho)"
proof -
 have head: "a=lp_ieval h rho"
   using mgu ground by (simp add: lpc_mgu_resolve_def lp_seg_ground_subst)
 have comparison: "lp_isubst a LPIVar=lp_ieval h (lpp_ground_head_comparison h rho)"
   by (simp add: lpp_ground_head_comparison_equal head)
 show ?thesis
 proof (rule lpp_finite_term_eval)
  fix x assume x: "x\<in>vars_term t"
  show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu comparison member x
     lpp_ground_head_comparison_finite[OF ground[unfolded head]]])
 qed
qed

lemma lpp_ground_head_finite_continuation:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and ground: "lp_seg_ground a"
   and finite: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow> lpp_finite_term t"
   and member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 shows "lpp_finite_term (lp_isubst t sigma)"
proof -
 have comparison: "lp_isubst a LPIVar=lp_ieval h rho"
   using mgu ground by (simp add: lpc_mgu_resolve_def lp_seg_ground_subst)
 show ?thesis by (rule lpp_mgu_continuation_finite[OF mgu comparison _ member])
   (simp add: finite)
qed

ML \<open>
val checked = [@{thm lpp_ground_head_finite_body}, @{thm lpp_ground_head_finite_continuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ground head transport" else ();
\<close>
end
