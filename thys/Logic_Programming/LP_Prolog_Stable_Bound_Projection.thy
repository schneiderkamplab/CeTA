theory LP_Prolog_Stable_Bound_Projection
 imports LP_Prolog_Stable_Return_Context
begin

text \<open>A bound coordinate observes the value of an expression, not an
integer type of the original term. Non-evaluable expressions have a fixed
unused coordinate; successful comparison premises remain mandatory.\<close>

definition lpp_stable_expression_bound where
  "lpp_stable_expression_bound operation expression =
    (if \<exists>v. lpp_stable_scalar_evaluation operation expression v
     then lpp_scalar_floor (THE v. lpp_stable_scalar_evaluation operation expression v)
     else 0)"

lemma lpp_stable_expression_bound_exact:
  assumes evaluated: "lpp_stable_scalar_evaluation operation expression v"
  shows "lpp_stable_expression_bound operation expression=lpp_scalar_floor v"
proof -
  have unique: "(THE w. lpp_stable_scalar_evaluation operation expression w)=v"
    by (rule the_equality[where P="lpp_stable_scalar_evaluation operation expression", OF evaluated])
      (use evaluated in \<open>auto dest: lpp_stable_scalar_evaluation_unique\<close>)
  show ?thesis using evaluated unique by (auto simp: lpp_stable_expression_bound_def)
qed

lemma lpp_stable_expression_bound_ground_subst:
  "lp_seg_ground expression \<Longrightarrow>
    lpp_stable_expression_bound operation (lp_isubst expression sigma)=
    lpp_stable_expression_bound operation expression"
  by (simp add: lp_seg_ground_subst)

lemma lpp_stable_expression_bound_comparison:
  assumes compatible: "lpp_stable_integer_operations operation"
    and integer: "lpp_integer_evaluation a k"
    and comparison: "comparison=LPPIntLess \<or> comparison=LPPIntLessEqual"
    and success: "lpp_stable_compare_outcome operation comparison a b (LPPBuiltinSuccess LPIVar)"
  shows "k \<le> lpp_stable_expression_bound operation b"
proof -
  obtain v n d where evaluated: "lpp_stable_scalar_evaluation operation b v"
    and fraction: "lpp_scalar_fraction v n d"
    using success by (auto simp: lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
  show ?thesis using lpp_stable_compare_upper_bound[OF compatible integer evaluated fraction comparison success]
    by (simp only: lpp_stable_expression_bound_exact[OF evaluated])
qed

lemma lpp_stable_expression_bound_actual_return:
  assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and ground: "lp_seg_ground initial_expression"
    and initialized: "list_all (\<lambda>frame. lp_ieval expression (snd frame)=initial_expression) ss"
  shows "lpp_stable_expression_bound operation (lp_ieval expression eta)=
    lpp_stable_expression_bound operation initial_expression"
proof -
  have stable: "lp_ieval expression (\<lambda>x. lp_isubst (rho x) sigma)=initial_expression"
    if "lp_ieval expression rho=initial_expression" for rho sigma
    using that ground by (simp add: lp_ieval_subst[symmetric] lp_seg_ground_subst)
  have "lp_ieval expression eta=initial_expression"
    by (rule lpp_actual_return_substitution_property[OF stable actual initialized])
  then show ?thesis by simp
qed

ML \<open>
val checked = [@{thm lpp_stable_expression_bound_exact}, @{thm lpp_stable_expression_bound_ground_subst},
  @{thm lpp_stable_expression_bound_comparison}, @{thm lpp_stable_expression_bound_actual_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable bound projection dependency" else ();
\<close>
end
