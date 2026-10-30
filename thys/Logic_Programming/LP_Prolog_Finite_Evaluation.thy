theory LP_Prolog_Finite_Evaluation
 imports LP_Prolog_Finite_Comparison
begin

text \<open>A finite evaluation envelope preserves exact checked integer
expressions. Other finite-ground expressions may return a scalar or raise an
error. Scalar results include binary64 encodings; they are not assumed integer.
This relation alone is not a source certificate.\<close>
definition lpp_finite_evaluation_result :: "(string lp_cut_symbol,'v) lp_iterm \<Rightarrow>
  (string lp_cut_symbol,'v) lp_iterm \<Rightarrow> bool" where
  "lpp_finite_evaluation_result e t =
    (if \<exists>n. lpp_integer_evaluation e n then lpp_integer_result e t
     else lp_seg_ground e \<and> (\<exists>f. t=LPIFun (LPCUser f) []))"

lemma lpp_finite_evaluation_integer:
  "lpp_integer_evaluation e n \<Longrightarrow>
    lpp_finite_evaluation_result e t = lpp_integer_result e t"
  by (auto simp: lpp_finite_evaluation_result_def)

lemma lpp_finite_evaluation_exact:
  assumes checked: "lpp_expression_check K e"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_finite_evaluation_result (lp_ieval (lpp_expression_term e) eta) t \<longleftrightarrow>
    t=lpp_integer_value (lpp_expression_value e rho)"
  by (simp only: lpp_finite_evaluation_integer[OF lpp_expression_evaluation[OF checked typed]]
    lpp_integer_result_exact[OF checked typed])

lemma lpp_finite_evaluation_integer_contract:
  "lpp_eval_integer_contract TYPE('v) lpp_finite_evaluation_result"
proof (unfold lpp_eval_integer_contract_def, intro allI impI)
  fix K :: "'v list" and e eta t
  assume check: "lpp_expression_check K e" and known: "lpp_integer_known K eta"
    and result: "lpp_finite_evaluation_result (lp_ieval (lpp_expression_term e) eta) t"
  obtain rho where typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    using lpp_integer_known_environment[OF known] by blast
  have exact: "lpp_finite_evaluation_result (lp_ieval (lpp_expression_term e) eta) t =
    (t=lpp_integer_value (lpp_expression_value e rho))"
    by (rule lpp_finite_evaluation_exact[where K=K and eta=eta and rho=rho, OF check typed])
  show "lpp_is_integer t" using result exact
    by (auto simp: lpp_is_integer_def)
qed

lemma lpp_finite_evaluation_ground:
  "lpp_finite_evaluation_result e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
  by (auto simp: lpp_finite_evaluation_result_def lpp_integer_result_def lpp_integer_value_def
    dest: lpp_integer_evaluation_ground intro: lp_seg_ground.intros split: if_splits)

lemma lpp_finite_evaluation_subst:
  fixes e t :: "(string lp_cut_symbol,'v) lp_iterm"
    and sigma :: "'v \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm"
  assumes result: "lpp_finite_evaluation_result e t"
  shows "lpp_finite_evaluation_result (lp_isubst e sigma) (lp_isubst t sigma)"
proof -
  have eg: "lp_seg_ground e" and tg: "lp_seg_ground t"
    using lpp_finite_evaluation_ground[OF result] by auto
  show ?thesis by (simp only: lp_seg_ground_subst[OF eg] lp_seg_ground_subst[OF tg] result)
qed

end
