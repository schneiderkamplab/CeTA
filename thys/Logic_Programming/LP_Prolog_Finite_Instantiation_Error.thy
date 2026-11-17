theory LP_Prolog_Finite_Instantiation_Error
  imports LP_Prolog_Finite_Evaluation
begin

text \<open>Finiteness here concerns the evaluated arithmetic expression, not
the graph representation of a rational term. An unbound variable in a finite
expression prevents successful arithmetic evaluation. Other operands must also
be finite: a free variable alone does not rule out a diverging cyclic operand.\<close>

definition lpp_finite_instantiation_error where
  "lpp_finite_instantiation_error e = (lpp_finite_term e \<and> \<not>lp_seg_ground e)"

lemma lpp_finite_instantiation_error_not_ground:
  "lpp_finite_instantiation_error e \<Longrightarrow> \<not>lp_seg_ground e"
  by (simp add: lpp_finite_instantiation_error_def)

lemma lpp_finite_instantiation_error_not_integer:
  "lpp_finite_instantiation_error e \<Longrightarrow> \<not>lpp_integer_evaluation e n"
  using lpp_integer_evaluation_ground
  by (auto simp: lpp_finite_instantiation_error_def)

definition lpp_check_finite_instantiation_error where
  "lpp_check_finite_instantiation_error G F e =
    (vars_term e \<subseteq> G \<union> F \<and> vars_term e \<inter> F \<noteq> {})"

lemma lpp_checked_finite_instantiation_error:
  assumes checked: "lpp_check_finite_instantiation_error G F e"
    and ground: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
    and free: "\<And>x. x\<in>F \<Longrightarrow> \<exists>y. eta x=LPIVar y"
  shows "lpp_finite_instantiation_error (lp_ieval e eta)"
proof -
  have finite: "lpp_finite_term (lp_ieval e eta)"
  proof (rule lpp_finite_term_eval)
    fix x assume "x\<in>vars_term e"
    then have "x\<in>G \<or> x\<in>F"
      using checked by (auto simp: lpp_check_finite_instantiation_error_def)
    then show "lpp_finite_term (eta x)"
      using ground[of x] free[of x]
      by (auto intro: lpp_ground_finite_term lpp_finite_term.intros)
  qed
  obtain x where x: "x\<in>vars_term e" and member: "x\<in>F"
    using checked by (auto simp: lpp_check_finite_instantiation_error_def)
  obtain y where valuation: "eta x=LPIVar y" using free[OF member] by blast
  have nonground: "\<not>lp_seg_ground (eta x)"
    unfolding valuation by (auto elim: lp_seg_ground.cases)
  have "\<not>lp_seg_ground (lp_ieval e eta)"
    using x nonground by (simp only: lp_seg_ground_eval; blast)
  then show ?thesis using finite by (simp add: lpp_finite_instantiation_error_def)
qed

end
