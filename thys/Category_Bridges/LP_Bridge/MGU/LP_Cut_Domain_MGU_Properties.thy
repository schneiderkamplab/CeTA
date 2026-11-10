theory LP_Cut_Domain_MGU_Properties
  imports Category_LP_Cut_NO_Bridge.LP_Cut_Domain_MGU
begin

text \<open>Most-generality in the selected domain preserves fresh clause-body
variables. The comparison substitutions replace selected values by variables,
so their membership in the finite or rational domain is proved explicitly.\<close>

context cut_runtime_domain
begin

lemma mgu_body_factor:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_resolve a gs h bs \<sigma> \<rho>"
    and comparison: "lp_isubst a \<tau> = lp_ieval h \<nu>"
    and domains: "\<forall>x. D (\<tau> x)" "\<forall>x. D (\<nu> x)"
  shows "\<exists>\<delta> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    \<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
proof -
  from mgu comparison domains obtain \<delta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm" where factor:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
     map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    unfolding mgu_resolve_def by blast
  show ?thesis
  proof (rule exI[of _ \<delta>], intro ballI)
    fix g t x assume body: "g \<in> set bs" and occurrence: "t \<in> set (lp_cut_terms g)"
      and variable: "x \<in> vars_term t"
    have eq: "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>) g =
      lp_cut_map (\<lambda>t. lp_ieval t \<nu>) g"
      using factor body by (simp add: map_eq_conv)
    have "lp_isubst (lp_ieval t \<rho>) \<delta> = lp_ieval t \<nu>"
      using eq occurrence by (cases g) auto
    then show "lp_isubst (\<rho> x) \<delta> = \<nu> x"
      using lpc_ieval_variables_eq[OF _ variable] by (simp add: lp_ieval_subst)
  qed
qed


lemma mgu_body_variable_free:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes "mgu_resolve a gs h bs \<sigma> \<rho>"
    "lp_isubst a \<tau> = lp_ieval h \<nu>"
    "g \<in> set bs" "t \<in> set (lp_cut_terms g)" "x \<in> vars_term t"
    "\<nu> x = LPIVar y"
    "\<forall>x. D (\<tau> x)" "\<forall>x. D (\<nu> x)"
  shows "\<exists>z. \<rho> x = LPIVar z"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    where "lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using mgu_body_factor[OF assms(1,2,7,8)] assms(3-5) by blast
  then have "lp_isubst (\<rho> x) \<delta> = LPIVar y" using assms(6) by simp
  then show ?thesis by (rule lpc_isubst_variable_reflect)
qed

lemma mgu_body_variables_separate:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes "mgu_resolve a gs h bs \<sigma> \<rho>"
    "lp_isubst a \<tau> = lp_ieval h \<nu>"
    "g \<in> set bs" "t \<in> set (lp_cut_terms g)" "x \<in> vars_term t"
    "g' \<in> set bs" "t' \<in> set (lp_cut_terms g')" "y \<in> vars_term t'"
    "\<nu> x \<noteq> \<nu> y"
    "\<forall>x. D (\<tau> x)" "\<forall>x. D (\<nu> x)"
  shows "\<rho> x \<noteq> \<rho> y"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm" where factor:
    "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using mgu_body_factor[OF assms(1,2,10,11)] by blast
  have x: "lp_isubst (\<rho> x) \<delta> = \<nu> x" using factor assms(3-5) by blast
  have y: "lp_isubst (\<rho> y) \<delta> = \<nu> y" using factor assms(6-8) by blast
  show ?thesis using x y assms(9) by auto
qed


lemma mgu_body_only_variable_free:
  assumes mgu: "mgu_resolve a gs h bs \<sigma> \<rho>"
    and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
    and fresh: "x\<notin>vars_term h"
  shows "\<exists>y. \<rho> x = LPIVar y"
proof -
  let ?nu = "\<rho>(x := LPIVar x)"
  have head: "lp_ieval h ?nu = lp_ieval h \<rho>"
    by (rule lp_ieval_cong) (use fresh in auto)
  have comparison: "lp_isubst a \<sigma> = lp_ieval h ?nu"
    using mgu head by (simp add: mgu_resolve_def)
  show ?thesis
    by (rule mgu_body_variable_free[OF mgu comparison body])
      (use mgu in \<open>auto simp: mgu_resolve_def intro: variables\<close>)
qed

lemma mgu_body_only_variables_separate:
  assumes mgu: "mgu_resolve a gs h bs \<sigma> \<rho>"
    and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
      "g'\<in>set bs" "t'\<in>set (lp_cut_terms g')" "y\<in>vars_term t'"
    and fresh: "x\<notin>vars_term h" "y\<notin>vars_term h" "x\<noteq>y"
  shows "\<rho> x \<noteq> \<rho> y"
proof -
  let ?nu = "\<rho>(x := LPIVar x, y := LPIVar y)"
  have head: "lp_ieval h ?nu = lp_ieval h \<rho>"
    by (rule lp_ieval_cong) (use fresh in auto)
  have comparison: "lp_isubst a \<sigma> = lp_ieval h ?nu"
    using mgu head by (simp add: mgu_resolve_def)
  show ?thesis
    by (rule mgu_body_variables_separate[OF mgu comparison body])
      (use mgu fresh in \<open>auto simp: mgu_resolve_def intro: variables\<close>)
qed

theorem mgu_body_only_knowledge:
  assumes mgu: "mgu_resolve a gs h bs \<sigma> \<rho>"
  shows "lpc_free_knowledge (lpc_body_only_variables h bs) \<rho>"
proof (unfold lpc_free_knowledge_def, intro conjI)
  show "\<forall>x\<in>lpc_body_only_variables h bs. \<exists>y. \<rho> x = LPIVar y"
    using mgu_body_only_variable_free[OF mgu]
    by (auto simp: lpc_body_only_variables_def)
  show "inj_on \<rho> (lpc_body_only_variables h bs)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>lpc_body_only_variables h bs"
      and y: "y\<in>lpc_body_only_variables h bs" and eq: "\<rho> x=\<rho> y"
    show "x=y"
    proof (rule ccontr)
      assume "x\<noteq>y"
      then have "\<rho> x\<noteq>\<rho> y"
        using mgu_body_only_variables_separate[OF mgu] x y
        by (auto simp: lpc_body_only_variables_def)
      then show False using eq by contradiction
    qed
  qed
qed


end
end
