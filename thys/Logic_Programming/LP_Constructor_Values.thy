theory LP_Constructor_Values
  imports LP_PiDP_Narrowing
begin

text \<open>Constructor values include infinite/rational trees and free
  variables. Only their measured projections have to be finite. This invariant
  is separate from DP minimality and must be carried by source extraction.\<close>

coinductive lp_constructor_value :: "'f set \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> bool"
  for C where
  var: "lp_constructor_value C (LPIVar x)"
| node: "f\<in>C \<Longrightarrow> list_all (lp_constructor_value C) ts \<Longrightarrow>
    lp_constructor_value C (LPIFun f ts)"

lemma lp_constructor_value_Fun:
  "lp_constructor_value C (LPIFun f ts) \<longleftrightarrow>
    f\<in>C \<and> list_all (lp_constructor_value C) ts"
  by (auto elim: lp_constructor_value.cases intro: lp_constructor_value.node)

lemma lp_constructor_value_map:
  assumes "range data \<subseteq> C"
  shows "lp_constructor_value C (map_lp_iterm data id t)"
proof (coinduction arbitrary: t)
  case lp_constructor_value
  then show ?case using assms by (cases t) (auto simp: list_all_iff)
qed

lemma lp_constructor_value_subst:
  assumes valid: "lp_constructor_value C t"
    and subst: "\<And>x. lp_constructor_value C (\<sigma> x)"
  shows "lp_constructor_value C (lp_isubst t \<sigma>)"
  using valid
proof (coinduction arbitrary: t)
  case lp_constructor_value
  show ?case
  proof (cases t)
    case (LPIVar x)
    show ?thesis using subst[of x]
      by (cases rule: lp_constructor_value.cases) (auto simp: LPIVar list_all_iff)
  next
    case (LPIFun f ts)
    show ?thesis using lp_constructor_value
      by (auto simp: LPIFun list_all_iff lp_constructor_value_Fun)
  qed
qed

lemma lp_constructor_value_projection:
  assumes pr: "lp_iproject \<pi> s t" and valid: "lp_constructor_value C s"
  shows "funs_term t \<subseteq> C"
  using pr valid
  by (induct rule: lp_iproject.induct)
    (fastforce simp: lp_constructor_value_Fun list_all_iff list_all2_conv_all_nth in_set_conv_nth)+

lemma lp_constructor_value_eval:
  assumes symbols: "funs_term t \<subseteq> C"
    and vals: "\<And>x. lp_constructor_value C (\<rho> x)"
  shows "lp_constructor_value C (lp_ieval t \<rho>)"
  using symbols by (induct t)
    (auto simp: lp_constructor_value_Fun list_all_iff intro: vals)

lemma lp_constructor_arguments_projection:
  assumes pr: "lp_iproject \<pi> (LPIFun f ts) a"
    and args: "\<And>t. t\<in>set ts \<Longrightarrow> lp_constructor_value C t"
  shows "\<forall>u\<lhd>a. funs_term u\<subseteq>C"
proof (cases "afs \<pi> (f,length ts)")
  case (AFList indices)
  obtain us where a: "a=Fun f us"
    and projected: "list_all2 (\<lambda>i t. i<length ts \<and> lp_iproject \<pi> (ts!i) t) indices us"
    using pr AFList by (cases rule: lp_iproject.cases) auto
  have children: "\<And>u. u\<in>set us \<Longrightarrow> funs_term u\<subseteq>C"
    using projected args lp_constructor_value_projection
    by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  show ?thesis unfolding a using children
    by (meson supt_Fun_imp_arg_supteq supteq_imp_funs_term_subset subset_trans)
next
  case (Collapse i)
  have bound: "i<length ts" and projected: "lp_iproject \<pi> (ts!i) a"
    using pr Collapse by (cases rule: lp_iproject.cases; auto)+
  have "funs_term a\<subseteq>C"
    by (rule lp_constructor_value_projection[OF projected args])
      (use bound in auto)
  then show ?thesis by (meson subset_trans supteq_imp_funs_term_subset supt_imp_supteq)
qed

lemma lp_constructor_finite_nf:
  assumes symbols: "funs_term t \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  shows "t\<in>NF_terms Q"
proof (rule ccontr)
  assume "t\<notin>NF_terms Q"
  then obtain ctxt q \<sigma> where t: "t=ctxt\<langle>q\<cdot>\<sigma>\<rangle>" and q: "q\<in>Q"
    by (rule not_NF_termsE)
  obtain f ts where q: "q=Fun f ts" and outside: "f\<notin>C" using roots[OF q] by blast
  have "f\<in>funs_term t" by (simp add: t q)
  then show False using symbols outside by blast
qed

corollary lp_constructor_projection_nf:
  assumes "lp_iproject \<pi> s t" "lp_constructor_value C s"
    "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  shows "t\<in>NF_terms Q"
  by (rule lp_constructor_finite_nf[OF lp_constructor_value_projection[OF assms(1,2)] assms(3)])

lemma lp_constructor_projected_subst_nf:
  fixes l r a b :: "('f,'v) term"
  assumes left: "lp_iproject \<pi> (lp_ieval l \<rho>) a"
    and right: "lp_iproject \<pi> (lp_ieval r \<rho>) b"
    and vals: "\<And>x. lp_constructor_value C (\<rho> x)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  shows "NF_subst nfs (af_term \<pi> l, af_term \<pi> r)
    (\<lambda>x. lp_projection \<pi> (\<rho> x)) Q"
proof (rule NF_substI)
  fix x
  assume "nfs" and x: "x\<in>vars_term (af_term \<pi> l) \<or> x\<in>vars_term (af_term \<pi> r)"
  obtain v :: "('f,'v) term" where pv: "lp_iproject \<pi> (\<rho> x) v"
    using x lp_iproject_ieval_variables[OF left] lp_iproject_ieval_variables[OF right] by blast
  have "v\<in>NF_terms Q" by (rule lp_constructor_projection_nf[OF pv vals roots])
  then show "lp_projection \<pi> (\<rho> x)\<in>NF_terms Q"
    unfolding lp_projection_eq[OF pv] .
qed

lemma lp_constructor_rule_qprojection:
  fixes r a :: "('f,'v) term"
  assumes rule: "(Fun f ts,r)\<in>R"
    and pr: "lp_iproject \<pi> (lp_ieval (Fun f ts) \<rho>) a"
    and vars: "vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> (Fun f ts))"
    and symbols: "\<And>t. t\<in>set ts \<Longrightarrow> funs_term t\<subseteq>C"
    and vals: "\<And>x. lp_constructor_value C (\<rho> x)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  obtains b where "lp_iproject \<pi> (lp_ieval r \<rho>) b"
    "(a,b)\<in>qrstep nfs Q (af_rule \<pi> ` R)"
proof -
  obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval r \<rho>) b"
    by (rule lp_infinite_rule_projection[OF pr vars rule]) blast
  have args: "\<And>t. t\<in>set (map (\<lambda>t. lp_ieval t \<rho>) ts) \<Longrightarrow> lp_constructor_value C t"
    using lp_constructor_value_eval[OF symbols vals] by auto
  have proper: "\<forall>u\<lhd>a. funs_term u\<subseteq>C"
    by (rule lp_constructor_arguments_projection[OF pr[unfolded lp_ieval.simps] args])
  have normal: "\<forall>u\<lhd>a. u\<in>NF_terms Q"
    using proper lp_constructor_finite_nf[OF _ roots] by blast
  have member: "(af_term \<pi> (Fun f ts),af_term \<pi> r)\<in>af_rule \<pi> ` R"
    using imageI[OF rule, of "af_rule \<pi>"] by (simp add: af_rule_alt_def)
  have subst: "NF_subst nfs (af_term \<pi> (Fun f ts),af_term \<pi> r)
      (\<lambda>x. lp_projection \<pi> (\<rho> x)) Q"
    by (rule lp_constructor_projected_subst_nf[OF pr pb vals roots])
  have step: "(a,b)\<in>qrstep nfs Q (af_rule \<pi> ` R)"
    unfolding lp_iproject_ieval_inverse[OF pr] lp_iproject_ieval_inverse[OF pb]
    by (rule qrstep.subst[OF _ member])
      (use normal subst lp_iproject_ieval_inverse[OF pr] in auto)
  show ?thesis by (rule that[OF pb step])
qed

end
