theory LP_Prolog_Finite_Term_Basis
 imports LP_Prolog_Builtin_Domain
begin

text \<open>Shared finite-term facts for arithmetic evaluation and comparison.
A finite cyclic graph is not a finite term.\<close>

inductive lpp_finite_term :: "('f,'v) lp_iterm \<Rightarrow> bool" where
  variable: "lpp_finite_term (LPIVar x)"
| node: "list_all lpp_finite_term ts \<Longrightarrow> lpp_finite_term (LPIFun f ts)"

lemma lpp_finite_term_variable[simp]: "lpp_finite_term (LPIVar x)"
  by (rule lpp_finite_term.variable)

lemma lpp_finite_term_fun[simp]:
  "lpp_finite_term (LPIFun f ts) = list_all lpp_finite_term ts"
  by (auto intro: lpp_finite_term.intros elim: lpp_finite_term.cases)

lemma lpp_ground_finite_term:
  "lp_seg_ground t \<Longrightarrow> lpp_finite_term t"
  by (induct rule: lp_seg_ground.induct)
    (auto simp: list_all_iff intro: lpp_finite_term.intros)

lemma lpp_finite_term_eval:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> lpp_finite_term (eta x)) \<Longrightarrow>
    lpp_finite_term (lp_ieval t eta)"
  by (induct t) (auto simp: list_all_iff intro: lpp_finite_term.intros)

end
