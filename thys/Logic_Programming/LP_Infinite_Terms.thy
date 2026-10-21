theory LP_Infinite_Terms
  imports LP_Filtered_Narrowing
begin

text \<open>Runtime values may be infinite. In particular, cyclic rational trees
  obtained by unification without the occurs check are included. Program clauses
  remain finite terms. Only the projection used as a termination measure must
  be finite; discarded arguments need not be finite or ground.\<close>

codatatype ('f,'v) lp_iterm =
    LPIVar 'v
  | LPIFun 'f "('f,'v) lp_iterm list"

fun lp_ieval :: "('f,'v) term \<Rightarrow> ('v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow> ('f,'w) lp_iterm" where
  "lp_ieval (Var x) \<rho> = \<rho> x"
| "lp_ieval (Fun f ts) \<rho> = LPIFun f (map (\<lambda>t. lp_ieval t \<rho>) ts)"

primcorec lp_isubst :: "('f,'v) lp_iterm \<Rightarrow> ('v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow> ('f,'w) lp_iterm" where
  "lp_isubst t \<sigma> = (case t of LPIVar x \<Rightarrow> \<sigma> x
    | LPIFun f ts \<Rightarrow> LPIFun f (map (\<lambda>s. lp_isubst s \<sigma>) ts))"

lemma lp_isubst_Var[simp]: "lp_isubst (LPIVar x) \<sigma> = \<sigma> x"
  by (subst lp_isubst.code) simp

lemma lp_isubst_Fun[simp]:
  "lp_isubst (LPIFun f ts) \<sigma> = LPIFun f (map (\<lambda>t. lp_isubst t \<sigma>) ts)"
  by (subst lp_isubst.code) simp

lemma lp_ieval_subst:
  "lp_isubst (lp_ieval t \<rho>) \<sigma> = lp_ieval t (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
  by (induct t) (auto intro!: map_cong)

lemma lp_isubst_id[simp]: "lp_isubst t LPIVar = t"
  by (coinduction arbitrary: t)
    (auto simp: list_all2_map1 list.rel_refl split: lp_iterm.splits)

text \<open>The inductive relation deliberately has no variable case. Its
  derivations are finite even when the source value is infinite.\<close>

inductive lp_iproject :: "'f afs \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> ('f,'w) term \<Rightarrow> bool"
  for \<pi> where
  list: "afs \<pi> (f,length ts) = AFList indices \<Longrightarrow>
    list_all2 (\<lambda>i t. i < length ts \<and> lp_iproject \<pi> (ts!i) t) indices us \<Longrightarrow>
    lp_iproject \<pi> (LPIFun f ts) (Fun f us)"
| collapse: "afs \<pi> (f,length ts) = Collapse i \<Longrightarrow>
    i < length ts \<Longrightarrow> lp_iproject \<pi> (ts!i) t \<Longrightarrow>
    lp_iproject \<pi> (LPIFun f ts) t"

lemma lp_iproject_ground:
  "lp_iproject \<pi> s t \<Longrightarrow> ground t"
  by (induct rule: lp_iproject.induct)
    (auto simp: list_all2_conv_all_nth in_set_conv_nth)

lemma lp_iproject_subst:
  "lp_iproject \<pi> s t \<Longrightarrow> lp_iproject \<pi> (lp_isubst s \<sigma>) t"
  by (induct rule: lp_iproject.induct)
    (auto simp: list_all2_conv_all_nth intro: lp_iproject.intros)

lemma lp_iproject_unique:
  assumes "lp_iproject \<pi> s t" "lp_iproject \<pi> s u"
  shows "t = u"
  using assms
proof (induct arbitrary: u rule: lp_iproject.induct)
  case (list f ts indices us)
  obtain vs where u: "u = Fun f vs"
    and vs: "list_all2 (\<lambda>i t. i < length ts \<and> lp_iproject \<pi> (ts!i) t) indices vs"
    using list.prems list.hyps(1) by (cases rule: lp_iproject.cases) auto
  have "us = vs"
    using list.hyps(2) vs
    by (intro nth_equalityI) (auto simp: list_all2_conv_all_nth)
  then show ?case by (simp add: u)
next
  case (collapse f ts i t)
  have "lp_iproject \<pi> (ts!i) u"
    using collapse.prems collapse.hyps(1)
    by (cases rule: lp_iproject.cases) auto
  then show ?case by (rule collapse.hyps(4))
qed

definition lp_projection where
  "lp_projection \<pi> s = (THE t. lp_iproject \<pi> s t)"

lemma lp_projection_eq:
  "lp_iproject \<pi> s t \<Longrightarrow> lp_projection \<pi> s = t"
  unfolding lp_projection_def
  by (rule the_equality) (auto intro: lp_iproject_unique)

lemma lp_iproject_ieval_forward:
  assumes "\<And>x. x \<in> vars_term (af_term \<pi> t) \<Longrightarrow> lp_iproject \<pi> (\<rho> x) (\<theta> x)"
  shows "lp_iproject \<pi> (lp_ieval t \<rho>) (af_term \<pi> t \<cdot> \<theta>)"
  using assms
proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts)
  have wf: "wf_af_entry (length ts) (afs \<pi> (f,length ts))"
    by (rule Argument_Filter.afs)
  show ?case
  proof (cases "afs \<pi> (f,length ts)")
    case (Collapse i)
    with wf have i: "i < length ts" by simp
    have child: "lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) (af_term \<pi> (ts!i) \<cdot> \<theta>)"
      using Fun.hyps[OF nth_mem[OF i]] Fun.prems Collapse i by auto
    show ?thesis
      apply (simp only: lp_ieval.simps af_term.simps Collapse apply_af_entry.simps)
      apply (simp only: nth_map[OF i])
      apply (rule lp_iproject.collapse[where i=i])
      using Collapse i child by simp_all
  next
    case (AFList indices)
    with wf have valid: "\<And>i. i \<in> set indices \<Longrightarrow> i < length ts" by auto
    have children: "\<And>i. i \<in> set indices \<Longrightarrow>
      lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) (af_term \<pi> (ts!i) \<cdot> \<theta>)"
    proof -
      fix i assume mem: "i \<in> set indices"
      show "lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) (af_term \<pi> (ts!i) \<cdot> \<theta>)"
      proof (rule Fun.hyps[OF nth_mem[OF valid[OF mem]]])
        fix x assume "x \<in> vars_term (af_term \<pi> (ts!i))"
        then have "x \<in> vars_term (af_term \<pi> (Fun f ts))"
          using mem valid by (auto simp: AFList)
        then show "lp_iproject \<pi> (\<rho> x) (\<theta> x)" by (rule Fun.prems)
      qed
    qed
    show ?thesis
      using children valid AFList
      by (auto simp: list_all2_conv_all_nth intro!: lp_iproject.list)
  qed
qed

lemma lp_iproject_ieval_variables:
  fixes u :: "('f,'v) term"
  assumes "lp_iproject \<pi> (lp_ieval t \<rho>) u"
    and "x \<in> vars_term (af_term \<pi> t)"
  shows "\<exists>v::('f,'v) term. lp_iproject \<pi> (\<rho> x) v"
  using assms
proof (induct t arbitrary: u)
  case (Var y) then show ?case by auto
next
  case (Fun f ts)
  have wf: "wf_af_entry (length ts) (afs \<pi> (f,length ts))"
    by (rule Argument_Filter.afs)
  show ?case
  proof (cases "afs \<pi> (f,length ts)")
    case (Collapse i)
    with wf have i: "i < length ts" by simp
    have child: "lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) u"
      using Fun.prems(1) Collapse i
      by (cases rule: lp_iproject.cases) auto
    have var: "x \<in> vars_term (af_term \<pi> (ts!i))"
      using Fun.prems(2) Collapse i by simp
    show ?thesis by (rule Fun.hyps[OF nth_mem[OF i] child var])
  next
    case (AFList indices)
    with wf have valid: "\<And>i. i \<in> set indices \<Longrightarrow> i < length ts" by auto
    obtain i where mem: "i \<in> set indices" and var: "x \<in> vars_term (af_term \<pi> (ts!i))"
      using Fun.prems(2) AFList valid by auto
    obtain us where result: "u = Fun f us" and raw: "list_all2 (\<lambda>i t. i < length (map (\<lambda>t. lp_ieval t \<rho>) ts) \<and>
      lp_iproject \<pi> (map (\<lambda>t. lp_ieval t \<rho>) ts ! i) t) indices us"
      using Fun.prems(1) AFList
      by (cases rule: lp_iproject.cases) auto
    have children: "list_all2 (\<lambda>i t. i < length ts \<and>
      lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) t) indices us"
      using raw by (auto simp: list_all2_conv_all_nth)
    obtain j where j: "j < length indices" "indices!j=i" using mem by (auto simp: in_set_conv_nth)
    have child: "lp_iproject \<pi> (lp_ieval (ts!i) \<rho>) (us!j)"
      using children j by (auto simp: list_all2_conv_all_nth)
    show ?thesis by (rule Fun.hyps[OF nth_mem[OF valid[OF mem]] child var])
  qed
qed

lemma lp_iproject_ieval_inverse:
  fixes u :: "('f,'v) term"
  assumes pr: "lp_iproject \<pi> (lp_ieval t \<rho>) u"
  shows "u = af_term \<pi> t \<cdot> (\<lambda>x. lp_projection \<pi> (\<rho> x))"
proof -
  have vars: "\<And>x. x \<in> vars_term (af_term \<pi> t) \<Longrightarrow>
    lp_iproject \<pi> (\<rho> x) (lp_projection \<pi> (\<rho> x) :: ('f,'v) term)"
  proof -
    fix x assume x: "x \<in> vars_term (af_term \<pi> t)"
    obtain v :: "('f,'v) term" where pv: "lp_iproject \<pi> (\<rho> x) v"
      using lp_iproject_ieval_variables[OF pr x] by blast
    show "lp_iproject \<pi> (\<rho> x) (lp_projection \<pi> (\<rho> x) :: ('f,'v) term)"
      using pv lp_projection_eq[OF pv] by simp
  qed
  show ?thesis by (rule lp_iproject_unique[OF pr lp_iproject_ieval_forward[OF vars]])
qed

lemma lp_infinite_rule_projection:
  fixes l r s :: "('f,'v) term"
  assumes pr: "lp_iproject \<pi> (lp_ieval l \<rho>) s"
    and vars: "vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and rule: "(l,r) \<in> R"
  obtains t where "lp_iproject \<pi> (lp_ieval r \<rho>) t"
    "(s,t) \<in> rstep (af_rule \<pi> ` R)"
proof -
  let ?\<theta> = "\<lambda>x. (lp_projection \<pi> (\<rho> x) :: ('f,'v) term)"
  have available: "\<And>x. x \<in> vars_term (af_term \<pi> r) \<Longrightarrow>
    lp_iproject \<pi> (\<rho> x) (?\<theta> x)"
  proof -
    fix x assume "x \<in> vars_term (af_term \<pi> r)"
    with vars have x: "x \<in> vars_term (af_term \<pi> l)" by blast
    obtain v :: "('f,'v) term" where pv: "lp_iproject \<pi> (\<rho> x) v"
      using lp_iproject_ieval_variables[OF pr x] by blast
    show "lp_iproject \<pi> (\<rho> x) (?\<theta> x)"
      using pv lp_projection_eq[OF pv] by simp
  qed
  have target: "lp_iproject \<pi> (lp_ieval r \<rho>) (af_term \<pi> r \<cdot> ?\<theta>)"
    by (rule lp_iproject_ieval_forward[OF available])
  have member: "(af_term \<pi> l,af_term \<pi> r) \<in> af_rule \<pi> ` R"
    using imageI[OF rule, of "af_rule \<pi>"] by (simp add: af_rule_alt_def)
  have step: "(s,af_term \<pi> r \<cdot> ?\<theta>) \<in> rstep (af_rule \<pi> ` R)"
    unfolding lp_iproject_ieval_inverse[OF pr]
    by (rule rstep_subst[OF rstep_rule[OF member]])
  show thesis by (rule that[OF target step])
qed

end
