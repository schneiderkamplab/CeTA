(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Innermost_Usable
  imports
    CSR_Muterm_Usable_Rules
    CSR_Checker_Extensions.CSR_Innermost_Active_SCT
begin

text \<open>
  Semantic invariant for the innermost branch of the LPAR'08
  U-triangle processor.  A normal active argument needs no usable rules;
  otherwise every rule at its root must have been retained, recursively at
  active argument positions.
\<close>

fun muterm_innermost_ur_safe where
  "muterm_innermost_ur_safe R U \<mu> (Var x) = True"
| "muterm_innermost_ur_safe R U \<mu> (Fun f ts) =
    (((Fun f ts) \<in> NF (csstep \<mu> R) \<or>
       (\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U)) \<and>
     (\<forall>i<length ts. i \<in> \<mu> (f,length ts) \<longrightarrow>
       muterm_innermost_ur_safe R U \<mu> (ts ! i)))"

text \<open>
  The reduction-pair variant must only inspect active arguments which the
  certified argument filter retains.  In particular, a variable introduced
  below a filtered marked argument is semantically invisible to the weak
  order and need not satisfy the unfiltered MU-TERM variable condition.
\<close>

fun muterm_innermost_af_ur_safe where
  "muterm_innermost_af_ur_safe R U \<mu> \<pi> (Var x) = True"
| "muterm_innermost_af_ur_safe R U \<mu> \<pi> (Fun f ts) =
    (((Fun f ts) \<in> NF (csstep \<mu> R) \<or>
       (\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U)) \<and>
     (\<forall>i<length ts. i \<in> \<mu> (f,length ts) \<longrightarrow>
       i \<in> \<pi> (f,length ts) \<longrightarrow>
       muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)))"

fun muterm_innermost_af_ur_skeleton where
  "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> (Var x) = True"
| "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> (Fun f ts) =
    ((\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U) \<and>
     (\<forall>i<length ts. i \<in> \<mu> (f,length ts) \<longrightarrow>
       i \<in> \<pi> (f,length ts) \<longrightarrow>
       muterm_innermost_af_ur_skeleton R U \<mu> \<pi> (ts ! i)))"

lemma csstep_active_arg_lift:
  assumes i: "i < length ts"
    and active: "i \<in> \<mu> (f,length ts)"
    and step: "(ts ! i,u) \<in> csstep \<mu> R"
  shows "(Fun f ts,Fun f (ts[i := u])) \<in> csstep \<mu> R"
  using csstep_FunI[OF i active step]
  unfolding csstep_root_nonroot by blast

lemma NF_csstep_active_arg:
  assumes nf: "Fun f ts \<in> NF (csstep \<mu> R)"
    and i: "i < length ts"
    and active: "i \<in> \<mu> (f,length ts)"
  shows "ts ! i \<in> NF (csstep \<mu> R)"
proof (unfold NF_iff_no_step, intro allI notI)
  fix u
  assume step: "(ts ! i,u) \<in> csstep \<mu> R"
  from csstep_active_arg_lift[OF i active step] nf
  show False unfolding NF_iff_no_step by blast
qed

lemma muterm_innermost_ur_safe_NF:
  assumes "t \<in> NF (csstep \<mu> R)"
  shows "muterm_innermost_ur_safe R U \<mu> t"
  using assms
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have args: "muterm_innermost_ur_safe R U \<mu> (ts ! i)"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)" for i
  proof (rule Fun.hyps[OF nth_mem[OF i]])
    show "ts ! i \<in> NF (csstep \<mu> R)"
      by (rule NF_csstep_active_arg[OF Fun.prems i active])
  qed
  show ?case using Fun.prems args by simp
qed

fun muterm_innermost_ur_skeleton where
  "muterm_innermost_ur_skeleton R U \<mu> (Var x) = True"
| "muterm_innermost_ur_skeleton R U \<mu> (Fun f ts) =
    ((\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U) \<and>
     (\<forall>i<length ts. i \<in> \<mu> (f,length ts) \<longrightarrow>
       muterm_innermost_ur_skeleton R U \<mu> (ts ! i)))"

lemma muterm_root_closed_imp_skeleton:
  assumes closed: "csr_u3_root_rules_closed R U t (mu_fun_poss \<mu> t)"
  shows "muterm_innermost_ur_skeleton R U \<mu> t"
  using closed
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have root_rules: "\<forall>lr\<in>R.
      root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U"
  proof (intro ballI impI)
    fix lr
    assume lr: "lr \<in> R" and root_lr: "root (fst lr) = Some (f,length ts)"
    have nil: "[] \<in> mu_fun_poss \<mu> (Fun f ts)" by simp
    from Fun.prems[unfolded csr_u3_root_rules_closed_def,
      rule_format, OF nil, of "(f,length ts)"] root_lr lr
    show "lr \<in> U" by simp
  qed
  have child_closed: "csr_u3_root_rules_closed R U (ts ! i)
      (mu_fun_poss \<mu> (ts ! i))"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)" for i
  proof (unfold csr_u3_root_rules_closed_def)
    show "\<forall>p\<in>mu_fun_poss \<mu> (ts ! i). \<forall>g.
      root (ts ! i |_ p) = Some g \<longrightarrow>
      (\<forall>lr\<in>R. root (fst lr) = Some g \<longrightarrow> lr \<in> U)"
    proof (rule ballI)
      fix p
      assume p: "p \<in> mu_fun_poss \<mu> (ts ! i)"
      show "\<forall>g. root (ts ! i |_ p) = Some g \<longrightarrow>
        (\<forall>lr\<in>R. root (fst lr) = Some g \<longrightarrow> lr \<in> U)"
      proof (rule allI)
        fix g
        show "root (ts ! i |_ p) = Some g \<longrightarrow>
          (\<forall>lr\<in>R. root (fst lr) = Some g \<longrightarrow> lr \<in> U)"
        proof
          assume at: "root (ts ! i |_ p) = Some g"
          have ip: "i # p \<in> mu_fun_poss \<mu> (Fun f ts)"
            using i active p by simp
          have at_parent: "root (Fun f ts |_ (i # p)) = Some g"
            using i at by simp
          have parent_closed:
            "\<forall>q\<in>mu_fun_poss \<mu> (Fun f ts). \<forall>h.
              root (Fun f ts |_ q) = Some h \<longrightarrow>
              (\<forall>lr\<in>R. root (fst lr) = Some h \<longrightarrow> lr \<in> U)"
            using Fun.prems unfolding csr_u3_root_rules_closed_def .
          show "\<forall>lr\<in>R. root (fst lr) = Some g \<longrightarrow> lr \<in> U"
            using parent_closed ip at_parent by blast
        qed
      qed
    qed
  qed
  have children: "muterm_innermost_ur_skeleton R U \<mu> (ts ! i)"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)" for i
    by (rule Fun.hyps[OF nth_mem[OF i] child_closed[OF i active]])
  show ?case using root_rules children by simp
qed

lemma muterm_root_closed_imp_af_skeleton:
  assumes closed: "csr_u3_root_rules_closed R U t (mu_fun_poss \<mu> t)"
  shows "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> t"
proof -
  from muterm_root_closed_imp_skeleton[OF closed]
  show ?thesis
  proof (induct t)
    case (Var x)
    then show ?case by simp
  next
    case (Fun f ts)
    then show ?case by auto
  qed
qed

lemma muterm_innermost_af_ur_safe_NF:
  assumes "t \<in> NF (csstep \<mu> R)"
  shows "muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
  using assms
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have args: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)" for i
  proof (rule Fun.hyps[OF nth_mem[OF i]])
    show "ts ! i \<in> NF (csstep \<mu> R)"
      by (rule NF_csstep_active_arg[OF Fun.prems i active])
  qed
  show ?case using Fun.prems args by simp
qed

lemma muterm_innermost_af_ur_safe_inter_subterm:
  assumes safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
    and p: "p \<in> mu_poss (af_inter \<pi> \<mu>) t"
  shows "muterm_innermost_af_ur_safe R U \<mu> \<pi> (t |_ p)"
  using safe p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  from Cons.prems(2) obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts"
    and active: "i \<in> \<mu> (f,length ts)"
    and retained: "i \<in> \<pi> (f,length ts)"
    and p': "p \<in> mu_poss (\<lambda>a. \<pi> a \<inter> \<mu> a) (ts ! i)"
    by (cases t) (auto simp: af_inter_def)
  have p: "p \<in> mu_poss (af_inter \<pi> \<mu>) (ts ! i)"
    using p' unfolding af_inter_def .
  have child: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
    using Cons.prems(1) i active retained unfolding t by simp
  have ih: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i |_ p)"
    by (rule Cons.hyps[OF child p])
  show ?case unfolding t using i ih by simp
qed

lemma muterm_innermost_af_ur_safe_subst_safe:
  assumes skeleton: "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> t"
    and safe: "\<And>x. x \<in> mu_vars_term (af_inter \<pi> \<mu>) t \<Longrightarrow>
      muterm_innermost_af_ur_safe R U \<mu> \<pi> (\<sigma> x)"
  shows "muterm_innermost_af_ur_safe R U \<mu> \<pi> (t \<cdot> \<sigma>)"
  using skeleton safe
proof (induct t)
  case (Var x)
  have x: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) (Var x)"
    unfolding mu_vars_term_def by simp
  show ?case using Var.prems(2)[OF x] by simp
next
  case (Fun f ts)
  have root_rules: "\<forall>lr\<in>R.
      root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U"
    using Fun.prems(1) by simp
  have children: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i \<cdot> \<sigma>)"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
      and retained: "i \<in> \<pi> (f,length ts)" for i
  proof (rule Fun.hyps[OF nth_mem[OF i]])
    show "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> (ts ! i)"
      using Fun.prems(1) i active retained by simp
  next
    fix x
    assume x: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) (ts ! i)"
    have "x \<in> mu_vars_term (af_inter \<pi> \<mu>) (Fun f ts)"
      by (rule mu_vars_term_active_argI[OF i _ x],
          use active retained in \<open>simp add: af_inter_def\<close>)
    then show "muterm_innermost_af_ur_safe R U \<mu> \<pi> (\<sigma> x)"
      by (rule Fun.prems(2))
  qed
  show ?case using root_rules children by simp
qed

definition rhs_af_mu_vars_condition where
  "rhs_af_mu_vars_condition \<mu> \<pi> T = (\<forall>(l,r)\<in>T.
    mu_vars_term (af_inter \<pi> \<mu>) r \<subseteq>
    mu_vars_term (af_inter \<pi> \<mu>) l)"

definition rhs_pair_af_mu_vars_condition where
  "rhs_pair_af_mu_vars_condition \<mu> \<pi> T = (\<forall>(l,r)\<in>T.
    mu_vars_term (af_inter \<pi> \<mu>) r \<subseteq> mu_vars_term \<mu> l)"

lemma muterm_innermost_af_ur_safe_csstep:
  fixes R U S NS :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_af_mu_vars_condition \<mu> \<pi> U"
    and redpair: "af_redpair S NS \<pi>"
    and U_NS: "U \<subseteq> NS"
    and safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> s"
    and step: "(s,t) \<in> csstep \<mu> R"
  shows "(s,t) \<in> NS \<and> muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
  using safe step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  interpret rp: af_redpair S NS \<pi> by (rule redpair)
  from Fun.prems(2) consider
      (root) "(Fun f ss,t) \<in> csrstep \<mu> R"
    | (nonroot) "(Fun f ss,t) \<in> csnrstep \<mu> R"
    unfolding csstep_root_nonroot by blast
  then show ?case
  proof cases
    case root
    from root obtain l r \<sigma> where lr: "(l,r) \<in> R"
      and source: "Fun f ss = l \<cdot> \<sigma>"
      and target: "t = r \<cdot> \<sigma>"
      by (elim csrstepE)
    from wf lr obtain g ls where l: "l = Fun g ls"
      unfolding wf_trs_def by (cases l, auto)
    from source l have g: "g = f" and len: "length ls = length ss" by auto
    have not_nf: "Fun f ss \<notin> NF (csstep \<mu> R)"
      using Fun.prems(2) unfolding NF_iff_no_step by blast
    from Fun.prems(1) not_nf have roots: "\<forall>ab\<in>R.
      root (fst ab) = Some (f,length ss) \<longrightarrow> ab \<in> U" by simp
    have lrU: "(l,r) \<in> U" using roots lr l g len by simp
    have rel: "(Fun f ss,t) \<in> NS"
    proof -
      have "(Fun f ss,t) \<in> rstep U"
        by (rule rstepI[OF lrU, of _ Hole \<sigma>], use source target in auto)
      with rstep_subset[OF rp.ctxt_NS rp.subst_NS U_NS] show ?thesis by blast
    qed
    have skeleton: "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> r"
      by (rule muterm_root_closed_imp_af_skeleton[OF closed[OF lrU]])
    have subst_safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (\<sigma> x)"
      if x: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) r" for x
    proof -
      have xl: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) l"
        using conservative lrU x unfolding rhs_af_mu_vars_condition_def by blast
      from xl obtain p where p: "p \<in> mu_poss (af_inter \<pi> \<mu>) l"
        and at: "l |_ p = Var x" unfolding mu_vars_term_def by blast
      have psub: "p \<in> mu_poss (af_inter \<pi> \<mu>) (l \<cdot> \<sigma>)"
        using p by (rule mu_poss_subst_lift)
      have atsub: "(l \<cdot> \<sigma>) |_ p = \<sigma> x"
        using subt_at_subst[OF mu_poss_imp_poss[OF p], of \<sigma>] at by simp
      have safe_l: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (l \<cdot> \<sigma>)"
        using Fun.prems(1) source by simp
      from muterm_innermost_af_ur_safe_inter_subterm[OF safe_l psub]
      show ?thesis using atsub by simp
    qed
    have safe_t: "muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
      unfolding target
      by (rule muterm_innermost_af_ur_safe_subst_safe[OF skeleton subst_safe])
    show ?thesis using rel safe_t by blast
  next
    case nonroot
    from nonroot obtain i ts where
      i: "i < length ss" and active: "i \<in> \<mu> (f,length ss)"
      and target: "t = Fun f ts" and len: "length ts = length ss"
      and local: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
        ts ! j = ss ! j" by (metis csnrstep_FunE)
    have update: "ts = ss[i := ts ! i]"
    proof (rule nth_equalityI)
      show "length ts = length (ss[i := ts ! i])" using len by simp
      fix j
      assume j: "j < length ts"
      show "ts ! j = (ss[i := ts ! i]) ! j"
        by (cases "j=i", use j i len same in auto)
    qed
    show ?thesis
    proof (cases "i \<in> \<pi> (f,length ss)")
      case retained: True
      have safe_i: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! i)"
        using Fun.prems(1) i active retained by simp
      from Fun.hyps[OF nth_mem[OF i], of "ts ! i", OF safe_i local]
      have local_NS: "(ss ! i,ts ! i) \<in> NS"
        and safe_i': "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)" by auto
      have rel0: "(Fun f ss,Fun f (ss[i := ts ! i])) \<in> NS"
      proof -
        have lifted: "(Fun f (take i ss @ ss ! i # drop (Suc i) ss),
            Fun f (take i ss @ ts ! i # drop (Suc i) ss)) \<in> NS"
          by (rule ctxt_closed_one[OF rp.ctxt_NS local_NS])
        have decomp: "ss = take i ss @ ss ! i # drop (Suc i) ss"
          by (rule id_take_nth_drop[OF i])
        have upd: "ss[i := ts ! i] = take i ss @ ts ! i # drop (Suc i) ss"
          by (rule upd_conv_take_nth_drop[OF i])
        show ?thesis
          apply (subst upd)
          apply (subst decomp)
          by (rule lifted)
      qed
      have rel: "(Fun f ss,t) \<in> NS" using rel0 target update by simp
      have safe_t: "muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
      proof (unfold target muterm_innermost_af_ur_safe.simps, intro conjI)
        have not_nf: "Fun f ss \<notin> NF (csstep \<mu> R)"
          using Fun.prems(2) unfolding NF_iff_no_step by blast
        have top: "\<forall>lr\<in>R.
          root (fst lr) = Some (f,length ss) \<longrightarrow> lr \<in> U"
          using Fun.prems(1) not_nf by simp
        show "Fun f ts \<in> NF (csstep \<mu> R) \<or>
          (\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U)"
          using top len by simp
        show "\<forall>j<length ts. j \<in> \<mu> (f,length ts) \<longrightarrow>
          j \<in> \<pi> (f,length ts) \<longrightarrow>
          muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
        proof (intro allI impI)
          fix j
          assume j: "j < length ts"
            and active_j: "j \<in> \<mu> (f,length ts)"
            and retained_j: "j \<in> \<pi> (f,length ts)"
          show "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
          proof (cases "j=i")
            case True
            then show ?thesis using safe_i' by simp
          next
            case False
            have jss: "j < length ss" using j len by simp
            have old: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! j)"
              using Fun.prems(1) jss active_j retained_j len by simp
            show ?thesis using old same[OF jss False] by simp
          qed
        qed
      qed
      show ?thesis using rel safe_t by blast
    next
      case retained: False
      have rel0: "(Fun f ss,Fun f (ss[i := ts ! i])) \<in> NS"
      proof -
        have lifted: "(Fun f (take i ss @ ss ! i # drop (Suc i) ss),
            Fun f (take i ss @ ts ! i # drop (Suc i) ss)) \<in> NS"
          using rp.af_compat[unfolded af_compatible_def, rule_format,
            of "take i ss" f "drop (Suc i) ss"]
            i retained by simp
        have decomp: "ss = take i ss @ ss ! i # drop (Suc i) ss"
          by (rule id_take_nth_drop[OF i])
        have upd: "ss[i := ts ! i] = take i ss @ ts ! i # drop (Suc i) ss"
          by (rule upd_conv_take_nth_drop[OF i])
        show ?thesis
          apply (subst upd)
          apply (subst decomp)
          by (rule lifted)
      qed
      have rel: "(Fun f ss,t) \<in> NS" using rel0 target update by simp
      have safe_t: "muterm_innermost_af_ur_safe R U \<mu> \<pi> t"
      proof (unfold target muterm_innermost_af_ur_safe.simps, intro conjI)
        have not_nf: "Fun f ss \<notin> NF (csstep \<mu> R)"
          using Fun.prems(2) unfolding NF_iff_no_step by blast
        have top: "\<forall>lr\<in>R.
          root (fst lr) = Some (f,length ss) \<longrightarrow> lr \<in> U"
          using Fun.prems(1) not_nf by simp
        show "Fun f ts \<in> NF (csstep \<mu> R) \<or>
          (\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U)"
          using top len by simp
        show "\<forall>j<length ts. j \<in> \<mu> (f,length ts) \<longrightarrow>
          j \<in> \<pi> (f,length ts) \<longrightarrow>
          muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
        proof (intro allI impI)
          fix j
          assume j: "j < length ts"
            and active_j: "j \<in> \<mu> (f,length ts)"
            and retained_j: "j \<in> \<pi> (f,length ts)"
          have not_retained_i: "i \<notin> \<pi> (f,length ts)"
            using retained len by simp
          have jne: "j \<noteq> i" using not_retained_i retained_j by blast
          have jss: "j < length ss" using j len by simp
          have old: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! j)"
            using Fun.prems(1) jss active_j retained_j len by simp
          show "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
            using old same[OF jss jne] by simp
        qed
      qed
      show ?thesis using rel safe_t by blast
    qed
  qed
qed

lemma muterm_innermost_af_ur_safe_sharp_csdp_step:
  fixes R U S NS :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>g n. \<not> defined R (Sharp g,n)"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_af_mu_vars_condition \<mu> \<pi> U"
    and redpair: "af_redpair S NS \<pi>"
    and U_NS: "U \<subseteq> NS"
    and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (Fun (Sharp f) ss)"
    and step: "(Fun (Sharp f) ss,v) \<in> csdp_step Sharp \<mu> R"
  shows "(Fun (Sharp f) ss,v) \<in> NS \<and>
    muterm_innermost_af_ur_safe R U \<mu> \<pi> v \<and>
    (\<exists>ts. v = Fun (Sharp f) ts \<and> length ts = length ss)"
proof -
  interpret rp: af_redpair S NS \<pi> by (rule redpair)
  have step': "(sharp_term Sharp (Fun f ss),v) \<in> csdp_step Sharp \<mu> R"
    using step by simp
  from sharp_csdp_step_imp_csnrstep[
    where shp=Sharp and s="Fun f ss", OF wf fresh inj_Sharp step']
  obtain t where v: "v = sharp_term Sharp t"
    and nonroot: "(Fun f ss,t) \<in> csnrstep \<mu> R" by blast
  from nonroot obtain i ts where
    i: "i < length ss" and active: "i \<in> \<mu> (f,length ss)"
    and t: "t = Fun f ts" and len: "length ts = length ss"
    and local: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      ts ! j = ss ! j" by (metis csnrstep_FunE)
  have active_marked: "i \<in> \<mu> (Sharp f,length ss)"
    using active marked by simp
  have update: "ts = ss[i := ts ! i]"
  proof (rule nth_equalityI)
    show "length ts = length (ss[i := ts ! i])" using len by simp
    fix j
    assume j: "j < length ts"
    show "ts ! j = (ss[i := ts ! i]) ! j"
      by (cases "j=i", use j i len same in auto)
  qed
  have rel: "(Fun (Sharp f) ss,Fun (Sharp f) ts) \<in> NS"
    and safe_i': "i \<in> \<pi> (Sharp f,length ss) \<Longrightarrow>
      muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
  proof -
    show "(Fun (Sharp f) ss,Fun (Sharp f) ts) \<in> NS"
    proof (cases "i \<in> \<pi> (Sharp f,length ss)")
      case True
      have safe_i: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! i)"
        using safe i active_marked True by simp
      have local_result: "(ss ! i,ts ! i) \<in> NS \<and>
          muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
      proof (rule muterm_innermost_af_ur_safe_csstep[
          OF wf subset _ conservative redpair U_NS safe_i local])
        show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
          csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
          by (rule closed)
      qed
      have local_NS: "(ss ! i,ts ! i) \<in> NS" using local_result by blast
      have lifted: "(Fun (Sharp f) (take i ss @ ss ! i # drop (Suc i) ss),
          Fun (Sharp f) (take i ss @ ts ! i # drop (Suc i) ss)) \<in> NS"
        by (rule ctxt_closed_one[OF rp.ctxt_NS local_NS])
      have decomp: "ss = take i ss @ ss ! i # drop (Suc i) ss"
        by (rule id_take_nth_drop[OF i])
      have upd: "ss[i := ts ! i] = take i ss @ ts ! i # drop (Suc i) ss"
        by (rule upd_conv_take_nth_drop[OF i])
      show ?thesis
        apply (subst update)
        apply (subst upd)
        apply (subst decomp)
        by (rule lifted)
    next
      case False
      have lifted: "(Fun (Sharp f) (take i ss @ ss ! i # drop (Suc i) ss),
          Fun (Sharp f) (take i ss @ ts ! i # drop (Suc i) ss)) \<in> NS"
        using rp.af_compat[unfolded af_compatible_def, rule_format,
          of "take i ss" "Sharp f" "drop (Suc i) ss"] i False by simp
      have decomp: "ss = take i ss @ ss ! i # drop (Suc i) ss"
        by (rule id_take_nth_drop[OF i])
      have upd: "ss[i := ts ! i] = take i ss @ ts ! i # drop (Suc i) ss"
        by (rule upd_conv_take_nth_drop[OF i])
      show ?thesis
        apply (subst update)
        apply (subst upd)
        apply (subst decomp)
        by (rule lifted)
    qed
  next
    assume retained: "i \<in> \<pi> (Sharp f,length ss)"
    have safe_i: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! i)"
      using safe i active_marked retained by simp
    have local_result: "(ss ! i,ts ! i) \<in> NS \<and>
        muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
    proof (rule muterm_innermost_af_ur_safe_csstep[
        OF wf subset _ conservative redpair U_NS safe_i local])
      show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
        csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
        by (rule closed)
    qed
    show "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! i)"
      using local_result by blast
  qed
  have safe_children: "\<forall>j<length ts.
      j \<in> \<mu> (Sharp f,length ts) \<longrightarrow>
      j \<in> \<pi> (Sharp f,length ts) \<longrightarrow>
      muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
  proof (intro allI impI)
    fix j
    assume j: "j < length ts"
      and active_j: "j \<in> \<mu> (Sharp f,length ts)"
      and retained_j: "j \<in> \<pi> (Sharp f,length ts)"
    show "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ts ! j)"
    proof (cases "j=i")
      case True
      then show ?thesis using safe_i' retained_j len by simp
    next
      case False
      have jss: "j < length ss" using j len by simp
      have old: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (ss ! j)"
        using safe jss active_j retained_j len by simp
      show ?thesis using old same[OF jss False] by simp
    qed
  qed
  have no_sharp_rules: "\<forall>lr\<in>R.
      root (fst lr) = Some (Sharp f,length ts) \<longrightarrow> lr \<in> U"
  proof (intro ballI impI)
    fix lr
    assume lr: "lr \<in> R" and root: "root (fst lr) = Some (Sharp f,length ts)"
    have "defined R (Sharp f,length ts)"
      unfolding defined_def using lr root by (cases lr, auto)
    with fresh[of f "length ts"] show "lr \<in> U" by contradiction
  qed
  have safe_v: "muterm_innermost_af_ur_safe R U \<mu> \<pi> v"
    using no_sharp_rules safe_children v t by simp
  have rel_v: "(Fun (Sharp f) ss,v) \<in> NS" using rel v t by simp
  show ?thesis using rel_v safe_v v t len by simp
qed

lemma muterm_innermost_af_ur_safe_sharp_csdp_steps:
  fixes R U S NS :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>g n. \<not> defined R (Sharp g,n)"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_af_mu_vars_condition \<mu> \<pi> U"
    and redpair: "af_redpair S NS \<pi>"
    and order: "compat_redpair_order S NS"
    and U_NS: "U \<subseteq> NS"
    and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (Fun (Sharp f) ss)"
    and steps: "(Fun (Sharp f) ss,v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(Fun (Sharp f) ss,v) \<in> NS \<and>
    muterm_innermost_af_ur_safe R U \<mu> \<pi> v \<and>
    (\<exists>ts. v = Fun (Sharp f) ts \<and> length ts = length ss)"
proof -
  interpret rp: af_redpair S NS \<pi> by (rule redpair)
  interpret ord: compat_redpair_order S NS by (rule order)
  let ?s = "Fun (Sharp f) ss"
  from steps safe show ?thesis
  proof (induct rule: rtrancl_induct)
    case base
    have "(?s,?s) \<in> NS" using ord.refl_NS unfolding refl_on_def by blast
    then show ?case using safe by simp
  next
    case (step y z)
    from step.hyps(3)[OF step.prems] obtain ys where
      sy: "(?s,y) \<in> NS"
      and safe_y: "muterm_innermost_af_ur_safe R U \<mu> \<pi> y"
      and y: "y = Fun (Sharp f) ys" and len_y: "length ys = length ss"
      by blast
    have marked_y: "\<mu> (Sharp f,length ys) = \<mu> (f,length ys)"
      using marked len_y by simp
    from muterm_innermost_af_ur_safe_sharp_csdp_step[
      OF wf fresh subset closed conservative redpair U_NS marked_y
        safe_y[unfolded y] step.hyps(2)[unfolded y]]
    have yz: "(y,z) \<in> NS"
      and safe_z: "muterm_innermost_af_ur_safe R U \<mu> \<pi> z"
      and shape_z: "\<exists>zs. z = Fun (Sharp f) zs \<and> length zs = length ys"
      unfolding y by auto
    have sz: "(?s,z) \<in> NS"
      using transD[OF ord.trans_NS sy yz] .
    show ?case using sz safe_z shape_z len_y by auto
  qed
qed

lemma muterm_innermost_ur_safe_mu_subterm:
  assumes safe: "muterm_innermost_ur_safe R U \<mu> t"
    and p: "p \<in> mu_poss \<mu> t"
  shows "muterm_innermost_ur_safe R U \<mu> (t |_ p)"
  using safe p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  from Cons.prems(2) obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
    and p: "p \<in> mu_poss \<mu> (ts ! i)"
    by (cases t) auto
  have child: "muterm_innermost_ur_safe R U \<mu> (ts ! i)"
    using Cons.prems(1) i active unfolding t by simp
  have ih: "muterm_innermost_ur_safe R U \<mu> (ts ! i |_ p)"
    by (rule Cons.hyps[OF child p])
  show ?case unfolding t using i ih by simp
qed

lemma muterm_innermost_ur_safe_subst_safe:
  assumes skeleton: "muterm_innermost_ur_skeleton R U \<mu> t"
    and safe: "\<And>x. x \<in> mu_vars_term \<mu> t \<Longrightarrow>
      muterm_innermost_ur_safe R U \<mu> (\<sigma> x)"
  shows "muterm_innermost_ur_safe R U \<mu> (t \<cdot> \<sigma>)"
  using skeleton safe
proof (induct t)
  case (Var x)
  have x: "x \<in> mu_vars_term \<mu> (Var x)"
    unfolding mu_vars_term_def by simp
  show ?case using Var.prems(2)[OF x] by simp
next
  case (Fun f ts)
  have root_rules: "\<forall>lr\<in>R.
      root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U"
    using Fun.prems(1) by simp
  have children: "muterm_innermost_ur_safe R U \<mu> (ts ! i \<cdot> \<sigma>)"
    if i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)" for i
  proof (rule Fun.hyps[OF nth_mem[OF i]])
    show "muterm_innermost_ur_skeleton R U \<mu> (ts ! i)"
      using Fun.prems(1) i active by simp
  next
    fix x
    assume x: "x \<in> mu_vars_term \<mu> (ts ! i)"
    have "x \<in> mu_vars_term \<mu> (Fun f ts)"
      by (rule mu_vars_term_active_argI[OF i active x])
    then show "muterm_innermost_ur_safe R U \<mu> (\<sigma> x)"
      by (rule Fun.prems(2))
  qed
  show ?case using root_rules children by simp
qed

lemma muterm_innermost_ur_safe_subst:
  assumes skeleton: "muterm_innermost_ur_skeleton R U \<mu> t"
    and normal: "\<And>x. x \<in> mu_vars_term \<mu> t \<Longrightarrow>
      \<sigma> x \<in> NF (csstep \<mu> R)"
  shows "muterm_innermost_ur_safe R U \<mu> (t \<cdot> \<sigma>)"
proof (rule muterm_innermost_ur_safe_subst_safe[OF skeleton])
  fix x
  assume "x \<in> mu_vars_term \<mu> t"
  then show "muterm_innermost_ur_safe R U \<mu> (\<sigma> x)"
    by (rule muterm_innermost_ur_safe_NF[OF normal])
qed

lemma muterm_innermost_ur_safe_csstep:
  assumes wf: "wf_trs R"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and safe: "muterm_innermost_ur_safe R U \<mu> s"
    and step: "(s,t) \<in> csstep \<mu> R"
  shows "(s,t) \<in> csstep \<mu> U \<and>
    muterm_innermost_ur_safe R U \<mu> t"
  using safe step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  from Fun.prems(2) consider
      (root) "(Fun f ss,t) \<in> csrstep \<mu> R"
    | (nonroot) "(Fun f ss,t) \<in> csnrstep \<mu> R"
    unfolding csstep_root_nonroot by blast
  then show ?case
  proof cases
    case root
    from root obtain l r \<sigma> where lr: "(l,r) \<in> R"
      and source: "Fun f ss = l \<cdot> \<sigma>"
      and target: "t = r \<cdot> \<sigma>"
      by (elim csrstepE)
    from wf lr obtain g ls where l: "l = Fun g ls"
      unfolding wf_trs_def by (cases l, auto)
    from source l have g: "g = f" and len: "length ls = length ss"
      by auto
    have not_nf: "Fun f ss \<notin> NF (csstep \<mu> R)"
      using Fun.prems(2) unfolding NF_iff_no_step by blast
    from Fun.prems(1) not_nf have root_rules:
      "\<forall>ab\<in>R. root (fst ab) = Some (f,length ss) \<longrightarrow> ab \<in> U"
      by simp
    have lrU: "(l,r) \<in> U"
      using root_rules lr l g len by simp
    have root_U: "(Fun f ss,t) \<in> csrstep \<mu> U"
      using lrU source target unfolding csrstep_iff_rstep_root
      by (intro exI[of _ "(l,r)"] exI[of _ \<sigma>], simp add: rstep_r_p_s_def')
    have step_U: "(Fun f ss,t) \<in> csstep \<mu> U"
      using root_U unfolding csstep_root_nonroot by blast
    have skeleton_r: "muterm_innermost_ur_skeleton R U \<mu> r"
      by (rule muterm_root_closed_imp_skeleton[OF closed[OF lrU]])
    have subst_safe: "muterm_innermost_ur_safe R U \<mu> (\<sigma> x)"
      if x: "x \<in> mu_vars_term \<mu> r" for x
    proof -
      have xl: "x \<in> mu_vars_term \<mu> l"
        using conservative lrU x unfolding rhs_mu_vars_condition_def by blast
      have active_sub: "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
        by (rule mu_vars_term_subst_mu_supt[OF _ xl], unfold l, simp)
      from active_sub obtain i p where pos: "i # p \<in> mu_poss \<mu> (l \<cdot> \<sigma>)"
        and at: "(l \<cdot> \<sigma>) |_ (i # p) = \<sigma> x"
        unfolding mu_supt_def by blast
      have safe_sub: "muterm_innermost_ur_safe R U \<mu>
          ((l \<cdot> \<sigma>) |_ (i # p))"
        by (rule muterm_innermost_ur_safe_mu_subterm[OF _ pos],
          use Fun.prems(1) source in simp)
      show ?thesis using safe_sub at by simp
    qed
    have safe_t: "muterm_innermost_ur_safe R U \<mu> t"
      unfolding target
      by (rule muterm_innermost_ur_safe_subst_safe[OF skeleton_r subst_safe])
    show ?thesis using step_U safe_t by blast
  next
    case nonroot
    from nonroot obtain i ts where
      i: "i < length ss" and active: "i \<in> \<mu> (f,length ss)"
      and target: "t = Fun f ts" and len: "length ts = length ss"
      and local: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
        ts ! j = ss ! j" by (metis csnrstep_FunE)
    have safe_i: "muterm_innermost_ur_safe R U \<mu> (ss ! i)"
      using Fun.prems(1) i active by simp
    from Fun.hyps[OF nth_mem[OF i], of "ts ! i", OF safe_i local]
    have local_U: "(ss ! i,ts ! i) \<in> csstep \<mu> U"
      and safe_i': "muterm_innermost_ur_safe R U \<mu> (ts ! i)"
      by auto
    have ts_update: "ts = ss[i := ts ! i]"
    proof (rule nth_equalityI)
      show "length ts = length (ss[i := ts ! i])" using len by simp
      fix j
      assume j: "j < length ts"
      show "ts ! j = (ss[i := ts ! i]) ! j"
      proof (cases "j = i")
        case True
        then show ?thesis using i len by simp
      next
        case False
        then show ?thesis using same[of j] j len by simp
      qed
    qed
    have step_U0: "(Fun f ss,Fun f (ss[i := ts ! i])) \<in> csstep \<mu> U"
      by (rule csstep_active_arg_lift[OF i active local_U])
    have step_U: "(Fun f ss,t) \<in> csstep \<mu> U"
      using step_U0 target ts_update by simp
    have not_nf: "Fun f ss \<notin> NF (csstep \<mu> R)"
      using Fun.prems(2) unfolding NF_iff_no_step by blast
    have top_rules: "\<forall>lr\<in>R.
        root (fst lr) = Some (f,length ss) \<longrightarrow> lr \<in> U"
      using Fun.prems(1) not_nf by simp
    have safe_t: "muterm_innermost_ur_safe R U \<mu> t"
    proof (unfold target muterm_innermost_ur_safe.simps, intro conjI)
      show "Fun f ts \<in> NF (csstep \<mu> R) \<or>
        (\<forall>lr\<in>R. root (fst lr) = Some (f,length ts) \<longrightarrow> lr \<in> U)"
        using top_rules len by simp
      show "\<forall>j<length ts. j \<in> \<mu> (f,length ts) \<longrightarrow>
        muterm_innermost_ur_safe R U \<mu> (ts ! j)"
      proof (intro allI impI)
        fix j
        assume j: "j < length ts" and active_j: "j \<in> \<mu> (f,length ts)"
        show "muterm_innermost_ur_safe R U \<mu> (ts ! j)"
        proof (cases "j = i")
          case True
          then show ?thesis using safe_i' by simp
        next
          case False
          have j_ss: "j < length ss" using j len by simp
          have active_ss: "j \<in> \<mu> (f,length ss)" using active_j len by simp
          have safe_j: "muterm_innermost_ur_safe R U \<mu> (ss ! j)"
            using Fun.prems(1) j_ss active_ss by simp
          show ?thesis using safe_j same[OF j_ss False] by simp
        qed
      qed
    qed
    show ?thesis using step_U safe_t by blast
  qed
qed

lemma muterm_innermost_ur_safe_cssteps:
  assumes wf: "wf_trs R"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and safe: "muterm_innermost_ur_safe R U \<mu> s"
    and steps: "(s,t) \<in> (csstep \<mu> R)\<^sup>*"
  shows "(s,t) \<in> (csstep \<mu> U)\<^sup>* \<and>
    muterm_innermost_ur_safe R U \<mu> t"
  using steps safe
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step.hyps(3)[OF step.prems]
  have prefix: "(s,y) \<in> (csstep \<mu> U)\<^sup>*"
    and safe_y: "muterm_innermost_ur_safe R U \<mu> y" by auto
  from muterm_innermost_ur_safe_csstep[
    OF wf subset closed conservative safe_y step.hyps(2)]
  have yz: "(y,z) \<in> csstep \<mu> U"
    and safe_z: "muterm_innermost_ur_safe R U \<mu> z" by auto
  show ?case using prefix yz safe_z by auto
qed

lemma marked_mu_var_is_root_supt:
  fixes \<mu> :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab) \<times> nat)
    \<Rightarrow> nat set"
  assumes shape: "l = Fun (Sharp f) ls"
    and marked: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and x: "x \<in> mu_vars_term \<mu> l"
  shows "csr_dp_root_supt \<mu> l (Var x)"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l"
    and at: "l |_ p = Var x"
    unfolding mu_vars_term_def by blast
  from shape at have p_ne: "p \<noteq> []" by (cases p) auto
  then obtain i q where pq: "p = i # q" by (cases p, auto)
  from p[unfolded shape pq] have i: "i < length ls"
    and active: "i \<in> \<mu> (Sharp f,length ls)"
    and q: "q \<in> mu_poss \<mu> (ls ! i)" by auto
  have active': "i \<in> \<mu> (f,length ls)" using active marked by simp
  have pos: "i # q \<in> mu_poss \<mu> (Fun f ls)"
    using i active' q by auto
  have sub: "Fun f ls |_ (i # q) = Var x"
    using shape at pq i by simp
  show ?thesis unfolding csr_dp_root_supt_def shape mu_supt_def
    using pos sub by auto
qed

lemma innermost_pair_source_active_subst_NF:
  fixes \<mu> :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab) \<times> nat)
    \<Rightarrow> nat set"
  assumes source: "innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>)"
    and shape: "l = Fun (Sharp f) ls"
    and marked: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and x: "x \<in> mu_vars_term \<mu> l"
  shows "\<sigma> x \<in> NF (csstep \<mu> R)"
proof -
  have active: "csr_dp_root_supt \<mu> l (Var x)"
    by (rule marked_mu_var_is_root_supt[OF shape marked x])
  from innermost_pair_source_root_supt_NF[OF source active]
  show ?thesis by simp
qed

lemma muterm_innermost_ur_safe_sharp_csdp_step:
  fixes R U :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>g n. \<not> defined R (Sharp g,n)"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and safe: "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)"
    and step: "(Fun (Sharp f) ss,v) \<in> csdp_step Sharp \<mu> R"
  shows "(Fun (Sharp f) ss,v) \<in> csdp_step Sharp \<mu> U \<and>
    muterm_innermost_ur_safe R U \<mu> v \<and>
    (\<exists>ts. v = Fun (Sharp f) ts \<and> length ts = length ss)"
proof -
  have step': "(sharp_term Sharp (Fun f ss),v) \<in> csdp_step Sharp \<mu> R"
    using step by simp
  from sharp_csdp_step_imp_csnrstep[
    where shp=Sharp and s="Fun f ss", OF wf fresh inj_Sharp step']
  obtain t where v: "v = sharp_term Sharp t"
    and nonroot: "(Fun f ss,t) \<in> csnrstep \<mu> R" by blast
  from nonroot obtain i ts where
    i: "i < length ss" and active: "i \<in> \<mu> (f,length ss)"
    and t: "t = Fun f ts" and len: "length ts = length ss"
    and local: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      ts ! j = ss ! j" by (metis csnrstep_FunE)
  have active_marked: "i \<in> \<mu> (Sharp f,length ss)"
    using active marked by simp
  have safe_i: "muterm_innermost_ur_safe R U \<mu> (ss ! i)"
    using safe i active_marked by simp
  from muterm_innermost_ur_safe_csstep[
    OF wf subset closed conservative safe_i local]
  have local_U: "(ss ! i,ts ! i) \<in> csstep \<mu> U"
    and safe_i': "muterm_innermost_ur_safe R U \<mu> (ts ! i)" by auto
  have ts_update: "ts = ss[i := ts ! i]"
  proof (rule nth_equalityI)
    show "length ts = length (ss[i := ts ! i])" using len by simp
    fix j
    assume j: "j < length ts"
    show "ts ! j = (ss[i := ts ! i]) ! j"
    proof (cases "j = i")
      case True
      then show ?thesis using i len by simp
    next
      case False
      then show ?thesis using same[of j] j len by simp
    qed
  qed
  have nonroot_U: "(Fun f ss,Fun f ts) \<in> csnrstep \<mu> U"
    using csstep_FunI[OF i active local_U] ts_update by simp
  have step_U0: "(sharp_term Sharp (Fun f ss),sharp_term Sharp (Fun f ts))
      \<in> csdp_step Sharp \<mu> U"
    by (rule sharp_csnrstep_imp_csdp_step[OF nonroot_U])
  have step_U: "(Fun (Sharp f) ss,Fun (Sharp f) ts) \<in> csdp_step Sharp \<mu> U"
    using step_U0 by simp
  have safe_children: "\<forall>j<length ts. j \<in> \<mu> (Sharp f,length ts)
      \<longrightarrow> muterm_innermost_ur_safe R U \<mu> (ts ! j)"
  proof (intro allI impI)
    fix j
    assume j: "j < length ts"
      and active_j: "j \<in> \<mu> (Sharp f,length ts)"
    show "muterm_innermost_ur_safe R U \<mu> (ts ! j)"
    proof (cases "j = i")
      case True
      then show ?thesis using safe_i' by simp
    next
      case False
      have j_ss: "j < length ss" using j len by simp
      have active_old: "j \<in> \<mu> (Sharp f,length ss)"
        using active_j len by simp
      have safe_j: "muterm_innermost_ur_safe R U \<mu> (ss ! j)"
        using safe j_ss active_old by simp
      show ?thesis using safe_j same[OF j_ss False] by simp
    qed
  qed
  have no_sharp_rules: "\<forall>lr\<in>R.
      root (fst lr) = Some (Sharp f,length ts) \<longrightarrow> lr \<in> U"
  proof (intro ballI impI)
    fix lr
    assume lr: "lr \<in> R" and root: "root (fst lr) = Some (Sharp f,length ts)"
    have "defined R (Sharp f,length ts)"
      unfolding defined_def using lr root by (cases lr, auto)
    with fresh[of f "length ts"] show "lr \<in> U" by contradiction
  qed
  have safe_marked: "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ts)"
    using no_sharp_rules safe_children by simp
  have safe_v: "muterm_innermost_ur_safe R U \<mu> v"
    using safe_marked v t by simp
  show ?thesis using step_U safe_v v t len by simp
qed

lemma muterm_innermost_ur_safe_sharp_csdp_steps:
  fixes R U :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>g n. \<not> defined R (Sharp g,n)"
    and subset: "U \<subseteq> R"
    and closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and safe: "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)"
    and steps: "(Fun (Sharp f) ss,v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(Fun (Sharp f) ss,v) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
    muterm_innermost_ur_safe R U \<mu> v \<and>
    (\<exists>ts. v = Fun (Sharp f) ts \<and> length ts = length ss)"
proof -
  let ?s = "Fun (Sharp f) ss"
  have general: "\<And>f ss. y = Fun (Sharp f) ss \<Longrightarrow>
      muterm_innermost_ur_safe R U \<mu> y \<Longrightarrow>
      (?s,y) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<Longrightarrow>
      (y,z) \<in> (csdp_step Sharp \<mu> R)\<^sup>* \<Longrightarrow>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss) \<Longrightarrow>
      (?s,z) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
      muterm_innermost_ur_safe R U \<mu> z \<and>
      (\<exists>ts. z = Fun (Sharp f) ts \<and> length ts = length ss)"
    for y z
  proof -
    fix f ss
    assume y: "y = Fun (Sharp f) ss"
      and safe_y: "muterm_innermost_ur_safe R U \<mu> y"
      and prefix: "(?s,y) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
      and yz: "(y,z) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      and marked_y: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    from yz safe_y prefix y show
      "(?s,z) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
       muterm_innermost_ur_safe R U \<mu> z \<and>
       (\<exists>ts. z = Fun (Sharp f) ts \<and> length ts = length ss)"
    proof (induct rule: rtrancl_induct)
      case base
      then show ?case by auto
    next
      case (step a b)
      from step.hyps(3)[OF step.prems(1-3)] obtain as where
        prefix_a: "(?s,a) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
        and safe_a: "muterm_innermost_ur_safe R U \<mu> a"
        and a: "a = Fun (Sharp f) as" and len_a: "length as = length ss"
        by blast
      have marked_a: "\<mu> (Sharp f,length as) = \<mu> (f,length as)"
      proof -
        have "\<mu> (Sharp f,length as) = \<mu> (Sharp f,length ss)"
          using len_a by simp
        also have "... = \<mu> (f,length ss)" by (rule marked_y)
        also have "... = \<mu> (f,length as)" using len_a by simp
        finally show ?thesis .
      qed
      from muterm_innermost_ur_safe_sharp_csdp_step[
        OF wf fresh subset closed conservative marked_a safe_a[unfolded a]
          step.hyps(2)[unfolded a]]
      have ab_U: "(a,b) \<in> csdp_step Sharp \<mu> U"
        and safe_b: "muterm_innermost_ur_safe R U \<mu> b"
        and shape_b: "\<exists>bs. b = Fun (Sharp f) bs \<and> length bs = length as"
        unfolding a by auto
      show ?case using prefix_a ab_U safe_b shape_b len_a by auto
    qed
  qed
  show ?thesis
    by (rule general[OF refl safe rtrancl_refl steps marked])
qed

text \<open>
  A typed MU-TERM macro target is a suitable entry point for the innermost
  usable-rule simulation when it is a marked term, its marked replacement map
  agrees with the underlying symbol, and all of its active subterms are
  covered by the supplied usable rules.  Keeping this invariant on concrete
  macro steps avoids imposing the stronger (and unnecessary) conservativity
  condition on their variable-renamed expanded presentation.
\<close>

definition muterm_innermost_typed_target_safe where
  "muterm_innermost_typed_target_safe R U \<mu> P S \<longleftrightarrow>
    (\<forall>a b. (a,b) \<in> muterm_innermost_typed_pair_step Sharp \<mu> R P S
      \<longrightarrow> (\<exists>f bs. b = Fun (Sharp f) bs \<and>
        \<mu> (Sharp f,length bs) = \<mu> (f,length bs) \<and>
        muterm_innermost_ur_safe R U \<mu> b))"

lemma muterm_innermost_typed_target_safeD:
  assumes safe: "muterm_innermost_typed_target_safe R U \<mu> P S"
    and step: "(a,b) \<in> muterm_innermost_typed_pair_step Sharp \<mu> R P S"
  obtains f bs where "b = Fun (Sharp f) bs"
    "\<mu> (Sharp f,length bs) = \<mu> (f,length bs)"
    "muterm_innermost_ur_safe R U \<mu> b"
  using safe step unfolding muterm_innermost_typed_target_safe_def by blast

lemma muterm_innermost_typed_relto_target_safe:
  fixes R U T P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v::infinite) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> T"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and target: "muterm_innermost_typed_target_safe R U \<mu> P S"
    and step: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_innermost_typed_pair_step Sharp \<mu> R P S O
      (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>f ts. t = Fun (Sharp f) ts \<and>
      \<mu> (Sharp f,length ts) = \<mu> (f,length ts) \<and>
      muterm_innermost_ur_safe R U \<mu> t"
proof -
  from step obtain a b where event:
      "(a,b) \<in> muterm_innermost_typed_pair_step Sharp \<mu> R P S"
    and suffix: "(b,t) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  from muterm_innermost_typed_target_safeD[OF target event]
  obtain f bs where b: "b = Fun (Sharp f) bs"
    and marked: "\<mu> (Sharp f,length bs) = \<mu> (f,length bs)"
    and safe: "muterm_innermost_ur_safe R U \<mu> b" by blast
  have full: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    using suffix rtrancl_mono[OF innermost_csdp_step_subset_csdp_step]
    by blast
  from closed have subset: "U \<subseteq> R"
    and rules: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have full': "(Fun (Sharp f) bs,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    using full unfolding b .
  have safe': "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) bs)"
    using safe unfolding b .
  have result: "(Fun (Sharp f) bs,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
      muterm_innermost_ur_safe R U \<mu> t \<and>
      (\<exists>ts. t = Fun (Sharp f) ts \<and> length ts = length bs)"
  proof (rule muterm_innermost_ur_safe_sharp_csdp_steps[
      where R=R and U=U and \<mu>=\<mu>])
    show "wf_trs R" by (rule wf)
    show "\<And>g n. \<not> defined R (Sharp g,n)" by (rule fresh)
    show "U \<subseteq> R" by (rule subset)
    show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)" by (rule rules)
    show "rhs_mu_vars_condition \<mu> U" by (rule conservative)
    show "\<mu> (Sharp f,length bs) = \<mu> (f,length bs)" by (rule marked)
    show "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) bs)" by (rule safe')
    show "(Fun (Sharp f) bs,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by (rule full')
  qed
  from result obtain ts where t: "t = Fun (Sharp f) ts"
    and len: "length ts = length bs"
    and safe_t: "muterm_innermost_ur_safe R U \<mu> t" by blast
  have marked_t: "\<mu> (Sharp f,length ts) = \<mu> (f,length ts)"
    using marked len by simp
  show ?thesis using t marked_t safe_t by blast
qed

lemma muterm_innermost_typed_relto_transfer_expanded:
  fixes R U T P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v::infinite) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> T"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and target: "muterm_innermost_typed_target_safe R U \<mu> P S"
    and safe_s: "\<exists>f ss. s = Fun (Sharp f) ss \<and>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss) \<and>
      muterm_innermost_ur_safe R U \<mu> s"
    and step: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_innermost_typed_pair_step Sharp \<mu> R P S O
      (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s,t) \<in> (rstep U)\<^sup>* O
      rrstep (muterm_expanded_pairs ren P S) O (rstep U)\<^sup>* \<and>
    (\<exists>f ts. t = Fun (Sharp f) ts \<and>
      \<mu> (Sharp f,length ts) = \<mu> (f,length ts) \<and>
      muterm_innermost_ur_safe R U \<mu> t)"
proof -
  from step obtain a b where prefix:
      "(s,a) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    and event:
      "(a,b) \<in> muterm_innermost_typed_pair_step Sharp \<mu> R P S"
    and suffix: "(b,t) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  from safe_s obtain f ss where s: "s = Fun (Sharp f) ss"
    and marked_s: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and safe0: "muterm_innermost_ur_safe R U \<mu> s" by blast
  from closed have subset: "U \<subseteq> R"
    and rules: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have prefix_full: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    using prefix rtrancl_mono[OF innermost_csdp_step_subset_csdp_step]
    by blast
  have safe0': "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)"
    using safe0 unfolding s .
  have prefix_full': "(Fun (Sharp f) ss,a) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*" using prefix_full unfolding s .
  have prefix_result:
      "(Fun (Sharp f) ss,a) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
       muterm_innermost_ur_safe R U \<mu> a \<and>
       (\<exists>ts. a = Fun (Sharp f) ts \<and> length ts = length ss)"
  proof (rule muterm_innermost_ur_safe_sharp_csdp_steps[
      where R=R and U=U and \<mu>=\<mu>])
    show "wf_trs R" by (rule wf)
    show "\<And>g n. \<not> defined R (Sharp g,n)" by (rule fresh)
    show "U \<subseteq> R" by (rule subset)
    show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)" by (rule rules)
    show "rhs_mu_vars_condition \<mu> U" by (rule conservative)
    show "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)" by (rule marked_s)
    show "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)" by (rule safe0')
    show "(Fun (Sharp f) ss,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      by (rule prefix_full')
  qed
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    using prefix_result unfolding s by blast
  have prefix_r: "(s,a) \<in> (rstep U)\<^sup>*"
  proof (rule rtrancl_mono[THEN subsetD, OF _ prefix_U])
    show "csdp_step Sharp \<mu> U \<subseteq> rstep U"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
  qed
  have expanded: "(a,b) \<in> rrstep (muterm_expanded_pairs ren P S)"
    using event unfolding muterm_innermost_typed_pair_step_def
    using muterm_typed_pair_step_subset_expanded by blast
  from muterm_innermost_typed_target_safeD[OF target event]
  obtain g bs where b: "b = Fun (Sharp g) bs"
    and marked_b: "\<mu> (Sharp g,length bs) = \<mu> (g,length bs)"
    and safe_b: "muterm_innermost_ur_safe R U \<mu> b" by blast
  have suffix_full: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    using suffix rtrancl_mono[OF innermost_csdp_step_subset_csdp_step]
    by blast
  have safe_b': "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp g) bs)"
    using safe_b unfolding b .
  have suffix_full': "(Fun (Sharp g) bs,t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*" using suffix_full unfolding b .
  have suffix_result:
      "(Fun (Sharp g) bs,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
       muterm_innermost_ur_safe R U \<mu> t \<and>
       (\<exists>ts. t = Fun (Sharp g) ts \<and> length ts = length bs)"
  proof (rule muterm_innermost_ur_safe_sharp_csdp_steps[
      where R=R and U=U and \<mu>=\<mu>])
    show "wf_trs R" by (rule wf)
    show "\<And>h n. \<not> defined R (Sharp h,n)" by (rule fresh)
    show "U \<subseteq> R" by (rule subset)
    show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)" by (rule rules)
    show "rhs_mu_vars_condition \<mu> U" by (rule conservative)
    show "\<mu> (Sharp g,length bs) = \<mu> (g,length bs)" by (rule marked_b)
    show "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp g) bs)" by (rule safe_b')
    show "(Fun (Sharp g) bs,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      by (rule suffix_full')
  qed
  from suffix_result obtain ts where suffix_U0:
      "(Fun (Sharp g) bs,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    and safe_t: "muterm_innermost_ur_safe R U \<mu> t"
    and t: "t = Fun (Sharp g) ts" and len: "length ts = length bs"
    by blast
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    using suffix_U0 unfolding b .
  have suffix_r: "(b,t) \<in> (rstep U)\<^sup>*"
  proof (rule rtrancl_mono[THEN subsetD, OF _ suffix_U])
    show "csdp_step Sharp \<mu> U \<subseteq> rstep U"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
  qed
  have marked_t: "\<mu> (Sharp g,length ts) = \<mu> (g,length ts)"
    using marked_b len by simp
  show ?thesis using prefix_r expanded suffix_r t marked_t safe_t by auto
qed

theorem finite_muterm_innermost_typed_dpp_expanded_usable:
  fixes R U T P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v::infinite) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> T"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and target: "muterm_innermost_typed_target_safe R U \<mu> P S"
    and fin: "finite_dpp (False,False,
      muterm_expanded_pairs ren P S,{},{},{},U)"
  shows "finite_muterm_innermost_typed_dpp Sharp \<mu> R P S"
proof (unfold finite_muterm_innermost_typed_dpp_def SN_rel_on_def SN_on_def,
    intro notI)
  let ?A = "(innermost_csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_innermost_typed_pair_step Sharp \<mu> R P S O
    (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
  let ?B = "(rstep U)\<^sup>* O
    rrstep (muterm_expanded_pairs ren P S) O (rstep U)\<^sup>*"
  assume "\<exists>f. f 0 \<in> UNIV \<and> (\<forall>n. (f n,f (Suc n)) \<in> ?A)"
  then obtain f where chain: "\<And>n. (f n,f (Suc n)) \<in> ?A" by auto
  from muterm_innermost_typed_relto_target_safe[
      OF wf fresh closed conservative target chain[of 0]]
  have safe_1: "\<exists>g ss. f (Suc 0) = Fun (Sharp g) ss \<and>
      \<mu> (Sharp g,length ss) = \<mu> (g,length ss) \<and>
      muterm_innermost_ur_safe R U \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have safe_g: "\<exists>h ss. ?g n = Fun (Sharp h) ss \<and>
      \<mu> (Sharp h,length ss) = \<mu> (h,length ss) \<and>
      muterm_innermost_ur_safe R U \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using safe_1 by simp
  next
    case (Suc n)
    from muterm_innermost_typed_relto_transfer_expanded[
      OF wf fresh closed conservative target Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n,?g (Suc n)) \<in> ?B" for n
    using muterm_innermost_typed_relto_transfer_expanded[
      OF wf fresh closed conservative target safe_g[of n] chain[of "Suc n"]]
    by auto
  from fin have sn: "SN ?B"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have not_sn: "\<not> SN ?B"
    by (rule not_SN_onI[of ?g], simp, simp add: chain_def g_step)
  from not_sn sn show False ..
qed

lemma muterm_innermost_pair_target_safe:
  fixes R U P :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes closed: "muterm_innermost_ur_closed R U \<mu> P"
    and conservative: "rhs_mu_vars_condition \<mu> P"
    and pair: "(l,r) \<in> P"
    and lhs: "l = Fun (Sharp f) ls"
    and rhs: "r = Fun (Sharp g) rs"
    and marked: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and source: "innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>)"
  shows "muterm_innermost_ur_safe R U \<mu> (r \<cdot> \<sigma>)"
proof -
  from closed pair rhs have roots:
      "csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have skeleton: "muterm_innermost_ur_skeleton R U \<mu> r"
    by (rule muterm_root_closed_imp_skeleton[OF roots])
  have normal: "\<sigma> x \<in> NF (csstep \<mu> R)"
    if x: "x \<in> mu_vars_term \<mu> r" for x
  proof -
    have xl: "x \<in> mu_vars_term \<mu> l"
      using conservative pair x unfolding rhs_mu_vars_condition_def by blast
    show ?thesis
      by (rule innermost_pair_source_active_subst_NF[
        OF source lhs marked xl])
  qed
  show ?thesis
    by (rule muterm_innermost_ur_safe_subst[OF skeleton normal])
qed

lemma muterm_innermost_af_pair_target_safe:
  fixes R U P :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes closed: "muterm_innermost_ur_closed R U \<mu> P"
    and conservative: "rhs_pair_af_mu_vars_condition \<mu> \<pi> P"
    and pair: "(l,r) \<in> P"
    and lhs: "l = Fun (Sharp f) ls"
    and rhs: "r = Fun (Sharp g) rs"
    and marked: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and source: "innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>)"
  shows "muterm_innermost_af_ur_safe R U \<mu> \<pi> (r \<cdot> \<sigma>)"
proof -
  from closed pair rhs have roots:
      "csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have skeleton: "muterm_innermost_af_ur_skeleton R U \<mu> \<pi> r"
    by (rule muterm_root_closed_imp_af_skeleton[OF roots])
  have normal: "\<sigma> x \<in> NF (csstep \<mu> R)"
    if x: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) r" for x
  proof -
    have xl: "x \<in> mu_vars_term \<mu> l"
      using conservative pair x unfolding rhs_pair_af_mu_vars_condition_def by blast
    show ?thesis
      by (rule innermost_pair_source_active_subst_NF[
        OF source lhs marked xl])
  qed
  have safe_subst: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (\<sigma> x)"
    if x: "x \<in> mu_vars_term (af_inter \<pi> \<mu>) r" for x
    by (rule muterm_innermost_af_ur_safe_NF[OF normal[OF x]])
  show ?thesis
    by (rule muterm_innermost_af_ur_safe_subst_safe[OF skeleton safe_subst])
qed

theorem finite_innermost_csr_dpp_redpair_simulation:
  fixes P S NS R :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and simulation:
      "\<And>s t \<sigma>.
        (\<And>k. (s k,t k) \<in> P) \<Longrightarrow>
        (\<And>k. innermost_pair_source Sharp \<mu> R (s k \<cdot> \<sigma> k)) \<Longrightarrow>
        (\<And>k. (t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
          \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*) \<Longrightarrow>
        \<exists>\<tau>. \<forall>k. (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> (P - S) R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof (rule ccontr)
  interpret compat_redpair_order S NS by (rule redpair)
  let ?RS = "innermost_csdp_step Sharp \<mu> R"
  let ?RP = "innermost_rrstep Sharp \<mu> R P"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  assume not_fin: "\<not> finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
  then obtain ch where chain: "\<And>k. (ch k,ch (Suc k)) \<in> ?rel"
    unfolding finite_mode_csr_dpp_def SN_rel_on_def SN_on_def by auto
  have witnesses: "\<forall>k. \<exists>l r \<sigma>.
      (l,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>) \<and>
      (ch k,l \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*"
  proof
    fix k
    from chain[of k] obtain a b where pre: "(ch k,a) \<in> ?RS\<^sup>*"
      and strict: "(a,b) \<in> ?RP"
      and post: "(b,ch (Suc k)) \<in> ?RS\<^sup>*" by auto
    from strict have root: "(a,b) \<in> rrstep P"
      and source: "innermost_pair_source Sharp \<mu> R a"
      unfolding innermost_rrstep_def by auto
    from rrstepE[OF root] obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>" .
    show "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>) \<and>
      (ch k,l \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*"
      using pair source pre post a b by blast
  qed
  from choice[OF witnesses] obtain s where choose_s: "\<forall>k. \<exists>r \<sigma>.
      (s k,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (s k \<cdot> \<sigma>) \<and>
      (ch k,s k \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from choice[OF choose_s] obtain t where choose_t: "\<forall>k. \<exists>\<sigma>.
      (s k,t k) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (s k \<cdot> \<sigma>) \<and>
      (ch k,s k \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (t k \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>k.
      (s k,t k) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (s k \<cdot> \<sigma> k) \<and>
      (ch k,s k \<cdot> \<sigma> k) \<in> ?RS\<^sup>* \<and>
      (t k \<cdot> \<sigma> k,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from chosen have pair: "\<And>k. (s k,t k) \<in> P"
    and source: "\<And>k. innermost_pair_source Sharp \<mu> R (s k \<cdot> \<sigma> k)"
    and pre: "\<And>k. (ch k,s k \<cdot> \<sigma> k) \<in> ?RS\<^sup>*"
    and post: "\<And>k. (t k \<cdot> \<sigma> k,ch (Suc k)) \<in> ?RS\<^sup>*"
    by blast+
  have steps: "\<And>k. (t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
      \<in> ?RS\<^sup>*"
    using post pre by (meson rtrancl_trans)
  from simulation[of s t \<sigma>, OF pair source steps]
  obtain \<tau> where sim: "\<And>k.
      (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS" by blast
  let ?x = "\<lambda>k. s k \<cdot> \<tau> k"
  let ?y = "\<lambda>k. t k \<cdot> \<tau> k"
  have pair_ord: "(?x k,?y k) \<in> S \<union> NS" for k
    using orient pair[of k] subst_S subst_NS
    by (auto simp: subst.closed_def)
  have x_step: "(?x k,?x (Suc k)) \<in> S \<union> NS" for k
  proof (cases "(?x k,?y k) \<in> S")
    case True
    from compat_S_NS True sim[of k] show ?thesis by blast
  next
    case False
    with pair_ord[of k] have weak: "(?x k,?y k) \<in> NS" by blast
    from trans_NS_point[OF weak sim[of k]] show ?thesis by blast
  qed
  have x_chain: "chain (NS \<union> S) ?x"
    using x_step by (simp add: Un_commute)
  have sn_x0: "SN_on S {?x 0}" using SN unfolding SN_on_def by auto
  from non_strict_ending[OF x_chain compat_NS_S sn_x0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?x k,?x (Suc k)) \<in> NS - S" by auto
  have pair_tail: "(s (k+j),t (k+j)) \<in> P - S" for k
  proof (rule DiffI)
    show "(s (k+j),t (k+j)) \<in> P" by (rule pair)
    show "(s (k+j),t (k+j)) \<notin> S"
    proof
      assume rule_S: "(s (k+j),t (k+j)) \<in> S"
      from subst.closedD[OF subst_S rule_S]
      have inst_S: "(?x (k+j),?y (k+j)) \<in> S" .
      from compat_S_NS inst_S sim[of "k+j"]
      have strict_step: "(?x (k+j),?x (Suc (k+j))) \<in> S" by blast
      from tail[of "k+j"] strict_step show False by auto
    qed
  qed
  let ?ss = "shift s j"
  let ?tt = "shift t j"
  let ?sub = "shift \<sigma> j"
  let ?RPres = "innermost_rrstep Sharp \<mu> R (P - S)"
  let ?relres = "?RS\<^sup>* O ?RPres O ?RS\<^sup>*"
  let ?vals = "\<lambda>k. ?ss k \<cdot> ?sub k"
  have rel_step: "(?vals k,?vals (Suc k)) \<in> ?relres" for k
  proof -
    have pk: "(?ss k,?tt k) \<in> P - S" using pair_tail[of k] by simp
    have src: "innermost_pair_source Sharp \<mu> R (?ss k \<cdot> ?sub k)"
      using source[of "k+j"] by simp
    have rr: "(?ss k \<cdot> ?sub k,?tt k \<cdot> ?sub k) \<in> rrstep (P-S)"
      unfolding rrstep_def'
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (rule exI[where x = "?ss k"])
      apply (rule exI[where x = "?tt k"])
      apply (rule exI[where x = "?sub k"])
      using pk
      apply simp
      done
    have strict: "(?ss k \<cdot> ?sub k,?tt k \<cdot> ?sub k) \<in> ?RPres"
      unfolding innermost_rrstep_def using rr src by blast
    have bridge: "(?tt k \<cdot> ?sub k,?ss (Suc k) \<cdot> ?sub (Suc k))
        \<in> ?RS\<^sup>*" using steps[of "k+j"] by simp
    show ?thesis using strict bridge by auto
  qed
  have vals_chain: "chain ?relres ?vals" using rel_step by simp
  have not_sn: "\<not> SN_on ?relres UNIV"
    by (rule not_SN_onI[OF _ vals_chain], simp)
  from fin have sn: "SN_on ?relres UNIV"
    unfolding finite_mode_csr_dpp_def SN_rel_on_def by simp
  from not_sn sn show False by contradiction
qed

theorem finite_innermost_csr_dpp_muterm_ur_redpair:
  fixes R U P S NS :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> P"
    and conservative: "rhs_mu_vars_condition \<mu> (P \<union> U)"
    and marked: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and U_NS: "U \<subseteq> NS"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> (P - S) R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof -
  interpret rp: compat_redpair_order S NS by (rule redpair)
  from closed have U_R: "U \<subseteq> R"
    and U_closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have cons_P: "rhs_mu_vars_condition \<mu> P"
    and cons_U: "rhs_mu_vars_condition \<mu> U"
    using conservative unfolding rhs_mu_vars_condition_def by auto
  have weak_step: "csdp_step Sharp \<mu> U \<subseteq> NS"
  proof -
    have "csdp_step Sharp \<mu> U \<subseteq> rstep U"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    also have "... \<subseteq> rstep NS" by (rule rstep_mono[OF U_NS])
    also have "... \<subseteq> NS" by (rule rp.rstep_NS)
    finally show ?thesis .
  qed
  have weak_steps: "(csdp_step Sharp \<mu> U)\<^sup>* \<subseteq> NS"
  proof -
    have "(csdp_step Sharp \<mu> U)\<^sup>* \<subseteq> NS\<^sup>*"
      by (rule rtrancl_mono[OF weak_step])
    also have "... = NS" by (rule rp.rtrancl_NS)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule finite_innermost_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k,t k) \<in> P"
      and source: "\<And>k. innermost_pair_source Sharp \<mu> R
        (s k \<cdot> \<sigma> k)"
      and steps: "\<And>k. (t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
        \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
    proof (rule exI[where x=\<sigma>], intro allI)
      fix k
      from pair_shape pair[of k] obtain f ls g rs where
        lhs: "s k = Fun (Sharp f) ls" and rhs: "t k = Fun (Sharp g) rs"
        by auto
      have marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
        using marked pair[of k] lhs by blast
      have marked_r: "\<mu> (Sharp g,length rs) = \<mu> (g,length rs)"
        using marked pair[of k] rhs by blast
      have safe: "muterm_innermost_ur_safe R U \<mu> (t k \<cdot> \<sigma> k)"
        by (rule muterm_innermost_pair_target_safe[
          OF closed cons_P pair[of k] lhs rhs marked_l source[of k]])
      have full_steps: "(t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
          \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps[of k]
          rtrancl_mono[OF innermost_csdp_step_subset_csdp_step] by blast
      let ?args = "map (\<lambda>x. x \<cdot> \<sigma> k) rs"
      have marked_args: "\<mu> (Sharp g,length ?args) = \<mu> (g,length ?args)"
        using marked_r by simp
      have safe_args: "muterm_innermost_ur_safe R U \<mu>
          (Fun (Sharp g) ?args)"
        using safe unfolding rhs by simp
      have full_args: "(Fun (Sharp g) ?args,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
        using full_steps unfolding rhs by simp
      have usable_result: "(Fun (Sharp g) ?args,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
          muterm_innermost_ur_safe R U \<mu> (s (Suc k) \<cdot> \<sigma> (Suc k)) \<and>
          (\<exists>ts. s (Suc k) \<cdot> \<sigma> (Suc k) = Fun (Sharp g) ts \<and>
            length ts = length ?args)"
      proof (rule muterm_innermost_ur_safe_sharp_csdp_steps[
          where R=R and U=U and \<mu>=\<mu> and f=g and ss="?args" and
            v="s (Suc k) \<cdot> \<sigma> (Suc k)"])
        show "wf_trs R" by (rule wf)
        show "\<And>g n. \<not> defined R (Sharp g,n)" by (rule fresh)
        show "U \<subseteq> R" by (rule U_R)
        show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
          csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
          by (rule U_closed)
        show "rhs_mu_vars_condition \<mu> U" by (rule cons_U)
        show "\<mu> (Sharp g,length ?args) = \<mu> (g,length ?args)"
          by (rule marked_args)
        show "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp g) ?args)"
          by (rule safe_args)
        show "(Fun (Sharp g) ?args,s (Suc k) \<cdot> \<sigma> (Suc k))
          \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by (rule full_args)
      qed
      from usable_result have usable_steps: "(Fun (Sharp g) ?args,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
        by blast
      have "(t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
          \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
        using usable_steps unfolding rhs by simp
      then show "(t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> NS"
        by (rule weak_steps[THEN subsetD])
    qed
  qed
qed

theorem finite_innermost_csr_dpp_muterm_af_ur_redpair:
  fixes R U P S NS :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> P"
    and conservative_pairs: "rhs_pair_af_mu_vars_condition \<mu> \<pi> P"
    and conservative_rules: "rhs_af_mu_vars_condition \<mu> \<pi> U"
    and marked: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and redpair: "compat_redpair_order S NS"
    and af_redpair: "af_redpair S NS \<pi>"
    and orient: "P \<subseteq> S \<union> NS"
    and U_NS: "U \<subseteq> NS"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> (P - S) R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof -
  from closed have U_R: "U \<subseteq> R"
    and U_closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  show ?thesis
  proof (rule finite_innermost_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k,t k) \<in> P"
      and source: "\<And>k. innermost_pair_source Sharp \<mu> R
        (s k \<cdot> \<sigma> k)"
      and steps: "\<And>k. (t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
        \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
    proof (rule exI[where x=\<sigma>], intro allI)
      fix k
      from pair_shape pair[of k] obtain f ls g rs where
        lhs: "s k = Fun (Sharp f) ls" and rhs: "t k = Fun (Sharp g) rs"
        by auto
      have marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
        using marked pair[of k] lhs by blast
      have marked_r: "\<mu> (Sharp g,length rs) = \<mu> (g,length rs)"
        using marked pair[of k] rhs by blast
      have safe: "muterm_innermost_af_ur_safe R U \<mu> \<pi> (t k \<cdot> \<sigma> k)"
        by (rule muterm_innermost_af_pair_target_safe[
          OF closed conservative_pairs pair[of k] lhs rhs marked_l source[of k]])
      have full_steps: "(t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k))
          \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps[of k]
          rtrancl_mono[OF innermost_csdp_step_subset_csdp_step] by blast
      let ?args = "map (\<lambda>x. x \<cdot> \<sigma> k) rs"
      have marked_args: "\<mu> (Sharp g,length ?args) = \<mu> (g,length ?args)"
        using marked_r by simp
      have safe_args: "muterm_innermost_af_ur_safe R U \<mu> \<pi>
          (Fun (Sharp g) ?args)"
        using safe unfolding rhs by simp
      have full_args: "(Fun (Sharp g) ?args,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
        using full_steps unfolding rhs by simp
      from muterm_innermost_af_ur_safe_sharp_csdp_steps[
        OF wf fresh U_R U_closed conservative_rules af_redpair redpair U_NS
          marked_args safe_args full_args]
      show "(t k \<cdot> \<sigma> k,s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> NS"
        unfolding rhs by simp
    qed
  qed
qed

lemma finite_innermost_csr_dpp_mono_pairs:
  assumes sub: "P \<subseteq> Q"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> Q R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof -
  have root_sub: "innermost_rrstep Sharp \<mu> R P \<subseteq>
      innermost_rrstep Sharp \<mu> R Q"
    unfolding innermost_rrstep_def
    using rrstep_mono[OF sub] by blast
  from fin have fin': "SN_rel (innermost_rrstep Sharp \<mu> R Q)
      (innermost_csdp_step Sharp \<mu> R)"
    unfolding finite_mode_csr_dpp_def by simp
  show ?thesis
    unfolding finite_mode_csr_dpp_def csr_mode_rrstep.simps
      csr_mode_csdp_step.simps
    by (rule SN_rel_mono[OF root_sub subset_refl fin'])
qed

fun af_mu_vars_term_list ::
  "'f muL \<Rightarrow> 'f af \<Rightarrow> ('f,'v) term \<Rightarrow> 'v list" where
  "af_mu_vars_term_list \<mu> \<pi> (Var x) = [x]"
| "af_mu_vars_term_list \<mu> \<pi> (Fun f ts) =
    concat (map (\<lambda>i. af_mu_vars_term_list \<mu> \<pi> (ts ! i))
      [i <- [0..<length ts].
        i \<in> mu_of \<mu> (f,length ts) \<and> i \<in> \<pi> (f,length ts)])"

lemma set_af_mu_vars_term_list [simp]:
  "set (af_mu_vars_term_list \<mu> \<pi> t) =
    mu_vars_term (af_inter \<pi> (mu_of \<mu>)) t"
proof (induct t)
  case (Var x)
  then show ?case unfolding mu_vars_term_def by auto
next
  case (Fun f ts)
  show ?case
  proof
    show "set (af_mu_vars_term_list \<mu> \<pi> (Fun f ts)) \<subseteq>
        mu_vars_term (af_inter \<pi> (mu_of \<mu>)) (Fun f ts)"
    proof
      fix x
      assume x: "x \<in> set (af_mu_vars_term_list \<mu> \<pi> (Fun f ts))"
      then obtain i where i: "i < length ts"
        "i \<in> mu_of \<mu> (f,length ts)" "i \<in> \<pi> (f,length ts)"
        and xi: "x \<in> set (af_mu_vars_term_list \<mu> \<pi> (ts ! i))"
        by auto
      from Fun.hyps[OF nth_mem[OF i(1)], unfolded mu_vars_term_def] xi
      obtain p where p: "p \<in> mu_poss (af_inter \<pi> (mu_of \<mu>)) (ts ! i)"
        and sub: "ts ! i |_ p = Var x" by auto
      have "i # p \<in> mu_poss (af_inter \<pi> (mu_of \<mu>)) (Fun f ts)"
        using i p by (auto simp: af_inter_def)
      moreover have "Fun f ts |_ (i # p) = Var x" using i sub by simp
      ultimately show "x \<in> mu_vars_term (af_inter \<pi> (mu_of \<mu>)) (Fun f ts)"
        unfolding mu_vars_term_def by blast
    qed
  next
    show "mu_vars_term (af_inter \<pi> (mu_of \<mu>)) (Fun f ts) \<subseteq>
        set (af_mu_vars_term_list \<mu> \<pi> (Fun f ts))"
    proof
      fix x
      assume "x \<in> mu_vars_term (af_inter \<pi> (mu_of \<mu>)) (Fun f ts)"
      then obtain p where p: "p \<in> mu_poss (af_inter \<pi> (mu_of \<mu>)) (Fun f ts)"
        and sub: "Fun f ts |_ p = Var x"
        unfolding mu_vars_term_def by auto
      show "x \<in> set (af_mu_vars_term_list \<mu> \<pi> (Fun f ts))"
      proof (cases p)
        case Nil
        with sub show ?thesis by simp
      next
        case (Cons i q)
        from p Cons have i: "i < length ts"
          "i \<in> mu_of \<mu> (f,length ts)" "i \<in> \<pi> (f,length ts)"
          and q: "q \<in> mu_poss (af_inter \<pi> (mu_of \<mu>)) (ts ! i)"
          by (auto simp: af_inter_def)
        from sub Cons i have sub_i: "ts ! i |_ q = Var x" by simp
        have "x \<in> set (af_mu_vars_term_list \<mu> \<pi> (ts ! i))"
          using Fun.hyps[OF nth_mem[OF i(1)]] q sub_i
          unfolding mu_vars_term_def by auto
        with i show ?thesis by auto
      qed
    qed
  qed
qed

definition rhs_af_mu_vars_condition_list where
  "rhs_af_mu_vars_condition_list \<mu> \<pi> R \<longleftrightarrow>
    list_all (\<lambda>(l,r). list_all
      (\<lambda>x. x \<in> set (af_mu_vars_term_list \<mu> \<pi> l))
      (af_mu_vars_term_list \<mu> \<pi> r)) R"

definition rhs_pair_af_mu_vars_condition_list where
  "rhs_pair_af_mu_vars_condition_list \<mu> \<pi> R \<longleftrightarrow>
    list_all (\<lambda>(l,r). list_all
      (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l))
      (af_mu_vars_term_list \<mu> \<pi> r)) R"

lemma rhs_af_mu_vars_condition_list_sound:
  assumes "rhs_af_mu_vars_condition_list \<mu> \<pi> R"
  shows "rhs_af_mu_vars_condition (mu_of \<mu>) \<pi> (set R)"
  using assms unfolding rhs_af_mu_vars_condition_list_def
    rhs_af_mu_vars_condition_def list_all_iff by auto

lemma rhs_pair_af_mu_vars_condition_list_sound:
  assumes "rhs_pair_af_mu_vars_condition_list \<mu> \<pi> R"
  shows "rhs_pair_af_mu_vars_condition (mu_of \<mu>) \<pi> (set R)"
  using assms unfolding rhs_pair_af_mu_vars_condition_list_def
    rhs_pair_af_mu_vars_condition_def list_all_iff by auto

definition muterm_innermost_ur_redpair_proc where
  "muterm_innermost_ur_redpair_proc J \<mu> rp Premove U dpp = check_return (do {
    rel_impl_redpair rp;
    let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
    check (csr_sharp_pairs_check (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''innermost MU-TERM usable-rule processor requires marked pairs''));
    check (muterm_marked_mu_pairs_check \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
    check (muterm_innermost_ur_closed_check
        (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''supplied rules are not the closed innermost MU-TERM usable set''));
    check (rhs_mu_vars_condition_list \<mu> (dpp_ops.pairs J dpp @ U))
      (showsl_lit (STR ''innermost MU-TERM conservativity condition failed''));
    rel_impl_ns rp (U @ pns);
    rel_impl_s rp ps
  }) (dpp_spec.delete_pairs J dpp Premove)"

definition muterm_innermost_af_ur_redpair_proc where
  "muterm_innermost_af_ur_redpair_proc J \<mu> rp Premove U dpp = check_return (do {
    rel_impl_redpair rp;
    let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
    check (csr_sharp_pairs_check (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''filtered innermost MU-TERM usable-rule processor requires marked pairs''));
    check (muterm_marked_mu_pairs_check \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
    check (muterm_innermost_ur_closed_check
        (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''supplied rules are not the closed innermost MU-TERM usable set''));
    check (rhs_pair_af_mu_vars_condition_list \<mu> (rel_impl.af rp)
        (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''filtered innermost MU-TERM pair-variable condition failed''));
    check (rhs_af_mu_vars_condition_list \<mu> (rel_impl.af rp) U)
      (showsl_lit (STR ''filtered innermost MU-TERM usable-rule variable condition failed''));
    rel_impl_ns rp (U @ pns);
    rel_impl_s rp ps
  }) (dpp_spec.delete_pairs J dpp Premove)"

lemma muterm_innermost_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_innermost_ur_redpair_proc J \<mu> rp Premove U dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_innermost_ur_redpair_proc_def Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and shape: "csr_sharp_pairs_check (pairs dpp)"
    and marked: "muterm_marked_mu_pairs_check \<mu> (pairs dpp)"
    and closed: "muterm_innermost_ur_closed_check (rules dpp) U \<mu> (pairs dpp)"
    and conservative: "rhs_mu_vars_condition_list \<mu> (pairs dpp @ U)"
    and weak: "isOK (rel_impl_ns rp (U @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have ex_rel: "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule all_rel[THEN spec])
  from ex_rel
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    by auto
  from rel_prop strict weak subst sn standard
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and pns_NS: "set pns \<subseteq> NS"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    and ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and subst_NS: "subst.closed NS"
    and trans_S: "trans S"
    and irrefl_S: "irrefl S"
    and subst_S: "subst.closed S"
    and SN_S: "SN S"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq> set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have fin_S: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (pairs dpp) - S) (set (rules dpp))"
    by (rule finite_innermost_csr_dpp_mono_pairs[
      OF sub fin[unfolded pairs' rules']])
  have shape_sem: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    by (rule csr_sharp_pairs_check_sound[OF shape])
  have marked_sem: "\<forall>(l,r)\<in>set (pairs dpp). \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
    by (rule muterm_marked_mu_pairs_check_sound[OF marked])
  have closed_sem: "muterm_innermost_ur_closed (set (rules dpp))
      (set U) (mu_of \<mu>) (set (pairs dpp))"
    by (rule muterm_innermost_ur_closed_check_sound[OF closed])
  have conservative_sem: "rhs_mu_vars_condition (mu_of \<mu>)
      (set (pairs dpp) \<union> set U)"
    using rhs_mu_vars_condition_list_sound[OF conservative] by simp
  show ?thesis
    by (rule finite_innermost_csr_dpp_muterm_ur_redpair[
      OF wf fresh closed_sem conservative_sem marked_sem shape_sem redpair
        orient U_NS fin_S])
qed

lemma muterm_innermost_af_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_innermost_af_ur_redpair_proc J \<mu> rp Premove U dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_innermost_af_ur_redpair_proc_def Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and shape: "csr_sharp_pairs_check (pairs dpp)"
    and marked: "muterm_marked_mu_pairs_check \<mu> (pairs dpp)"
    and closed: "muterm_innermost_ur_closed_check (rules dpp) U \<mu> (pairs dpp)"
    and conservative_pairs: "rhs_pair_af_mu_vars_condition_list \<mu>
      (rel_impl.af rp) (pairs dpp)"
    and conservative_rules: "rhs_af_mu_vars_condition_list \<mu>
      (rel_impl.af rp) U"
    and weak: "isOK (rel_impl_ns rp (U @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have ex_rel: "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule all_rel[THEN spec])
  from ex_rel obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    by auto
  from rel_prop strict weak subst sn standard
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and pns_NS: "set pns \<subseteq> NS"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    and ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and af_NS: "af_compatible (rel_impl.af rp) NS"
    and subst_NS: "subst.closed NS"
    and trans_S: "trans S"
    and irrefl_S: "irrefl S"
    and subst_S: "subst.closed S"
    and SN_S: "SN S"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have filtered_redpair: "af_redpair S NS (rel_impl.af rp)"
    by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq> set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have fin_S: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (pairs dpp) - S) (set (rules dpp))"
    by (rule finite_innermost_csr_dpp_mono_pairs[
      OF sub fin[unfolded pairs' rules']])
  have shape_sem: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    by (rule csr_sharp_pairs_check_sound[OF shape])
  have marked_sem: "\<forall>(l,r)\<in>set (pairs dpp). \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
    by (rule muterm_marked_mu_pairs_check_sound[OF marked])
  have closed_sem: "muterm_innermost_ur_closed (set (rules dpp))
      (set U) (mu_of \<mu>) (set (pairs dpp))"
    by (rule muterm_innermost_ur_closed_check_sound[OF closed])
  have pair_sem: "rhs_pair_af_mu_vars_condition (mu_of \<mu>)
      (rel_impl.af rp) (set (pairs dpp))"
    by (rule rhs_pair_af_mu_vars_condition_list_sound[OF conservative_pairs])
  have rule_sem: "rhs_af_mu_vars_condition (mu_of \<mu>)
      (rel_impl.af rp) (set U)"
    by (rule rhs_af_mu_vars_condition_list_sound[OF conservative_rules])
  show ?thesis
    by (rule finite_innermost_csr_dpp_muterm_af_ur_redpair[
      OF wf fresh closed_sem pair_sem rule_sem marked_sem shape_sem redpair
        filtered_redpair orient U_NS fin_S])
qed

theorem finite_innermost_csr_dpp_csr_instantiation:
  fixes P R sts :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab),string) trs"
    and RL :: "((('f,'l) lab),string) rules"
  assumes wf: "wf_trs R"
    and rules: "set RL = R"
    and undef: "\<And>u v. (u,v) \<in> P \<Longrightarrow>
      (case root v of None \<Rightarrow> True | Some fn \<Rightarrow> \<not> defined R fn)"
    and instances: "\<And>st'. st' \<in> sts \<Longrightarrow> instance_rule st' (s,t)"
    and cover: "\<And>u v. (u,v) \<in> P \<Longrightarrow>
      ((\<forall>\<gamma>. gc_matcher (csr_instantiation_cap \<mu> RL v) s = Some \<gamma> \<longrightarrow>
          (\<exists>st'\<in>sts. instance_rule (s \<cdot> \<gamma>,t \<cdot> \<gamma>) st')) \<or>
       (\<forall>\<gamma>. mgu_class (csr_shared_instantiation_cap \<mu> v) s = Some \<gamma> \<longrightarrow>
          (\<exists>st'\<in>sts. instance_rule
            (mv_yvar s \<cdot> \<gamma>,mv_yvar t \<cdot> \<gamma>) st')))"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu>
      (replace (s,t) sts P) R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof (rule ccontr)
  let ?RS = "innermost_csdp_step Sharp \<mu> R"
  let ?RP = "innermost_rrstep Sharp \<mu> R P"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  assume not_fin: "\<not> finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
  then obtain ch where chain: "\<And>k. (ch k,ch (Suc k)) \<in> ?rel"
    unfolding finite_mode_csr_dpp_def SN_rel_on_def SN_on_def by auto
  have witnesses: "\<forall>k. \<exists>l r \<sigma>.
      (l,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>) \<and>
      (ch k,l \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*"
  proof
    fix k
    from chain[of k] obtain a b where pre: "(ch k,a) \<in> ?RS\<^sup>*"
      and strict: "(a,b) \<in> ?RP"
      and post: "(b,ch (Suc k)) \<in> ?RS\<^sup>*" by auto
    from strict have rr: "(a,b) \<in> rrstep P"
      and source: "innermost_pair_source Sharp \<mu> R a"
      unfolding innermost_rrstep_def by auto
    from rrstepE[OF rr] obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>" .
    show "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>) \<and>
      (ch k,l \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*"
      using pair source pre post a b by blast
  qed
  from choice[OF witnesses] obtain si where choose_si: "\<forall>k. \<exists>r \<sigma>.
      (si k,r) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (si k \<cdot> \<sigma>) \<and>
      (ch k,si k \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from choice[OF choose_si] obtain ti where choose_ti: "\<forall>k. \<exists>\<sigma>.
      (si k,ti k) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (si k \<cdot> \<sigma>) \<and>
      (ch k,si k \<cdot> \<sigma>) \<in> ?RS\<^sup>* \<and>
      (ti k \<cdot> \<sigma>,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from choice[OF choose_ti] obtain \<sigma> where chosen: "\<forall>k.
      (si k,ti k) \<in> P \<and>
      innermost_pair_source Sharp \<mu> R (si k \<cdot> \<sigma> k) \<and>
      (ch k,si k \<cdot> \<sigma> k) \<in> ?RS\<^sup>* \<and>
      (ti k \<cdot> \<sigma> k,ch (Suc k)) \<in> ?RS\<^sup>*" by blast
  from chosen have pair: "\<And>k. (si k,ti k) \<in> P"
    and source: "\<And>k. innermost_pair_source Sharp \<mu> R
      (si k \<cdot> \<sigma> k)"
    and pre: "\<And>k. (ch k,si k \<cdot> \<sigma> k) \<in> ?RS\<^sup>*"
    and post: "\<And>k. (ti k \<cdot> \<sigma> k,ch (Suc k)) \<in> ?RS\<^sup>*"
    by blast+
  have steps: "\<And>k. (ti k \<cdot> \<sigma> k,
      si (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?RS\<^sup>*"
    using post pre by (meson rtrancl_trans)
  let ?RL = RL
  have replacement: "\<forall>k. \<exists>s' t' \<tau>.
      (s',t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = s' \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>"
  proof
    fix k
    show "\<exists>s' t' \<tau>. (s',t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = s' \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>"
    proof (cases "(si (Suc k),ti (Suc k)) = (s,t)")
      case False
      have not_singleton: "(si (Suc k),ti (Suc k)) \<notin> {(s,t)}"
        using False by simp
      show ?thesis
      proof (intro exI conjI)
        show "(si (Suc k),ti (Suc k)) \<in> replace (s,t) sts P"
        proof (cases "(s,t) \<in> P")
          case True
          have in_diff: "(si (Suc k),ti (Suc k)) \<in> P - {(s,t)}"
            using pair[of "Suc k"] not_singleton by blast
          have rep: "replace (s,t) sts P = P - {(s,t)} \<union> sts"
            unfolding Util.replace_def by (rule if_P[OF True])
          show ?thesis unfolding rep by (rule UnI1[OF in_diff])
        next
          case False
          with pair[of "Suc k"] show ?thesis
            unfolding Util.replace_def by simp
        qed
      qed simp_all
    next
      case True
      then have si: "si (Suc k) = s" and ti: "ti (Suc k) = t" by auto
      have undef_k: "case root (ti k) of None \<Rightarrow> True
          | Some fn \<Rightarrow> fn \<notin> set (defined_list ?RL)"
      proof (cases "root (ti k)")
        case None
        then show ?thesis by simp
      next
        case (Some fn)
        from undef[OF pair[of k]] Some have "\<not> defined R fn" by simp
        with Some rules show ?thesis by simp
      qed
      have inner_steps: "(ti k \<cdot> \<sigma> k,s \<cdot> \<sigma> (Suc k))
          \<in> (innermost_csdp_step Sharp \<mu> (set ?RL))\<^sup>*"
        using steps[of k] unfolding si rules .
      have steps_k: "(ti k \<cdot> \<sigma> k,s \<cdot> \<sigma> (Suc k))
          \<in> (csdp_step Sharp \<mu> (set ?RL))\<^sup>*"
        by (rule rtrancl_mono[OF innermost_csdp_step_subset_csdp_step,
              THEN subsetD, OF inner_steps])
      have wf_RL: "wf_trs (set ?RL)" using wf rules by simp
      from csr_instantiation_cap_steps[
        where R = ?RL and v = "ti k" and \<sigma> = "\<sigma> k"
          and s = s and \<tau> = "\<sigma> (Suc k)" and \<mu> = \<mu>,
        OF wf_RL undef_k steps_k]
      have old_cap_mem: "s \<cdot> \<sigma> (Suc k) \<in>
          Ground_Context.equiv_class (csr_instantiation_cap \<mu> ?RL (ti k))" .
      from gc_matcher_complete[OF old_cap_mem]
      obtain \<gamma>old \<delta>old where old_matcher:
          "gc_matcher (csr_instantiation_cap \<mu> ?RL (ti k)) s = Some \<gamma>old"
        and old_sigma: "\<sigma> (Suc k) = \<gamma>old \<circ>\<^sub>s \<delta>old" by blast
      from csr_shared_instantiation_cap_steps[
        where R = ?RL and v = "ti k" and \<sigma> = "\<sigma> k"
          and s = s and \<tau> = "\<sigma> (Suc k)" and \<mu> = \<mu>,
        OF wf_RL undef_k steps_k]
      have cap_mem: "s \<cdot> \<sigma> (Suc k) \<in>
          \<lbrace>csr_shared_instantiation_cap \<mu> (ti k)\<rbrace>_(mv_subst (\<sigma> k))" .
      have range: "\<And>x. Inr x \<in> vars_term
          (csr_shared_instantiation_cap \<mu> (ti k)) \<Longrightarrow> x \<in> range x_var"
        by (rule vars_csr_shared_instantiation_cap)
      from mgu_class_complete[OF cap_mem range]
      obtain \<gamma>shared \<delta>shared where shared_matcher:
          "mgu_class (csr_shared_instantiation_cap \<mu> (ti k)) s = Some \<gamma>shared"
        and shared_sigma: "\<And>q. q \<cdot> \<sigma> (Suc k) =
          mv_yvar q \<cdot> \<gamma>shared \<cdot> \<delta>shared" by blast
      have covered_instance: "\<exists>s' t' \<delta>. (s',t') \<in> sts \<and>
          s \<cdot> \<sigma> (Suc k) = s' \<cdot> \<delta> \<and>
          t \<cdot> \<sigma> (Suc k) = t' \<cdot> \<delta>"
      proof -
        from cover[OF pair[of k]] show ?thesis
        proof
          assume old: "\<forall>\<gamma>. gc_matcher
              (csr_instantiation_cap \<mu> ?RL (ti k)) s = Some \<gamma> \<longrightarrow>
              (\<exists>st'\<in>sts. instance_rule (s \<cdot> \<gamma>,t \<cdot> \<gamma>) st')"
          from old old_matcher obtain s' t' where st': "(s',t') \<in> sts"
            and inst: "instance_rule
              (s \<cdot> \<gamma>old,t \<cdot> \<gamma>old) (s',t')" by auto
          from inst[unfolded instance_rule_def] obtain \<rho> where
            rho: "s \<cdot> \<gamma>old = s' \<cdot> \<rho>"
              "t \<cdot> \<gamma>old = t' \<cdot> \<rho>" by auto
          have es: "s \<cdot> \<sigma> (Suc k) = s' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>old)"
            using rho(1) unfolding old_sigma by (simp add: subst_compose)
          have et: "t \<cdot> \<sigma> (Suc k) = t' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>old)"
            using rho(2) unfolding old_sigma by (simp add: subst_compose)
          show ?thesis using st' es et by blast
        next
          assume shared: "\<forall>\<gamma>. mgu_class
              (csr_shared_instantiation_cap \<mu> (ti k)) s = Some \<gamma> \<longrightarrow>
              (\<exists>st'\<in>sts. instance_rule
                (mv_yvar s \<cdot> \<gamma>,mv_yvar t \<cdot> \<gamma>) st')"
          from shared shared_matcher obtain s' t' where st': "(s',t') \<in> sts"
            and inst: "instance_rule
              (mv_yvar s \<cdot> \<gamma>shared,mv_yvar t \<cdot> \<gamma>shared) (s',t')"
            by auto
          from inst[unfolded instance_rule_def] obtain \<rho> where
            rho: "mv_yvar s \<cdot> \<gamma>shared = s' \<cdot> \<rho>"
              "mv_yvar t \<cdot> \<gamma>shared = t' \<cdot> \<rho>" by auto
          have es: "s \<cdot> \<sigma> (Suc k) = s' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>shared)"
            using rho(1) shared_sigma[of s] by (simp add: subst_compose)
          have et: "t \<cdot> \<sigma> (Suc k) = t' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>shared)"
            using rho(2) shared_sigma[of t] by (simp add: subst_compose)
          show ?thesis using st' es et by blast
        qed
      qed
      then obtain s' t' \<delta> where st': "(s',t') \<in> sts"
        and es: "s \<cdot> \<sigma> (Suc k) = s' \<cdot> \<delta>"
        and et: "t \<cdot> \<sigma> (Suc k) = t' \<cdot> \<delta>" by blast
      have selected: "(s,t) \<in> P" using pair[of "Suc k"] True by simp
      have member: "(s',t') \<in> replace (s,t) sts P"
        using st' selected unfolding Util.replace_def by simp
      show ?thesis using member es et unfolding si ti by blast
    qed
  qed
  from choice[OF replacement] obtain si' where one: "\<forall>k. \<exists>t' \<tau>.
      (si' k,t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>" by auto
  from choice[OF one] obtain ti' where two: "\<forall>k. \<exists>\<tau>.
      (si' k,ti' k) \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = ti' k \<cdot> \<tau>" by auto
  from choice[OF two] obtain \<tau> where transformed:
      "\<And>k. (si' k,ti' k) \<in> replace (s,t) sts P"
      "\<And>k. si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> k"
      "\<And>k. ti (Suc k) \<cdot> \<sigma> (Suc k) = ti' k \<cdot> \<tau> k"
    by auto
  let ?P' = "replace (s,t) sts P"
  let ?RP' = "innermost_rrstep Sharp \<mu> R ?P'"
  let ?g = "\<lambda>k. si' k \<cdot> \<tau> k"
  have strict: "(si' k \<cdot> \<tau> k,ti' k \<cdot> \<tau> k) \<in> ?RP'" for k
  proof -
    have rr: "(si' k \<cdot> \<tau> k,ti' k \<cdot> \<tau> k) \<in> rrstep ?P'"
      unfolding rrstep_def' using transformed(1)[of k] by auto
    have src: "innermost_pair_source Sharp \<mu> R (si' k \<cdot> \<tau> k)"
      using source[of "Suc k"] transformed(2)[of k] by simp
    show ?thesis unfolding innermost_rrstep_def using rr src by blast
  qed
  have bridge: "(ti' k \<cdot> \<tau> k,si' (Suc k) \<cdot> \<tau> (Suc k))
      \<in> ?RS\<^sup>*" for k
    using steps[of "Suc k"] transformed(3)[of k]
      transformed(2)[of "Suc k"] by auto
  have g_step: "(?g k,?g (Suc k)) \<in> ?RS\<^sup>* O ?RP' O ?RS\<^sup>*" for k
    using strict[of k] bridge[of k] by auto
  have g_chain: "chain (?RS\<^sup>* O ?RP' O ?RS\<^sup>*) ?g" using g_step by simp
  have not_sn: "\<not> SN_on (?RS\<^sup>* O ?RP' O ?RS\<^sup>*) UNIV"
    by (rule not_SN_onI[OF _ g_chain], simp)
  from fin have fin_rel: "SN_rel ?RP' ?RS"
    unfolding finite_mode_csr_dpp_def by simp
  from fin_rel have "SN_on (?RS\<^sup>* O ?RP' O ?RS\<^sup>*) UNIV"
    unfolding SN_rel_on_def .
  with not_sn show False by contradiction
qed

lemma csr_instantiation_proc_innermost_finite_sound:
  assumes J: "dpp_spec J"
    and proc: "csr_instantiation_proc J \<mu> st sts dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  note sound = csr_instantiation_proc_sound[OF proc]
  obtain s t where st: "st = (s,t)" by (cases st)
  interpret dpp_spec J by fact
  have selected: "(s,t) \<in> set (pairs dpp)" using sound(2) st by simp
  have dpp': "dpp' = replace_pair dpp (s,t) sts" using sound(1) st by simp
  have sem: "dpp_ops.dpp J dpp' =
    (NFS dpp,M dpp,replace (s,t) (set sts) (set (P dpp)),
      replace (s,t) (set sts) (set (Pw dpp)),set (Q dpp),
      set (R dpp),set (Rw dpp))"
    unfolding dpp' by (rule replace_pair_sound)
  have sem': "dpp_ops.dpp J dpp' =
    (NFS dpp',M dpp',set (P dpp'),set (Pw dpp'),set (Q dpp'),
      set (R dpp'),set (Rw dpp'))" by (rule dpp_sound)
  have pairs': "set (pairs dpp') =
      replace (s,t) (set sts) (set (pairs dpp))"
    using sem sem' pairs_sound[of dpp] pairs_sound[of dpp'] selected
    unfolding Util.replace_def by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' rules_sound[of dpp] rules_sound[of dpp'] by auto
  show ?thesis
  proof (rule finite_innermost_csr_dpp_csr_instantiation[
      where RL = "rules dpp" and s = s and t = t and sts = "set sts"])
    show "wf_trs (set (rules dpp))" by (rule wf)
    show "set (rules dpp) = set (rules dpp)" by simp
  next
    fix u v
    assume uv: "(u,v) \<in> set (pairs dpp)"
    from sound(4)[OF uv] show "case root v of None \<Rightarrow> True
      | Some fn \<Rightarrow> \<not> defined (set (rules dpp)) fn"
      by (cases "root v"; simp add: set_defined_list)
  next
    fix st'
    assume "st' \<in> set sts"
    from sound(3)[OF this] show "instance_rule st' (s,t)" unfolding st .
  next
    fix u v
    assume uv: "(u,v) \<in> set (pairs dpp)"
    from sound(5)[OF st uv]
    show "((\<forall>\<gamma>. gc_matcher
          (csr_instantiation_cap (mu_of \<mu>) (rules dpp) v) s = Some \<gamma> \<longrightarrow>
          (\<exists>st'\<in>set sts. instance_rule (s \<cdot> \<gamma>,t \<cdot> \<gamma>) st')) \<or>
       (\<forall>\<gamma>. mgu_class
          (csr_shared_instantiation_cap (mu_of \<mu>) v) s = Some \<gamma> \<longrightarrow>
          (\<exists>st'\<in>set sts. instance_rule
            (mv_yvar s \<cdot> \<gamma>,mv_yvar t \<cdot> \<gamma>) st')))" .
  next
    show "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (replace (s,t) (set sts) (set (pairs dpp))) (set (rules dpp))"
      using fin unfolding pairs' rules' .
  qed
qed

fun check_muterm_expanded_innermost_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_muterm_expanded_innermost_components ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f,label_type,string) csr_dp_termination_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_muterm_expanded_innermost_proof I J \<mu> i dpp
      (CSR_DP_Dep_Graph_Proc edps) =
    debug i (STR ''expanded innermost MU-TERM dependency graph'') (do {
      _ \<leftarrow> check_innermost_csr_dep_graph_proc J \<mu> dpp edps;
      check_muterm_expanded_innermost_components I J \<mu> i dpp edps
    })"
| "check_muterm_expanded_innermost_proof I J \<mu> i dpp
      (CSR_DP_Instantiation_Proc st sts prf) =
    debug i (STR ''expanded innermost MU-TERM instantiation'') (do {
      dpp' \<leftarrow> csr_instantiation_proc J \<mu> st sts dpp;
      check_muterm_expanded_innermost_proof I J \<mu>
        (add_index i 1) dpp' prf
    })"
| "check_muterm_expanded_innermost_proof I J \<mu> i dpp
      (CSR_DP_Ordinary_Proof (Redpair_UR_Proc redp Pr U subprf)) =
    debug i (STR ''expanded innermost MU-TERM QCS usable-rule reduction pair'') (do {
      check (list_all (\<lambda>lr. lr \<in> set (dpp_ops.rules J dpp)) U)
        (showsl_lit (STR ''expanded MU-TERM usable rules are not a subset of the active rules''));
      check (list_all (\<lambda>lr. qcs_ur_closed_term_check
          (dpp_ops.rules J dpp) U \<mu> (snd lr)) U)
        (showsl_lit (STR ''expanded MU-TERM usable-rule RHS closure failed''));
      check (list_all (\<lambda>dp. qcs_ur_closed_dp_rhs_check
          (dpp_ops.rules J dpp) U \<mu> (snd dp))
          (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''expanded MU-TERM dependency-pair RHS closure failed''));
      check (qcs_csr_ur_closed_check (dpp_ops.rules J dpp) U \<mu>
          (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''expanded MU-TERM QCS usable-rule closure failed''));
      let dppU = dpp_ops.mk J False False (dpp_ops.pairs J dpp) [] [] [] U;
      check_dp_termination_proof I J False (add_index i 1) dppU
        (Redpair_Proc redp Pr subprf)
    })"
| "check_muterm_expanded_innermost_proof I J \<mu> i dpp
      (CSR_DP_Ordinary_Proof dpprf) =
    debug i (STR ''expanded innermost ordinary DP proof'')
      (check_csr_dp_termination_proof I J False i dpp
        (CSR_DP_Ordinary_Proof dpprf))"
| "check_muterm_expanded_innermost_proof I J \<mu> i dpp prf =
    check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp prf"
| "check_muterm_expanded_innermost_components I J \<mu> i dpp [] = succeed"
| "check_muterm_expanded_innermost_components I J \<mu> i dpp
      ((None,C)#rest) =
    check_muterm_expanded_innermost_components I J \<mu> (add_index i 1) dpp rest"
| "check_muterm_expanded_innermost_components I J \<mu> i dpp
      ((Some prf,C)#rest) = do {
    check_muterm_expanded_innermost_proof I J \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp C) prf;
    check_muterm_expanded_innermost_components I J \<mu> (add_index i 1) dpp rest
  }"

lemma check_muterm_expanded_innermost_components_member:
  assumes ok: "isOK (check_muterm_expanded_innermost_components
      I J \<mu> i dpp edps)"
    and mem: "(Some prf,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_expanded_innermost_proof I J \<mu> j
    (dpp_ops.intersect_pairs J dpp C) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems head None show ?thesis by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = head")
      case True
      with Cons.prems head Some show ?thesis by auto
    next
      case False
      from Cons.prems head Some False show ?thesis by (auto intro: Cons.hyps)
    qed
  qed
qed

lemma check_muterm_expanded_innermost_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_muterm_expanded_innermost_proof I J \<mu> i dpp prf)"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain wf fresh
proof (induct "prf" arbitrary: dpp i)
  case (CSR_DP_Ordinary_Proof dpprf)
  show ?case
  proof (cases "\<exists>redp Pr U subprf.
      dpprf = Redpair_UR_Proc redp Pr U subprf")
    case True
    then obtain redp Pr U subprf where shape:
      "dpprf = Redpair_UR_Proc redp Pr U subprf" by blast
    let ?dU = "dpp_ops.mk J False False (dpp_ops.pairs J dpp) [] [] [] U"
    from CSR_DP_Ordinary_Proof.prems(1) shape have
      closed_check: "qcs_csr_ur_closed_check (dpp_ops.rules J dpp) U \<mu>
        (dpp_ops.pairs J dpp)"
      and rec: "isOK (check_dp_termination_proof I J False
        (add_index i 1) ?dU (Redpair_Proc redp Pr subprf))"
      by auto
    interpret dpp_spec J by fact
    have semU: "dpp_ops.dpp J ?dU =
        (False,False,set (pairs dpp),{},{},{},set U)"
      using dpp_spec.mk_sound[
        OF J, of False False "pairs dpp" "[]" "[]" "[]" U] by simp
    from check_dp_termination_proof[OF I J rec]
    have ordinary: "finite_dpp (dpp_ops.dpp J ?dU)" .
    have ordinary': "finite_dpp
        (False,False,set (pairs dpp),{},{},{},set U)"
      using ordinary unfolding semU .
    have sn: "SN_rel (rrstep (set (pairs dpp))) (rstep (set U))"
      using ordinary' unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
    have finU: "finite_csr_dpp Sharp (mu_of \<mu>)
        (set (pairs dpp)) (set U)"
      unfolding finite_csr_dpp_def
    proof (rule SN_rel_mono[OF subset_refl _ sn])
      show "csdp_step Sharp (mu_of \<mu>) (set U) \<subseteq> rstep (set U)"
        unfolding csdp_step_def csdp_step_p_def
        by (auto dest: rstep_r_p_s_imp_rstep)
    qed
    have closed: "qcs_csr_ur_closed (set (rules dpp)) (set U)
        (mu_of \<mu>) (set (pairs dpp))"
      by (rule qcs_csr_ur_closed_check_sound[OF closed_check])
    have full: "finite_csr_dpp Sharp (mu_of \<mu>)
        (set (pairs dpp)) (set (rules dpp))"
      by (rule finite_csr_dpp_qcs_usable_rules[
        OF CSR_DP_Ordinary_Proof.prems(3-4) closed finU])
    have full_mode: "finite_mode_csr_dpp Sharp CSR_Full (mu_of \<mu>)
        (set (pairs dpp)) (set (rules dpp))"
      using full by simp
    show ?thesis
      by (rule finite_full_imp_finite_innermost_csr_dpp[OF full_mode])
  next
    case False
    from CSR_DP_Ordinary_Proof.prems(1) False have standard:
      "isOK (check_csr_dp_termination_proof I J False i dpp
        (CSR_DP_Ordinary_Proof dpprf))"
      by (cases dpprf, auto)
    have full: "finite_mode_csr_dpp Sharp CSR_Full (mu_of \<mu>)
        (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
      using check_csr_dp_termination_proof_sound_csr[
        OF I J CSR_DP_Ordinary_Proof.prems(2) standard] by simp
    show ?thesis
      by (rule finite_full_imp_finite_innermost_csr_dpp[OF full])
  qed
next
  case (CSR_DP_Dep_Graph_Proc edps)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph:
      "isOK (check_innermost_csr_dep_graph_proc J \<mu> dpp edps)"
    and components: "isOK (check_muterm_expanded_innermost_components
      I J \<mu> i dpp edps)" by auto
  show ?case
  proof (rule check_innermost_csr_dep_graph_proc_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_muterm_expanded_innermost_components_member[OF components mem]
    obtain j where rec: "isOK (check_muterm_expanded_innermost_proof
      I J \<mu> j ?d p)" by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d = (NFS dpp,M dpp,set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C,set (Q dpp),set (R dpp),set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem dpp_sound[of ?d] pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem dpp_sound[of ?d] rules_sound[of dpp] rules_sound[of ?d] by auto
    have ih: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
        (set (pairs ?d)) (set (rules ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps)
          apply (rule mem)
         apply simp
        apply simp
       apply (rule rec)
      apply (rule plain')
      using CSR_DP_Dep_Graph_Proc.prems(3-4) unfolding rules' by auto
    show "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (pairs dpp) \<inter> set C) (set (rules dpp))"
      using ih unfolding pairs' rules' .
  qed
next
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct
        I J \<mu> i dpp CSR_DP_P_is_Empty)"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_P_is_Empty.prems(2) standard])
next
  case (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2) standard])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2) standard])
next
  case (CSR_DP_Usable_Rules_Proc x child)
  from CSR_DP_Usable_Rules_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Usable_Rules_Proc x child))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Usable_Rules_Proc.prems(2) standard])
next
  case (CSR_DP_Instantiation_Proc st sts child)
  from CSR_DP_Instantiation_Proc.prems(1) obtain dpp' where
    proc: "csr_instantiation_proc J \<mu> st sts dpp = return dpp'"
    and rec: "isOK (check_muterm_expanded_innermost_proof I J \<mu>
      (add_index i 1) dpp' child)" by auto
  have dpp': "dpp' = dpp_ops.replace_pair J dpp st sts"
    using csr_instantiation_proc_sound(1)[OF proc] by simp
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp' by (rule plain_csr_dpp_replace_pair[
      OF J CSR_DP_Instantiation_Proc.prems(2)])
  have rules': "set (dpp_ops.rules J dpp') = set (dpp_ops.rules J dpp)"
    unfolding dpp' by (rule rules_csr_dpp_replace_pair[OF J])
  have wf': "wf_trs (set (dpp_ops.rules J dpp'))"
    using CSR_DP_Instantiation_Proc.prems(3) unfolding rules' .
  have fresh': "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp')) (Sharp f,n)"
    using CSR_DP_Instantiation_Proc.prems(4) unfolding rules' .
  have fin': "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
    by (rule CSR_DP_Instantiation_Proc.hyps[OF rec plain' wf' fresh'])
  show ?case by (rule csr_instantiation_proc_innermost_finite_sound[
    OF J proc CSR_DP_Instantiation_Proc.prems(3) fin'])
next
  case (CSR_DP_Forward_Instantiation_Proc x1 x2 child)
  from CSR_DP_Forward_Instantiation_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Forward_Instantiation_Proc x1 x2 child))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Forward_Instantiation_Proc.prems(2) standard])
next
  case (CSR_DP_Redpair_UR_Proc x1 x2 x3 child)
  from CSR_DP_Redpair_UR_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Redpair_UR_Proc x1 x2 x3 child))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Redpair_UR_Proc.prems(2) standard])
next
  case (CSR_DP_Size_Change_Subterm_Proc x)
  from CSR_DP_Size_Change_Subterm_Proc.prems(1) have standard:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
        (CSR_DP_Size_Change_Subterm_Proc x))"
    by (simp only: check_muterm_expanded_innermost_proof.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
    OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2) standard])
qed

end
