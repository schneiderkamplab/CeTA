(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_CSDP_Proofs
  imports
    Proof_Checker.CSR_Checker
begin

lemma csnrstep_Var_empty:
  "(Var x, t) \<notin> csnrstep \<mu> R"
  unfolding csnrstep_def csstep_p_def rstep_r_p_s_def' by auto

lemma csnrstep_preserves_root:
  assumes "(s, t) \<in> csnrstep \<mu> R"
  shows "root t = root s"
  using assms
proof (cases s)
  case (Var x)
  with assms have False
    using csnrstep_Var_empty[of x t \<mu> R] by simp
  then show ?thesis by blast
next
  case (Fun f ss)
  have step: "(Fun f ss, t) \<in> csnrstep \<mu> R"
    using assms Fun by simp
  from step show ?thesis
  proof (elim csnrstep_FunE)
    fix i ts
    assume "t = Fun f ts" and "length ts = length ss"
    with Fun show ?thesis by simp
  qed
qed

lemma csnrsteps_preserve_root:
  assumes "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
  shows "root t = root s"
  using assms by (induct rule: rtrancl.induct, auto dest: csnrstep_preserves_root)

lemma csnrstep_imp_nrrstep:
  assumes "(s, t) \<in> csnrstep \<mu> R"
  shows "(s, t) \<in> nrrstep R"
proof -
  from assms obtain p lr \<sigma> where p: "p \<noteq> []"
    and step: "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csnrstep_def csstep_p_def by auto
  have step': "(s, t) \<in> qrstep_r_p_s False {} R lr p \<sigma>"
    using step unfolding rstep_r_p_s_def' qrstep_r_p_s_def by auto
  have "(s, t) \<in> nrqrstep False {} R"
    by (rule qrstep_r_p_s_imp_nrqrstep[OF step' p])
  then show ?thesis by simp
qed

lemma csstep_Var_empty_wf:
  assumes wf: "wf_trs R"
  shows "(Var x, t) \<notin> csstep \<mu> R"
proof
  assume "(Var x, t) \<in> csstep \<mu> R"
  then obtain p lr \<sigma> where step: "(Var x, t) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csstep_def csstep_p_def by auto
  from step have "p = []"
    unfolding rstep_r_p_s_def' by (cases p, auto)
  with step have "fst lr \<cdot> \<sigma> = Var x" and "lr \<in> R"
    unfolding rstep_r_p_s_def' by auto
  then have "is_Var (fst lr)"
    by (cases "fst lr", auto)
  moreover from wf \<open>lr \<in> R\<close> have "\<exists>f ts. fst lr = Fun f ts"
    unfolding wf_trs_def by (cases lr, auto)
  ultimately show False
    by auto
qed

lemma SN_on_csstep_Var:
  assumes wf: "wf_trs R"
  shows "SN_on (csstep \<mu> R) {Var x}"
  unfolding SN_on_def
proof clarify
  fix f
  assume f0_mem: "f 0 = Var x"
    and chain: "\<forall>i. (f i, f (Suc i)) \<in> csstep \<mu> R"
  then have f0: "f 0 = Var x"
    by simp
  from chain have "(f 0, f (Suc 0)) \<in> csstep \<mu> R"
    by blast
  with f0 have step0: "(Var x, f (Suc 0)) \<in> csstep \<mu> R"
    by simp
  have no_step0: "(Var x, f (Suc 0)) \<notin> csstep \<mu> R"
    by (rule csstep_Var_empty_wf[OF wf])
  from step0 no_step0 show False
    by blast
qed

lemma csrstepE:
  assumes "(s, t) \<in> csrstep \<mu> R"
  obtains l r \<sigma> where "(l, r) \<in> R" "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
proof -
  from assms obtain lr \<sigma> where step: "(s, t) \<in> rstep_r_p_s R lr [] \<sigma>"
    unfolding csrstep_iff_rstep_root by auto
  then have "lr \<in> R" "s = fst lr \<cdot> \<sigma>" "t = snd lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  then show ?thesis
    by (cases lr, intro that, auto)
qed

lemma csrstep_defined_root:
  assumes wf: "wf_trs R"
    and step: "(Fun f ss, t) \<in> csrstep \<mu> R"
  shows "defined R (f, length ss)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and lhs: "Fun f ss = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain g ts where l: "l = Fun g ts"
    unfolding wf_trs_def by (cases l, auto)
  from lhs l have "g = f" "length ts = length ss"
    by auto
  with lr l show ?thesis
    unfolding defined_def by auto
qed

lemma csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN:
  assumes wf: "wf_trs R"
    and undef: "\<not> defined R (f, length ss)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {Fun f ss}"
  shows "\<exists>i<length ss. i \<in> \<mu> (f, length ss) \<and> \<not> SN_on (csstep \<mu> R) {ss ! i}"
proof (rule ccontr)
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  assume no_arg: "\<not> ?thesis"
  then have arg_SN: "\<And>i. i < length ss \<Longrightarrow> i \<in> \<mu> (f, length ss) \<Longrightarrow> SN_on ?R {ss ! i}"
    by auto
  from notSN obtain ts where start: "ts 0 = Fun f ss" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  have shape_nsteps:
    "\<And>i. (\<exists>as. ts i = Fun f as \<and> length as = length ss) \<and>
      (ts i, ts (Suc i)) \<in> ?nR"
  proof -
    fix i
    show "(\<exists>as. ts i = Fun f as \<and> length as = length ss) \<and>
      (ts i, ts (Suc i)) \<in> ?nR"
    proof (induct i)
      case 0
      have shape: "\<exists>as. ts 0 = Fun f as \<and> length as = length ss"
        using start by auto
      from steps[of 0] have step0: "(ts 0, ts (Suc 0)) \<in> csrstep \<mu> R \<union> ?nR"
        unfolding csstep_root_nonroot by simp
      have nstep: "(ts 0, ts (Suc 0)) \<in> ?nR"
      proof (rule ccontr)
        assume "(ts 0, ts (Suc 0)) \<notin> ?nR"
        with step0 have "(ts 0, ts (Suc 0)) \<in> csrstep \<mu> R" by auto
        with start have "defined R (f, length ss)"
          using csrstep_defined_root[OF wf, of f ss "ts (Suc 0)" \<mu>] by simp
        with undef show False by simp
      qed
      from shape nstep show ?case by auto
    next
      case (Suc i)
      from Suc obtain as where tsi: "ts i = Fun f as" and len: "length as = length ss"
        and nstep_i: "(ts i, ts (Suc i)) \<in> ?nR" by auto
      from csnrstep_preserves_root[OF nstep_i] have root_eq:
        "root (ts (Suc i)) = Some (f, length as)"
        unfolding tsi by simp
      then obtain bs where tsSuc: "ts (Suc i) = Fun f bs"
        and len_bs_as: "length bs = length as"
        by (cases "ts (Suc i)", auto)
      from len_bs_as len have len_bs: "length bs = length ss"
        by simp
      from steps[of "Suc i"] have stepSuc: "(ts (Suc i), ts (Suc (Suc i))) \<in> csrstep \<mu> R \<union> ?nR"
        unfolding csstep_root_nonroot by simp
      have nstep: "(ts (Suc i), ts (Suc (Suc i))) \<in> ?nR"
      proof (rule ccontr)
        assume "(ts (Suc i), ts (Suc (Suc i))) \<notin> ?nR"
        with stepSuc have "(ts (Suc i), ts (Suc (Suc i))) \<in> csrstep \<mu> R" by auto
        with tsSuc len_bs have "defined R (f, length ss)"
          using csrstep_defined_root[OF wf, of f bs "ts (Suc (Suc i))" \<mu>] by simp
        with undef show False by simp
      qed
      from tsSuc len_bs nstep show ?case by auto
    qed
  qed
  have roots: "\<exists>as. ts i = Fun f as \<and> length as = length ss" for i
    using shape_nsteps[of i] by auto
  from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
    and len: "\<And>i. length (sss i) = length ss" by force
  have nsteps: "\<And>i. (Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
    using shape_nsteps[of i for i] by (simp add: ts)
  let ?strict = "\<lambda>i. \<exists>j<length ss. j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R"
  have strict_all: "\<And>i. ?strict i"
  proof -
    fix i
    from nsteps[of i] show "?strict i"
    proof (elim csnrstep_FunE)
      fix j us
      assume j: "j < length (sss i)" and jmu: "j \<in> \<mu> (f, length (sss i))"
        and sub: "(sss i ! j, us ! j) \<in> ?R"
        and tgt: "Fun f (sss (Suc i)) = Fun f us"
      from j len[of i] have jss: "j < length ss" by simp
      from jmu len[of i] have jmu': "j \<in> \<mu> (f, length ss)" by simp
      from tgt have us: "sss (Suc i) = us" by simp
      from jss jmu' sub us show ?thesis by auto
    qed
  qed
  let ?idx = "\<lambda>i. SOME j. j < length ss \<and> j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R"
  define idx where "idx = ?idx"
  have idx_strict: "idx i < length ss \<and> idx i \<in> \<mu> (f, length ss) \<and>
      (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
  proof -
    from strict_all[of i] have ex: "\<exists>j. j < length ss \<and> j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
    show ?thesis
      unfolding idx_def by (rule someI_ex[OF ex])
  qed
  have idx_bound: "idx i \<le> length ss" for i
    using idx_strict[of i] by auto
  have fin: "finite (idx ` X)" for X
  proof (rule finite_subset)
    show "idx ` X \<subseteq> {i. i \<le> length ss}" using idx_bound by auto
    have id: "{i. i \<le> length ss} = set [0 ..< Suc (length ss)]" by auto
    show "finite {i. i \<le> length ss}" unfolding id by (rule finite_set)
  qed
  have inf_strict: "infinite {i. ?strict i}"
    using strict_all by simp
  from pigeonhole_infinite[OF inf_strict fin]
  obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
  then have infj: "INFM i. idx i = j"
    unfolding INFM_iff_infinite
    using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
    by auto
  from infj[unfolded INFM_nat_le, rule_format, of 0]
  obtain k where kj: "idx k = j" by auto
  from idx_strict[of k] kj have jss: "j < length ss" and jmu: "j \<in> \<mu> (f, length ss)" by auto
  let ?ss = "\<lambda>i. sss i ! j"
  have SN: "SN_on ?R {?ss 0}"
    using arg_SN[OF jss jmu] start ts[of 0] by simp
  have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
  proof -
    from nsteps[of i] show ?thesis
    proof (elim csnrstep_FunE)
      fix k us
      assume k: "k < length (sss i)"
        and step: "(sss i ! k, us ! k) \<in> ?R"
        and tgt: "Fun f (sss (Suc i)) = Fun f us"
        and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
      from tgt have us_eq: "sss (Suc i) = us" by simp
      show ?thesis
      proof (cases "j = k")
        case True
        with step us_eq show ?thesis by auto
      next
        case False
        from jss len[of i] have "j < length (sss i)" by simp
        from same[OF this False] us_eq show ?thesis by simp
      qed
    qed
  qed
  have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
    using j_steps[of i] by auto
  have compat: "Id O ?R \<subseteq> ?R" by auto
  from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
  obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
  from infj[unfolded INFM_nat_le, rule_format, of k]
  obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
  from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
  with k[OF lk] show False by auto
qed

lemma csstep_notSN_imp_mu_defined_subterm:
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
    defined R (f, length ts) \<and> \<not> SN_on (csstep \<mu> R) {t |_ p}"
  using notSN
proof (induct t)
  case (Var x)
  from SN_on_csstep_Var[OF wf, of \<mu> x] Var.prems show ?case
    by simp
next
  case (Fun f ss)
  show ?case
  proof (cases "defined R (f, length ss)")
    case True
    show ?thesis
      by (intro exI[of _ "[]"] exI[of _ f] exI[of _ ss], insert True Fun.prems, auto)
  next
    case False
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf False Fun.prems]
    obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
      and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
      by auto
    from Fun.hyps[OF nth_mem[OF i] notSN_i]
    obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
      and sub: "ss ! i |_ p = Fun g ts"
      and def: "defined R (g, length ts)"
      and notSN_p: "\<not> SN_on (csstep \<mu> R) {ss ! i |_ p}"
      by auto
    let ?p = "i # p"
    have p_mu: "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
      using i imu p by auto
    have sub_p: "Fun f ss |_ ?p = Fun g ts"
      using i sub by simp
    have notSN_p': "\<not> SN_on (csstep \<mu> R) {Fun f ss |_ ?p}"
      using i notSN_p by simp
    show ?thesis
      by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts],
          insert p_mu sub_p def notSN_p', auto)
  qed
qed

fun mu_poss :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set"
where
  "mu_poss \<mu> (Var x) = {[]}"
| "mu_poss \<mu> (Fun f ts) =
    {[]} \<union> (\<Union>i\<in>\<mu> (f, length ts) \<inter> {0..<length ts}. {i # p |p. p \<in> mu_poss \<mu> (ts ! i)})"

definition mu_vars_term :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v set"
where
  "mu_vars_term \<mu> t = {x. \<exists>p. p \<in> mu_poss \<mu> t \<and> t |_ p = Var x}"

definition rhs_mu_vars_condition :: "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "rhs_mu_vars_condition \<mu> R \<longleftrightarrow>
    (\<forall>l r x. (l, r) \<in> R \<longrightarrow> x \<in> mu_vars_term \<mu> r \<longrightarrow> x \<in> mu_vars_term \<mu> l)"

lemma mu_fun_poss_imp_mu_poss:
  assumes "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> t"
  using assms by (induct t arbitrary: p) auto

lemma mu_poss_imp_poss:
  assumes "p \<in> mu_poss \<mu> t"
  shows "p \<in> poss t"
  using assms by (induct t arbitrary: p) auto

lemma mu_vars_term_imp_vars_term:
  assumes "x \<in> mu_vars_term \<mu> t"
  shows "x \<in> vars_term t"
proof -
  from assms obtain p where p: "p \<in> mu_poss \<mu> t" and sub: "t |_ p = Var x"
    unfolding mu_vars_term_def by auto
  from mu_poss_imp_poss[OF p] sub show ?thesis
    using vars_term_subt_at by force
qed

lemma mu_fun_poss_subst_cases_aux:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  shows "(p \<in> mu_fun_poss \<mu> t \<and> (t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>) \<or>
    (\<exists>x q1 q2. q1 \<in> poss t \<and> t |_ q1 = Var x \<and> x \<in> vars_term t \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case
    by auto
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons i q)
    from Fun.prems[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i \<cdot> \<sigma>)"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q]
    show ?thesis
    proof
      assume orig: "q \<in> mu_fun_poss \<mu> (ss ! i) \<and>
        (ss ! i \<cdot> \<sigma>) |_ q = (ss ! i |_ q) \<cdot> \<sigma>"
      then have "p \<in> mu_fun_poss \<mu> (Fun f ss) \<and>
        (Fun f ss \<cdot> \<sigma>) |_ p = (Fun f ss |_ p) \<cdot> \<sigma>"
        using i Cons by auto
      then show ?thesis by auto
    next
      assume subst: "\<exists>x q1 q2. q1 \<in> poss (ss ! i) \<and> ss ! i |_ q1 = Var x \<and>
        x \<in> vars_term (ss ! i) \<and> q = q1 @ q2 \<and>
        q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
      then obtain x q1 q2 where q1: "q1 \<in> poss (ss ! i)"
        and sub: "ss ! i |_ q1 = Var x"
        and vars: "x \<in> vars_term (ss ! i)"
        and q_eq: "q = q1 @ q2"
        and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and sub_at: "(ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
        by blast
      have "i # q1 \<in> poss (Fun f ss)"
        using i q1 by auto
      moreover have "Fun f ss |_ (i # q1) = Var x"
        using i sub by simp
      moreover have "x \<in> vars_term (Fun f ss)"
        using i vars by auto
      moreover have "p = (i # q1) @ q2"
        using Cons q_eq by simp
      moreover have "(Fun f ss \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
        using i Cons q_eq sub_at by simp
      ultimately show ?thesis
      using q2 by blast
    qed
  qed
qed

lemma mu_fun_poss_subst_cases_aux_mu:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  shows "(p \<in> mu_fun_poss \<mu> t \<and> (t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>) \<or>
    (\<exists>x q1 q2. q1 \<in> mu_poss \<mu> t \<and> t |_ q1 = Var x \<and> x \<in> vars_term t \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case
    by auto
next
  case (Fun f ss)
  then show ?case
  proof (cases p)
    case Nil
    then show ?thesis by auto
  next
    case (Cons i q)
    from Fun.prems[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i \<cdot> \<sigma>)"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q]
    show ?thesis
    proof
      assume orig: "q \<in> mu_fun_poss \<mu> (ss ! i) \<and>
        (ss ! i \<cdot> \<sigma>) |_ q = (ss ! i |_ q) \<cdot> \<sigma>"
      then have "p \<in> mu_fun_poss \<mu> (Fun f ss) \<and>
        (Fun f ss \<cdot> \<sigma>) |_ p = (Fun f ss |_ p) \<cdot> \<sigma>"
        using i Cons by auto
      then show ?thesis by auto
    next
      assume subst: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> (ss ! i) \<and> ss ! i |_ q1 = Var x \<and>
        x \<in> vars_term (ss ! i) \<and> q = q1 @ q2 \<and>
        q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
      then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> (ss ! i)"
        and sub: "ss ! i |_ q1 = Var x"
        and vars: "x \<in> vars_term (ss ! i)"
        and q_eq: "q = q1 @ q2"
        and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and sub_at: "(ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
        by blast
      have "i # q1 \<in> mu_poss \<mu> (Fun f ss)"
        using i q1 by auto
      moreover have "Fun f ss |_ (i # q1) = Var x"
        using i sub by simp
      moreover have "x \<in> vars_term (Fun f ss)"
        using i vars by auto
      moreover have "p = (i # q1) @ q2"
        using Cons q_eq by simp
      moreover have "(Fun f ss \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
        using i Cons q_eq sub_at by simp
      ultimately show ?thesis
        using q2 by blast
    qed
  qed
qed

lemma mu_fun_poss_subst_lift:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  using assms by (induct t arbitrary: p) auto

lemma mu_poss_subst_lift:
  assumes p: "p \<in> mu_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> (t \<cdot> \<sigma>)"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then have "p = []" by simp
  then show ?case by (cases "\<sigma> x", auto)
next
  case (Fun f ts)
  then show ?case by auto
qed

lemma mu_fun_poss_subst_cases [case_names orig subst]:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  obtains
    (orig) "p \<in> mu_fun_poss \<mu> t" "(t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>"
  | (subst) x q1 q2 where "q1 \<in> poss t" "t |_ q1 = Var x" "x \<in> vars_term t"
      "p = q1 @ q2" "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)" "(t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
  using mu_fun_poss_subst_cases_aux[OF p] by blast

lemma mu_fun_poss_replace_at_root:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and u: "is_Fun u"
  shows "p \<in> mu_fun_poss \<mu> (replace_at t p u)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      using u by (cases u, auto)
  next
    case (Cons i q)
    with Fun.prems have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i)"
      by auto
    have rec: "q \<in> mu_fun_poss \<mu> (replace_at (ss ! i) q u)"
      by (rule Fun.hyps[OF nth_mem[OF i(2)] q])
    show ?thesis
      using i rec Cons by (simp add: nth_append)
  qed
qed

lemma mu_fun_poss_replace_at_append:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and q: "q \<in> mu_fun_poss \<mu> u"
  shows "p @ q \<in> mu_fun_poss \<mu> (replace_at t p u)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      using q by simp
  next
    case (Cons i p')
    with Fun.prems have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and p': "p' \<in> mu_fun_poss \<mu> (ss ! i)"
      by auto
    have rec: "p' @ q \<in> mu_fun_poss \<mu> (replace_at (ss ! i) p' u)"
      by (rule Fun.hyps[OF nth_mem[OF i(2)] p'])
    show ?thesis
      using i rec Cons by (simp add: nth_append)
  qed
qed

lemma csstep_redex_mu_fun_poss:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csstep_p \<mu> R q"
  shows "q \<in> mu_fun_poss \<mu> s"
proof -
  from step obtain lr \<sigma> where rstep: "(s, t) \<in> rstep_r_p_s R lr q \<sigma>"
    and cond: "csstep_cond \<mu> q s"
    unfolding csstep_p_def by auto
  from rstep have lr: "lr \<in> R" and qposs: "q \<in> poss s" and redex: "s |_ q = fst lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  obtain l0 r0 where lr0: "lr = (l0, r0)"
    by (cases lr, auto)
  from wf lr have "\<exists>f ts. l0 = Fun f ts"
    unfolding wf_trs_def lr0 by auto
  then obtain f ts where l: "fst lr = Fun f ts"
    unfolding lr0 by auto
  have qfun: "q \<in> fun_poss s"
    by (rule poss_is_Fun_fun_poss[OF qposs], insert redex l, auto)
  from cond qfun show ?thesis
  proof (induct s arbitrary: q)
    case (Var x)
    then show ?case by simp
  next
    case (Fun g ss)
    show ?case
    proof (cases q)
      case Nil
      then show ?thesis by simp
    next
      case (Cons i q')
      from Fun.prems Cons have i: "i < length ss"
        and qfun': "q' \<in> fun_poss (ss ! i)"
        by auto
      have qposs': "q' \<in> poss (ss ! i)"
        by (rule fun_poss_imp_poss[OF qfun'])
      from Fun.prems(1)[unfolded csstep_cond_def, rule_format, of "[]" i q'] Cons i qposs'
      have imu: "i \<in> \<mu> (g, length ss)"
        by auto
      have cond': "csstep_cond \<mu> q' (ss ! i)"
        by (rule csstep_cond_Cons_FunD(2)[OF Fun.prems(1)[unfolded Cons]])
          (use i qposs' in auto)
      have "q' \<in> mu_fun_poss \<mu> (ss ! i)"
        by (rule Fun.hyps[OF nth_mem[OF i(1)] cond' qfun'])
      with i imu Cons show ?thesis by auto
    qed
  qed
qed

lemma replace_at_append:
  assumes p: "p \<in> poss t"
    and q: "q \<in> poss (t |_ p)"
  shows "replace_at t (p @ q) u = replace_at t p (replace_at (t |_ p) q u)"
  unfolding ctxt_of_pos_term_append[OF p]
  by (simp add: replace_at_subt_at[OF p])

lemma replace_at_overwrite:
  assumes p: "p \<in> poss t"
  shows "replace_at (replace_at t p u) p v = replace_at t p v"
  using p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t, auto)
  show ?case
    unfolding t
    using Cons.hyps[OF p] i by (simp add: nth_append)
qed

lemma csstep_mu_subterm_lift:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and step: "(t |_ p, u) \<in> csstep \<mu> R"
  shows "(t, replace_at t p u) \<in> csstep \<mu> R"
proof -
  from p have pposs: "p \<in> poss t"
    using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
  from step obtain q where stepq: "(t |_ p, u) \<in> csstep_p \<mu> R q"
    unfolding csstep_def by auto
  from stepq obtain lr \<sigma> where rstep: "(t |_ p, u) \<in> rstep_r_p_s R lr q \<sigma>"
    and cond: "csstep_cond \<mu> q (t |_ p)"
    unfolding csstep_p_def by auto
  from rstep have qposs: "q \<in> poss (t |_ p)"
    and u: "u = replace_at (t |_ p) q (snd lr \<cdot> \<sigma>)"
    unfolding rstep_r_p_s_def' by auto
  have q_mu: "q \<in> mu_fun_poss \<mu> (t |_ p)"
    by (rule csstep_redex_mu_fun_poss[OF wf stepq])
  have pq_mu: "p @ q \<in> mu_fun_poss \<mu> t"
  proof -
    have "p @ q \<in> mu_fun_poss \<mu> (replace_at t p (t |_ p))"
      by (rule mu_fun_poss_replace_at_append[OF p q_mu])
    also have "replace_at t p (t |_ p) = t"
      by (rule replace_at_ident[OF pposs refl])
    finally show ?thesis .
  qed
  have cond_pq: "csstep_cond \<mu> (p @ q) t"
    by (rule mu_fun_poss_imp_csstep_cond[OF pq_mu])
  have rstep_pq: "(t, replace_at t p u) \<in> rstep_r_p_s R lr (p @ q) \<sigma>"
    using rstep pposs qposs u
    by (auto simp: rstep_r_p_s_def' replace_at_append)
  from rstep_pq cond_pq have "(t, replace_at t p u) \<in> csstep_p \<mu> R (p @ q)"
    unfolding csstep_p_def by (cases lr, auto)
  then show ?thesis
    unfolding csstep_def by auto
qed

lemma notSN_mu_subterm_imp_notSN:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t |_ p}"
  shows "\<not> SN_on (csstep \<mu> R) {t}"
proof -
  let ?R = "csstep \<mu> R"
  from p have pposs: "p \<in> poss t"
    using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
  from notSN obtain f where f0: "f 0 = t |_ p"
    and chain: "\<And>i. (f i, f (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  define g where "g i = replace_at t p (f i)" for i
  have g0: "g 0 = t"
    unfolding g_def f0 by (rule replace_at_ident[OF pposs refl])
  have gstep: "(g i, g (Suc i)) \<in> ?R" for i
  proof -
    have f_fun: "is_Fun (f i)"
    proof (cases "f i")
      case (Var x)
      from chain[of i] have "(Var x, f (Suc i)) \<in> ?R"
        unfolding Var .
      with csstep_Var_empty_wf[OF wf, of x "f (Suc i)" \<mu>] show ?thesis
        by blast
    next
      case (Fun f' ts)
      then show ?thesis by simp
    qed
    have p_g: "p \<in> mu_fun_poss \<mu> (g i)"
      unfolding g_def by (rule mu_fun_poss_replace_at_root[OF p f_fun])
    have sub_g: "g i |_ p = f i"
      unfolding g_def by (rule replace_at_subt_at[OF pposs])
    have "(g i, replace_at (g i) p (f (Suc i))) \<in> ?R"
      by (rule csstep_mu_subterm_lift[OF wf p_g], unfold sub_g, rule chain)
    moreover have "replace_at (g i) p (f (Suc i)) = g (Suc i)"
      unfolding g_def
      by (rule replace_at_overwrite[OF pposs])
    ultimately show ?thesis by simp
  qed
  show ?thesis
    unfolding SN_on_def
    by (intro notI, insert g0 gstep, blast)
qed

lemma SN_on_mu_subterm:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and SN: "SN_on (csstep \<mu> R) {t}"
  shows "SN_on (csstep \<mu> R) {t |_ p}"
  using assms notSN_mu_subterm_imp_notSN by blast

lemma SN_on_mu_pos:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_poss \<mu> t"
    and SN: "SN_on (csstep \<mu> R) {t}"
  shows "SN_on (csstep \<mu> R) {t |_ p}"
  using p SN
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    with Fun.prems show ?thesis by simp
  next
    case (Cons i q)
    from Fun.prems(1)[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_poss \<mu> (ss ! i)"
      by auto
    have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
    proof (cases "ss ! i")
      case (Var x)
      show ?thesis unfolding Var by (rule SN_on_csstep_Var[OF wf])
    next
      case (Fun g ts)
      have "[i] \<in> mu_fun_poss \<mu> (Fun f ss)"
        using i Fun by auto
      from SN_on_mu_subterm[OF wf this Fun.prems(2)]
      show ?thesis by simp
    qed
    from Fun.hyps[OF nth_mem[OF i(2)] q SN_i]
    show ?thesis unfolding Cons by simp
  qed
qed

lemma mu_fun_poss_subst_var_lift:
  assumes p: "p \<in> mu_poss \<mu> t"
    and sub: "t |_ p = Var x"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "p @ q \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  using assms
proof (induct t arbitrary: p)
  case (Var y)
  then have "p = []" and "x = y"
    by auto
  with Var show ?case by simp
next
  case (Fun f ts)
  then show ?case
  proof (cases p)
    case Nil
    with Fun.prems(2) show ?thesis by simp
  next
    case (Cons i p')
    from Fun.prems(1)[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ts)" "i < length ts"
      and p': "p' \<in> mu_poss \<mu> (ts ! i)"
      by auto
    from Fun.prems(2)[unfolded Cons] i
    have sub': "ts ! i |_ p' = Var x"
      by simp
    from Fun.hyps[OF nth_mem[OF i(2)] p' sub' Fun.prems(3)]
    have "p' @ q \<in> mu_fun_poss \<mu> (ts ! i \<cdot> \<sigma>)" .
    with i Cons show ?thesis by auto
  qed
qed

definition mu_supt :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "mu_supt \<mu> s t \<longleftrightarrow> (\<exists>i p. i # p \<in> mu_poss \<mu> s \<and> s |_ (i # p) = t)"

definition mu_Tinf :: "'f mu \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) set \<Rightarrow> ('f, 'v) term set"
where
  "mu_Tinf \<mu> R = {t. \<not> SN_on R {t} \<and> (\<forall>s. mu_supt \<mu> t s \<longrightarrow> SN_on R {s})}"

lemma mu_supt_imp_supt:
  assumes "mu_supt \<mu> s t"
  shows "s \<rhd> t"
proof -
  from assms obtain i p where ip: "i # p \<in> mu_poss \<mu> s"
    and t: "s |_ (i # p) = t"
    unfolding mu_supt_def by auto
  have "i # p \<in> poss s"
    using ip mu_poss_imp_poss by blast
  then have "s \<rhd> s |_ (i # p)"
    by (rule subt_at_nepos_imp_supt)
  then show ?thesis
    unfolding t .
qed

lemma Tinf_imp_mu_Tinf:
  assumes "t \<in> Tinf R"
  shows "t \<in> mu_Tinf \<mu> R"
  using assms mu_supt_imp_supt unfolding Tinf_def mu_Tinf_def by blast

lemma not_SN_imp_subt_mu_Tinf:
  assumes "\<not> SN_on R {t}"
  shows "\<exists>u. t \<unrhd> u \<and> u \<in> mu_Tinf \<mu> R"
  using not_SN_imp_subt_Tinf[OF assms] Tinf_imp_mu_Tinf by blast

lemma step_SN_on_target:
  assumes SN: "SN_on R {s}"
    and step: "(s, t) \<in> R"
  shows "SN_on R {t}"
proof (rule ccontr)
  assume "\<not> SN_on R {t}"
  then obtain f where f0: "f 0 = t" and steps: "\<And>i. (f i, f (Suc i)) \<in> R"
    unfolding SN_on_def by auto
  define g where "g n = (case n of 0 \<Rightarrow> s | Suc m \<Rightarrow> f m)" for n
  have "g 0 \<in> {s}" unfolding g_def by simp
  moreover have "\<And>i. (g i, g (Suc i)) \<in> R"
  proof -
    fix i
    show "(g i, g (Suc i)) \<in> R"
    proof (cases i)
      case 0
      then show ?thesis using step f0 unfolding g_def by simp
    next
      case (Suc n)
      then show ?thesis using steps[of n] unfolding g_def by simp
    qed
  qed
  ultimately show False
    using SN unfolding SN_on_def by blast
qed

lemma step_notSN_on_source:
  assumes step: "(s, t) \<in> R"
    and notSN: "\<not> SN_on R {t}"
  shows "\<not> SN_on R {s}"
proof
  assume "SN_on R {s}"
  from step_SN_on_target[OF this step] notSN show False by contradiction
qed

lemma steps_notSN_on_source:
  assumes steps: "(s, t) \<in> R\<^sup>*"
    and notSN: "\<not> SN_on R {t}"
  shows "\<not> SN_on R {s}"
  using steps notSN
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step_notSN_on_source[OF step.hyps(2) step.prems]
  have "\<not> SN_on R {y}" .
  from step.hyps(3)[OF this] show ?case .
qed

lemma csnrstep_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csnrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
proof -
  from sT have min: "\<And>u. mu_supt \<mu> s u \<Longrightarrow> SN_on (csstep \<mu> R) {u}"
    unfolding mu_Tinf_def by auto
  show ?thesis
    unfolding mu_Tinf_def
  proof (intro CollectI conjI allI impI)
    show "\<not> SN_on (csstep \<mu> R) {t}"
      by (rule notSN_t)
  next
    fix u
    assume tu: "mu_supt \<mu> t u"
    from step show "SN_on (csstep \<mu> R) {u}"
    proof (cases s)
      case (Var x)
      from step Var have False
        using csnrstep_Var_empty[of x t \<mu> R] by simp
      then show ?thesis by blast
    next
      case (Fun f ss)
      from step[unfolded Fun] show ?thesis
      proof (elim csnrstep_FunE)
        fix i ts
        assume i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
          and t: "t = Fun f ts" and len: "length ts = length ss"
          and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
          and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
        from tu[unfolded t mu_supt_def]
        obtain j q where jq: "j # q \<in> mu_poss \<mu> (Fun f ts)"
          and u: "Fun f ts |_ (j # q) = u"
          by auto
        from jq have j: "j < length ts" and jmu: "j \<in> \<mu> (f, length ts)"
          and q: "q \<in> mu_poss \<mu> (ts ! j)"
          by auto
        show ?thesis
        proof (cases "j = i")
          case False
          have same_j: "ts ! j = ss ! j"
            using same[of j] j len False by simp
          have "j # q \<in> mu_poss \<mu> s"
            unfolding Fun using j jmu q len same_j by auto
          moreover have "s |_ (j # q) = u"
            unfolding Fun using j len False same u by simp
          ultimately have "mu_supt \<mu> s u"
            unfolding mu_supt_def by blast
          then show ?thesis by (rule min)
        next
          case True
          have "j # [] \<in> mu_poss \<mu> s"
            unfolding Fun using j jmu len by (cases "ss ! i", auto simp: True)
          moreover have "s |_ (j # []) = ss ! i"
            unfolding Fun using i True by simp
          ultimately have "mu_supt \<mu> s (ss ! i)"
            unfolding mu_supt_def by blast
          then have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
            by (rule min)
          have SN_ti: "SN_on (csstep \<mu> R) {ts ! i}"
            by (rule step_SN_on_target[OF SN_i substep])
          have q_i: "q \<in> mu_poss \<mu> (ts ! i)"
            using q True by simp
          have u_eq: "u = ts ! i |_ q"
            using u t True j by simp
          show ?thesis
            using SN_on_mu_pos[OF wf q_i SN_ti] u_eq by simp
        qed
      qed
    qed
  qed
qed

lemma csnrsteps_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and steps: "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  using steps sT notSN_t
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y, z) \<in> csstep \<mu> R"
    using step.hyps(2) unfolding csstep_root_nonroot by auto
  have notSN_y: "\<not> SN_on (csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz step.prems(2)])
  from step.hyps(3)[OF step.prems(1) notSN_y]
  have yT: "y \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  show ?case
    by (rule csnrstep_mu_Tinf_preserve[OF wf step.hyps(2) yT step.prems(2)])
qed

lemma csstep_notSN_imp_mu_Tinf_defined_subterm:
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
    defined R (f, length ts) \<and> t |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  using notSN
proof (induct t)
  case (Var x)
  from SN_on_csstep_Var[OF wf, of \<mu> x] Var.prems show ?case
    by simp
next
  case (Fun f ss)
  show ?case
  proof (cases "defined R (f, length ss)")
    case root_def: True
    show ?thesis
    proof (cases "\<forall>i<length ss. i \<in> \<mu> (f, length ss) \<longrightarrow> SN_on (csstep \<mu> R) {ss ! i}")
      case args_SN: True
      have min: "\<And>u. mu_supt \<mu> (Fun f ss) u \<Longrightarrow> SN_on (csstep \<mu> R) {u}"
      proof -
        fix u
        assume "mu_supt \<mu> (Fun f ss) u"
        then obtain i q where iq: "i # q \<in> mu_poss \<mu> (Fun f ss)"
          and u: "Fun f ss |_ (i # q) = u"
          unfolding mu_supt_def by auto
        from iq have i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
          and q: "q \<in> mu_poss \<mu> (ss ! i)"
          by auto
        from args_SN i imu have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
          by auto
        show "SN_on (csstep \<mu> R) {u}"
          using SN_on_mu_pos[OF wf q SN_i] u i by simp
      qed
      have Troot: "Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        unfolding mu_Tinf_def using Fun.prems min by auto
      show ?thesis
        apply (rule exI[where x = "[]"])
        apply (rule exI[where x = f])
        apply (rule exI[where x = ss])
        using root_def Troot apply simp
        done
    next
      case False
      then obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
        and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
        by auto
      from Fun.hyps[OF nth_mem[OF i] notSN_i]
      obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
        and sub: "ss ! i |_ p = Fun g ts"
        and def: "defined R (g, length ts)"
        and T: "ss ! i |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        by auto
      let ?p = "i # p"
      have "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
        using i imu p by auto
      moreover have "Fun f ss |_ ?p = Fun g ts"
        using i sub by simp
      moreover have "Fun f ss |_ ?p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        using i T sub by simp
      ultimately show ?thesis
        by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts], insert def, auto)
    qed
  next
    case False
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf False Fun.prems]
    obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
      and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
      by auto
    from Fun.hyps[OF nth_mem[OF i] notSN_i]
    obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
      and sub: "ss ! i |_ p = Fun g ts"
      and def: "defined R (g, length ts)"
      and T: "ss ! i |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by auto
    let ?p = "i # p"
    have "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
      using i imu p by auto
    moreover have "Fun f ss |_ ?p = Fun g ts"
      using i sub by simp
    moreover have "Fun f ss |_ ?p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      using i T sub by simp
    ultimately show ?thesis
      by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts], insert def, auto)
  qed
qed

lemma mu_Tinf_SN_on_active_subst_mu_subterm:
  assumes lhs: "is_Fun l"
    and T: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l" and lp: "l |_ p = Var x"
    unfolding mu_vars_term_def by auto
  have pq: "p @ q \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_var_lift[where t = l and x = x and \<sigma> = \<sigma>, OF p lp q])
  have pq_pos: "p @ q \<in> mu_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_imp_mu_poss[OF pq])
  have pq_ne: "p @ q \<noteq> []"
  proof
    assume "p @ q = []"
    then have "p = []" by simp
    with lp have "l = Var x" by simp
    with lhs show False by (cases l, auto)
  qed
  then obtain i p' where pq_cons: "p @ q = i # p'"
    by (cases "p @ q", auto)
  have sub: "(l \<cdot> \<sigma>) |_ (p @ q) = \<sigma> x |_ q"
    using mu_poss_imp_poss[OF p] lp
    by (simp add: subt_at_append)
  have "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x |_ q)"
    unfolding mu_supt_def
    by (intro exI[of _ i] exI[of _ p'], insert pq_pos pq_cons sub, auto)
  with T show ?thesis
    unfolding mu_Tinf_def by blast
qed

lemma Tinf_imp_SN_csnr_first_csrstep:
  assumes Tinf: "t \<in> Tinf (csstep \<mu> R)"
  shows "SN_on (csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t, s) \<in> (csnrstep \<mu> R)\<^sup>* \<and> (s, u) \<in> csrstep \<mu> R \<and>
      \<not> SN_on (csstep \<mu> R) {u})"
proof -
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  let ?rR = "csrstep \<mu> R"
  from Tinf[unfolded Tinf_def] have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. s \<lhd> t \<Longrightarrow> SN_on ?R {s}" by auto
  from notSN obtain ts where start: "ts 0 = t" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i, ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
        using steps unfolding csstep_root_nonroot by auto
      with True start show False
        unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j, ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j, ts (Suc j)) \<in> ?nR"
        unfolding csstep_root_nonroot by auto
    qed
    have pref: "(ts 0, ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}"
        by simp
      moreover have "\<And>j. (?ss j, ?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis
        unfolding SN_on_def by blast
    qed
    show ?thesis
      using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start: "ts 0 = t" and nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
      by auto
    obtain f ss where init: "ts 0 = Fun f ss"
      using nsteps[of 0] csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi" and len: "length ssi = n" by auto
      from csnrstep_preserves_root[OF nsteps[of i]]
      show ?case unfolding tsi root.simps len by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n" by force
    let ?strict = "\<lambda>i. \<exists>j<n. (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)"
          and sub: "(sss i ! j, us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and> (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
      show ?thesis
        unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0 ..< Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj have jn: "j < n" by auto
    with n have "ss ! j \<in> set ss" by auto
    with init have "ss ! j \<lhd> ts 0" by auto
    from min[unfolded start[symmetric], OF this] have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}" using ts[of 0] init by simp
    have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k, us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
        from tgt have us_eq: "sss (Suc i) = us" by simp
        show ?thesis
        proof (cases "j = k")
          case True
          with step us_eq show ?thesis by auto
        next
          case False
          from jn len[of i] have "j < length (sss i)" by simp
          from same[OF this False] us_eq show ?thesis by simp
        qed
      qed
    qed
    have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma mu_Tinf_imp_SN_csnr_first_csrstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "SN_on (csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t, s) \<in> (csnrstep \<mu> R)\<^sup>* \<and> (s, u) \<in> csrstep \<mu> R \<and>
      \<not> SN_on (csstep \<mu> R) {u})"
proof -
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  let ?rR = "csrstep \<mu> R"
  from Tinf[unfolded mu_Tinf_def] have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. mu_supt \<mu> t s \<Longrightarrow> SN_on ?R {s}" by auto
  from notSN obtain ts where start: "ts 0 = t" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i, ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
        using steps unfolding csstep_root_nonroot by auto
      with True start show False
        unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j, ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j, ts (Suc j)) \<in> ?nR"
        unfolding csstep_root_nonroot by auto
    qed
    have pref: "(ts 0, ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}"
        by simp
      moreover have "\<And>j. (?ss j, ?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis
        unfolding SN_on_def by blast
    qed
    show ?thesis
      using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start: "ts 0 = t" and nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
      unfolding SN_on_def by auto
    obtain f ss where init: "ts 0 = Fun f ss"
      using nsteps[of 0] csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi" and len: "length ssi = n" by auto
      from csnrstep_preserves_root[OF nsteps[of i]]
      show ?case unfolding tsi root.simps len by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n" by force
    let ?strict = "\<lambda>i. \<exists>j<n. j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)" and jmu: "j \<in> \<mu> (f, length (sss i))"
          and sub: "(sss i ! j, us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j jmu sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and> j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and> idx i \<in> \<mu> (f, n) \<and> (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and> j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
      show ?thesis
        unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0 ..< Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj have jn: "j < n" and jmu: "j \<in> \<mu> (f, n)" by auto
    with n have "j # [] \<in> mu_poss \<mu> (Fun f ss)"
      by (cases "ss ! j", auto)
    moreover have "Fun f ss |_ (j # []) = ss ! j"
      using jn n by simp
    ultimately have "mu_supt \<mu> (Fun f ss) (ss ! j)"
      unfolding mu_supt_def by blast
    with min[unfolded start[symmetric] init] have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}" using ts[of 0] init by simp
    have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k, us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
        from tgt have us_eq: "sss (Suc i) = us" by simp
        show ?thesis
        proof (cases "j = k")
          case True
          with step us_eq show ?thesis by auto
        next
          case False
          from jn len[of i] have "j < length (sss i)" by simp
          from same[OF this False] us_eq show ?thesis by simp
        qed
      qed
    qed
    have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma Tinf_csstep_defined_root:
  assumes wf: "wf_trs R"
    and Tinf: "Fun f ts \<in> Tinf (csstep \<mu> R)"
  shows "defined R (f, length ts)"
proof -
  from Tinf_imp_SN_csnr_first_csrstep[OF Tinf]
  obtain s u where pref: "(Fun f ts, s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s, u) \<in> csrstep \<mu> R"
    by auto
  from root obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain g ls where l: "l = Fun g ls"
    unfolding wf_trs_def by (cases l, auto)
  from csnrsteps_preserve_root[OF pref] have "root s = Some (f, length ts)"
    by simp
  with s l have "g = f" "length ls = length ts"
    by auto
  with lr l show ?thesis
    unfolding defined_def by auto
qed

context
  fixes shp :: "'f::{showl, compare_order} \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

definition mu_CSDP_on :: "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "mu_CSDP_on \<mu> D R =
    { (\<sharp> l, \<sharp> (r |_ p)) | l r p f ts.
      (l, r) \<in> R \<and> p \<in> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> \<not> mu_supt \<mu> l (r |_ p) }"

lemma rrstep_mu_CSDP_onI:
  assumes lr: "(l, r) \<in> R"
    and lhs: "is_Fun l"
    and p: "p \<in> mu_fun_poss \<mu> r"
    and sub: "r |_ p = Fun f ts"
    and D: "(f, length ts) \<in> D"
    and ns: "\<not> mu_supt \<mu> l (r |_ p)"
  shows "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (mu_CSDP_on \<mu> D R)"
proof -
  have dp: "(\<sharp> l, \<sharp> (r |_ p)) \<in> mu_CSDP_on \<mu> D R"
    unfolding mu_CSDP_on_def
    apply (rule CollectI)
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p sub D ns by auto
  have l: "\<sharp> (l \<cdot> \<sigma>) = \<sharp> l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  have r: "\<sharp> ((r |_ p) \<cdot> \<sigma>) = \<sharp> (r |_ p) \<cdot> \<sigma>"
    using sub by simp
  then show ?thesis
    using dp l by auto
qed

lemma csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (\<sharp> s, \<sharp> u) \<in> rrstep (mu_CSDP_on \<mu> D R)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    from D def len have fD: "(f, length ts) \<in> D"
      by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l"
        using iq mu_poss_imp_poss by blast
      have "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      moreover have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>]
              \<open>(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>\<close>, auto)
      ultimately have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        using sT unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False
        by simp
    qed
    have rr: "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (mu_CSDP_on \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    show ?thesis
      using rr T_p sub_subst unfolding s by auto
  next
    assume "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and> r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    have "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    with vc lr have x_l: "x \<in> mu_vars_term \<mu> l"
      unfolding rhs_mu_vars_condition_def by blast
    have lT: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      using sT unfolding s .
    have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs lT x_l q2])
    with notSN_p sub_q2 show ?thesis
      by simp
  qed
qed

lemma csnrsteps_imp_sharp_rsteps:
  assumes "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
  shows "(\<sharp> s, \<sharp> t) \<in> (rstep R)\<^sup>*"
proof -
  have "(s, t) \<in> (nrrstep R)\<^sup>*"
    using assms
  proof (induct rule: rtrancl_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    from csnrstep_imp_nrrstep[OF step.hyps(2)]
    have "(y, z) \<in> nrrstep R" .
    with step.hyps(3) show ?case by auto
  qed
  then show ?thesis
    by (rule nrrsteps_imp_sharp_rsteps)
qed

lemma mu_Tinf_imp_mu_CSDP_relstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
proof -
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t, s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s, v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}"
    by auto
  have sv: "(s, v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  from csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on[OF wf root sT notSN_v vc D]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and dp: "(\<sharp> s, \<sharp> u) \<in> rrstep (mu_CSDP_on \<mu> D R)"
    by blast
  have left: "(\<sharp> t, \<sharp> s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have right: "(\<sharp> u, \<sharp> u) \<in> (rstep R)\<^sup>*"
    by simp
  have "(\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    using left dp right by auto
  with uT show ?thesis by blast
qed

lemma CSDP_list:
  "set (CSDP_list shp R \<mu> D) = CSDP_on shp (mu_of \<mu>) (set D) (set R)"
proof
  show "set (CSDP_list shp R \<mu> D) \<subseteq> CSDP_on shp (mu_of \<mu>) (set D) (set R)"
  proof
    fix dp
    assume "dp \<in> set (CSDP_list shp R \<mu> D)"
    then obtain lr p where
      lr: "lr \<in> set R" and p: "p \<in> set (mu_fun_poss_list \<mu> (snd lr))"
      and ns: "\<not> fst lr \<rhd> snd lr |_ p"
      and def: "(case snd lr |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)"
      and dp: "dp = (\<sharp> (fst lr), \<sharp> (snd lr |_ p))"
      unfolding CSDP_list_def Let_def by auto
    obtain l r where lr_pair: "lr = (l, r)"
      by force
    show "dp \<in> CSDP_on shp (mu_of \<mu>) (set D) (set R)"
    proof (cases "r |_ p")
      case (Var x)
      with def lr_pair show ?thesis by simp
    next
      case (Fun f ts)
      show ?thesis
        unfolding CSDP_on_def
        apply (rule CollectI)
        apply (rule exI[of _ l])
        apply (rule exI[of _ r])
        apply (rule exI[of _ p])
        apply (rule exI[of _ f])
        apply (rule exI[of _ ts])
        using lr p ns def dp lr_pair Fun by auto
    qed
  qed
next
  show "CSDP_on shp (mu_of \<mu>) (set D) (set R) \<subseteq> set (CSDP_list shp R \<mu> D)"
  proof
    fix dp
    assume "dp \<in> CSDP_on shp (mu_of \<mu>) (set D) (set R)"
    then obtain l r p f ts where
      lr: "(l, r) \<in> set R" and p: "p \<in> mu_fun_poss (mu_of \<mu>) r"
      and sub: "r |_ p = Fun f ts" and D: "(f, length ts) \<in> set D"
      and ns: "\<not> l \<rhd> r |_ p" and dp: "dp = (\<sharp> l, \<sharp> (r |_ p))"
      unfolding CSDP_on_def by auto
    from lr obtain bef aft where R: "R = bef @ (l, r) # aft"
      by (metis split_list)
    from p have p_list: "p \<in> set (mu_fun_poss_list \<mu> r)"
      by simp
    have p_filter: "p \<in> set (filter
        (\<lambda>p. \<not> l \<rhd> r |_ p \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r))"
      using p_list sub D ns by simp
    have pair_mem: "dp \<in> set (map (\<lambda>p. (\<sharp> l, \<sharp> (r |_ p))) (filter
        (\<lambda>p. \<not> l \<rhd> r |_ p \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r)))"
    proof -
      have "(\<sharp> l, \<sharp> (r |_ p)) \<in> (\<lambda>p. (\<sharp> l, \<sharp> (r |_ p))) ` set (filter
          (\<lambda>p. \<not> l \<rhd> r |_ p \<and> (case r |_ p of Var x \<Rightarrow> False
            | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r))"
        by (rule image_eqI[of _ _ p], insert p_filter, auto)
      then show ?thesis
        using dp by simp
    qed
    show "dp \<in> set (CSDP_list shp R \<mu> D)"
      unfolding CSDP_list_def R Let_def
      using pair_mem by auto
  qed
qed

lemma rrstep_CSDP_onI:
  assumes lr: "(l, r) \<in> R"
    and lhs: "is_Fun l"
    and p: "p \<in> mu_fun_poss \<mu> r"
    and sub: "r |_ p = Fun f ts"
    and D: "(f, length ts) \<in> D"
    and ns: "\<not> l \<rhd> r |_ p"
  shows "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (CSDP_on shp \<mu> D R)"
proof -
  have dp: "(\<sharp> l, \<sharp> (r |_ p)) \<in> CSDP_on shp \<mu> D R"
    unfolding CSDP_on_def
    apply (rule CollectI)
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p sub D ns by auto
  have l: "\<sharp> (l \<cdot> \<sigma>) = \<sharp> l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  have r: "\<sharp> ((r |_ p) \<cdot> \<sigma>) = \<sharp> (r |_ p) \<cdot> \<sigma>"
    using sub by simp
  then show ?thesis
    using dp l by auto
qed

definition exposed_fun_poss :: "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set"
where
  "exposed_fun_poss \<mu> D t =
    {p @ q | p q f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> q \<in> fun_poss (t |_ p)}"

definition exposed_CSDP_on :: "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "exposed_CSDP_on \<mu> D R =
    { (sharp_term shp l, sharp_term shp (r |_ p)) | l r p f ts.
      (l, r) \<in> R \<and> p \<in> exposed_fun_poss \<mu> D r \<and> r |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> \<not> l \<rhd> r |_ p }"

lemma exposed_fun_possI:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and sub: "t |_ p = Fun f ts"
    and D: "(f, length ts) \<in> D"
    and q: "q \<in> fun_poss (t |_ p)"
  shows "p @ q \<in> exposed_fun_poss \<mu> D t"
  using assms unfolding exposed_fun_poss_def by blast

lemma rrstep_exposed_CSDP_onI:
  assumes lr: "(l, r) \<in> R"
    and lhs: "is_Fun l"
    and p: "p \<in> exposed_fun_poss \<mu> D r"
    and sub: "r |_ p = Fun f ts"
    and D: "(f, length ts) \<in> D"
    and ns: "\<not> l \<rhd> r |_ p"
  shows "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (exposed_CSDP_on \<mu> D R)"
proof -
  have dp: "(\<sharp> l, \<sharp> (r |_ p)) \<in> exposed_CSDP_on \<mu> D R"
    unfolding exposed_CSDP_on_def
    apply (rule CollectI)
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p sub D ns by auto
  have l: "\<sharp> (l \<cdot> \<sigma>) = \<sharp> l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  have r: "\<sharp> ((r |_ p) \<cdot> \<sigma>) = \<sharp> (r |_ p) \<cdot> \<sigma>"
    using sub by simp
  then show ?thesis
    using dp l by auto
qed

lemma csrstep_Tinf_rhs_imp_rrstep_exposed_CSDP_on:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and sT: "s \<in> Tinf (csstep \<mu> R)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> Tinf (csstep \<mu> R) \<and>
    (\<sharp> s, \<sharp> u) \<in> rrstep (exposed_CSDP_on \<mu> D R)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from wf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from csstep_notSN_imp_mu_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and notSN_p: "\<not> SN_on (csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    by blast
  from mu_fun_poss_subst_cases_aux[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    from D def len have fD: "(f, length ts) \<in> D"
      by auto
    from not_SN_imp_subt_Tinf[OF notSN_p]
    obtain v where sub_v_inst: "(r \<cdot> \<sigma>) |_ p \<unrhd> v"
      and vT: "v \<in> Tinf (csstep \<mu> R)"
      by auto
    have var_r: "\<And>x. x \<in> vars_term (r |_ p) \<Longrightarrow> x \<in> vars_term r"
    proof -
      fix x
      assume x: "x \<in> vars_term (r |_ p)"
      from fun_poss_imp_poss[OF p_r[THEN mu_fun_poss_imp_fun_poss]]
      have p_poss: "p \<in> poss r" .
      from x show "x \<in> vars_term r"
        using vars_term_subt_at[OF p_poss] by auto
    qed
    have no_subst: "\<forall>x\<in>vars_term (r |_ p). \<not> \<sigma> x \<unrhd> v"
    proof
      fix x
      assume x: "x \<in> vars_term (r |_ p)"
      show "\<not> \<sigma> x \<unrhd> v"
      proof
        assume "\<sigma> x \<unrhd> v"
        from var_r[OF x] vars have x_l: "x \<in> vars_term l"
          by auto
        from lhs x_l have "l \<rhd> Var x"
          using supteq_Var[of x l] unfolding supt_supteq_conv
          by (cases l, auto)
        then have "l \<cdot> \<sigma> \<rhd> Var x \<cdot> \<sigma>"
          by (rule supt_subst)
        moreover from \<open>\<sigma> x \<unrhd> v\<close> have "Var x \<cdot> \<sigma> \<unrhd> v"
          by simp
        ultimately have "l \<cdot> \<sigma> \<rhd> v"
          by (rule supt_supteq_trans)
        then have "s \<rhd> v"
          unfolding s by simp
        with sT have "SN_on (csstep \<mu> R) {v}"
          unfolding Tinf_def by auto
        with vT show False
          unfolding Tinf_def by auto
      qed
    qed
    from sub_v_inst[unfolded sub_subst]
    have "(r |_ p) \<cdot> \<sigma> \<unrhd> v" .
    with no_subst
    obtain u where sub_u: "r |_ p \<unrhd> u" and v: "v = u \<cdot> \<sigma>"
      using subt_instance_and_not_subst_imp_subt[where s = "r |_ p" and \<sigma> = \<sigma>] by auto
    have u_fun: "is_Fun u"
    proof (rule ccontr)
      assume "\<not> is_Fun u"
      then obtain x where u: "u = Var x"
        by (cases u, auto)
      from sub_u u have x: "x \<in> vars_term (r |_ p)"
        using subteq_Var_imp_in_vars_term by auto
      have "\<sigma> x \<unrhd> v"
        unfolding v u by simp
      with no_subst x show False
        by auto
    qed
    then obtain h hs where u: "u = Fun h hs"
      by (cases u, auto)
    from v vT have uT: "u \<cdot> \<sigma> \<in> Tinf (csstep \<mu> R)"
      by simp
    have hT: "Fun h (map (\<lambda>t. t \<cdot> \<sigma>) hs) \<in> Tinf (csstep \<mu> R)"
      using uT unfolding u by simp
    from Tinf_csstep_defined_root[OF wf hT]
    have hdef: "defined R (h, length hs)"
      by simp
    with D have hD: "(h, length hs) \<in> D"
      by auto
    from supteq_imp_subt_at[OF sub_u]
    obtain q where q_poss: "q \<in> poss (r |_ p)" and u_sub: "u = r |_ p |_ q"
      by auto
    from u_fun q_poss u_sub have q_fun: "q \<in> fun_poss (r |_ p)"
      using poss_is_Fun_fun_poss by blast
    from fun_poss_imp_poss[OF p_r[THEN mu_fun_poss_imp_fun_poss]]
    have p_poss: "p \<in> poss r" .
    have pq_sub: "r |_ (p @ q) = u"
      using p_poss q_poss u_sub by (simp add: subt_at_append)
    have pq_exp: "p @ q \<in> exposed_fun_poss \<mu> D r"
      by (rule exposed_fun_possI[OF p_r rp fD q_fun])
    have ns: "\<not> l \<rhd> r |_ (p @ q)"
    proof
      assume "l \<rhd> r |_ (p @ q)"
      then have "l \<cdot> \<sigma> \<rhd> (r |_ (p @ q)) \<cdot> \<sigma>"
        by (rule supt_subst)
      with sT have "SN_on (csstep \<mu> R) {(r |_ (p @ q)) \<cdot> \<sigma>}"
        unfolding Tinf_def s by auto
      with uT pq_sub show False
        unfolding Tinf_def by simp
    qed
    have rr: "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ (p @ q)) \<cdot> \<sigma>)) \<in>
      rrstep (exposed_CSDP_on \<mu> D R)"
      by (rule rrstep_exposed_CSDP_onI[OF lr lhs pq_exp _ hD ns],
          unfold pq_sub u, simp)
    show ?thesis
      using rr uT pq_sub unfolding s by auto
  next
    assume "\<exists>x q1 q2. q1 \<in> poss r \<and> r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q2 where x_r: "x \<in> vars_term r"
      and q2_mu: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    from vars x_r have x_l: "x \<in> vars_term l"
      by auto
    from lhs x_l have l_supt_x: "l \<rhd> Var x"
      using supteq_Var[of x l] unfolding supt_supteq_conv
      by (cases l, auto)
    then have "l \<cdot> \<sigma> \<rhd> Var x \<cdot> \<sigma>"
      by (rule supt_subst)
    with sT have SN_x: "SN_on (csstep \<mu> R) {\<sigma> x}"
      unfolding Tinf_def s by auto
    have SN_q2: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule SN_on_mu_subterm[OF wf q2_mu SN_x])
    with notSN_p sub_q2 show ?thesis
      by simp
  qed
qed

lemma Tinf_imp_exposed_CSDP_relstep_if_csnrsteps_preserve_Tinf:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> Tinf (csstep \<mu> R)"
    and D: "{f. defined R f} \<subseteq> D"
    and pres: "\<And>s. (t, s) \<in> (csnrstep \<mu> R)\<^sup>* \<Longrightarrow>
      \<not> SN_on (csstep \<mu> R) {s} \<Longrightarrow> s \<in> Tinf (csstep \<mu> R)"
  shows "\<exists>u. u \<in> Tinf (csstep \<mu> R) \<and>
    (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (exposed_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
proof -
  from Tinf_imp_SN_csnr_first_csrstep[OF Tinf]
  obtain s v where pref: "(t, s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s, v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}"
    by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
  proof
    assume "SN_on (csstep \<mu> R) {s}"
    moreover have "(s, v) \<in> csstep \<mu> R"
      using root unfolding csstep_root_nonroot by auto
    ultimately have "SN_on (csstep \<mu> R) {v}"
    proof -
      assume SNs: "SN_on (csstep \<mu> R) {s}"
        and sv: "(s, v) \<in> csstep \<mu> R"
      show "SN_on (csstep \<mu> R) {v}"
      proof (rule ccontr)
        assume "\<not> SN_on (csstep \<mu> R) {v}"
        then obtain f where f0: "f 0 = v"
          and fstep: "\<And>i. (f i, f (Suc i)) \<in> csstep \<mu> R"
          unfolding SN_on_def by auto
        define g where "g n = (case n of 0 \<Rightarrow> s | Suc m \<Rightarrow> f m)" for n
        have "g 0 \<in> {s}"
          unfolding g_def by simp
        moreover have "\<And>i. (g i, g (Suc i)) \<in> csstep \<mu> R"
        proof -
          fix i
          show "(g i, g (Suc i)) \<in> csstep \<mu> R"
            using sv f0 fstep[of "i - 1"]
            by (cases i, auto simp: g_def)
        qed
        ultimately show False
          using SNs unfolding SN_on_def by blast
      qed
    qed
    with notSN_v show False by simp
  qed
  have sT: "s \<in> Tinf (csstep \<mu> R)"
    by (rule pres[OF pref notSN_s])
  from csrstep_Tinf_rhs_imp_rrstep_exposed_CSDP_on[OF wf root sT notSN_v D]
  obtain u where uT: "u \<in> Tinf (csstep \<mu> R)"
    and dp: "(\<sharp> s, \<sharp> u) \<in> rrstep (exposed_CSDP_on \<mu> D R)"
    by blast
  have left: "(\<sharp> t, \<sharp> s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have right: "(\<sharp> u, \<sharp> u) \<in> (rstep R)\<^sup>*"
    by simp
  have "(\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (exposed_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    using left dp right by auto
  with uT show ?thesis by blast
qed

lemma csrstep_Tinf_rhs_imp_rrstep_CSDP_on:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and sT: "s \<in> Tinf (csstep \<mu> R)"
    and tT: "t \<in> Tinf (csstep \<mu> R)"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> Tinf (csstep \<mu> R) \<and>
    (\<sharp> s, \<sharp> u) \<in> rrstep (CSDP_on shp \<mu> D R)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  have l_not_supt_r: "\<not> l \<rhd> r"
  proof
    assume "l \<rhd> r"
    then have "l \<cdot> \<sigma> \<rhd> r \<cdot> \<sigma>"
      by (rule supt_subst)
    with sT have "SN_on (csstep \<mu> R) {r \<cdot> \<sigma>}"
      unfolding Tinf_def s by auto
    with tT t show False
      unfolding Tinf_def by auto
  qed
  have r_fun: "is_Fun r"
  proof (rule ccontr)
    assume "\<not> is_Fun r"
    then obtain x where r: "r = Var x"
      by (cases r, auto)
    from wf lr have vars: "vars_term r \<subseteq> vars_term l"
      unfolding wf_trs_def by auto
    from vars have "x \<in> vars_term l"
      unfolding r by simp
    with lhs have "l \<rhd> Var x"
      using supteq_Var[of x l] unfolding supt_supteq_conv
      by (cases l, auto)
    then have "l \<cdot> \<sigma> \<rhd> Var x \<cdot> \<sigma>"
      by (rule supt_subst)
    with sT have "SN_on (csstep \<mu> R) {Var x \<cdot> \<sigma>}"
      unfolding Tinf_def s by auto
    with tT r t show False
      unfolding Tinf_def by auto
  qed
  then obtain f ts where r: "r = Fun f ts"
    by (cases r, auto)
  have t_fun: "Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts) \<in> Tinf (csstep \<mu> R)"
    using tT unfolding t r by simp
  from Tinf_csstep_defined_root[OF wf t_fun]
  have def: "defined R (f, length (map (\<lambda>t. t \<cdot> \<sigma>) ts))" .
  with D have fD: "(f, length ts) \<in> D"
    by auto
  have p0: "[] \<in> mu_fun_poss \<mu> r"
    by (simp add: r)
  have sub0: "r |_ [] = Fun f ts"
    by (simp add: r)
  have ns0: "\<not> l \<rhd> r |_ []"
    using l_not_supt_r by simp
  have "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ []) \<cdot> \<sigma>)) \<in> rrstep (CSDP_on shp \<mu> D R)"
    by (rule rrstep_CSDP_onI[OF lr lhs p0 sub0 fD ns0])
  then show ?thesis
    using tT unfolding s t by auto
qed

lemma csrstep_notSN_rhs_imp_rrstep_CSDP_on:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and sT: "s \<in> Tinf (csstep \<mu> R)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. \<not> SN_on (csstep \<mu> R) {u} \<and>
    (\<sharp> s, \<sharp> u) \<in> rrstep (CSDP_on shp \<mu> D R)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from wf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from csstep_notSN_imp_mu_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and notSN_p: "\<not> SN_on (csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    by blast
  from mu_fun_poss_subst_cases_aux[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    from D def len have fD: "(f, length ts) \<in> D"
      by auto
    have ns: "\<not> l \<rhd> r |_ p"
    proof
      assume supt: "l \<rhd> r |_ p"
      then have "l \<cdot> \<sigma> \<rhd> (r |_ p) \<cdot> \<sigma>"
        by (rule supt_subst)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding Tinf_def s by auto
      with notSN_p sub_subst show False
        by simp
    qed
    have rr: "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (CSDP_on shp \<mu> D R)"
      by (rule rrstep_CSDP_onI[OF lr lhs p_r rp fD ns])
    show ?thesis
      using rr notSN_p sub_subst unfolding s by auto
  next
    assume "\<exists>x q1 q2. q1 \<in> poss r \<and> r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where x_r: "x \<in> vars_term r"
      and q2_mu: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    from vars x_r have x_l: "x \<in> vars_term l"
      by auto
    from lhs x_l have l_supt_x: "l \<rhd> Var x"
      using supteq_Var[of x l] unfolding supt_supteq_conv
      by (cases l, auto)
    then have "l \<cdot> \<sigma> \<rhd> Var x \<cdot> \<sigma>"
      by (rule supt_subst)
    with sT have SN_x: "SN_on (csstep \<mu> R) {\<sigma> x}"
      unfolding Tinf_def s by auto
    have SN_q2: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule SN_on_mu_subterm[OF wf q2_mu SN_x])
    with notSN_p sub_q2 show ?thesis
      by simp
  qed
qed

lemma csrstep_notSN_rhs_imp_CSDP_or_supt:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and D: "{f. defined R f} \<subseteq> D"
  shows "(\<exists>u. \<not> SN_on (csstep \<mu> R) {u} \<and>
      (\<sharp> s, \<sharp> u) \<in> rrstep (CSDP_on shp \<mu> D R)) \<or>
    (\<exists>u. s \<rhd> u \<and> \<not> SN_on (csstep \<mu> R) {u})"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from wf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from csstep_notSN_imp_mu_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and notSN_p: "\<not> SN_on (csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    by blast
  from mu_fun_poss_subst_cases_aux[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    show ?thesis
    proof (cases "l \<rhd> r |_ p")
      case True
      then have "l \<cdot> \<sigma> \<rhd> (r |_ p) \<cdot> \<sigma>"
        by (rule supt_subst)
      with notSN_p sub_subst show ?thesis
        unfolding s by auto
    next
      case False
      from D def len have fD: "(f, length ts) \<in> D"
        by auto
      have rr: "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (CSDP_on shp \<mu> D R)"
        by (rule rrstep_CSDP_onI[OF lr lhs p_r rp fD False])
      with notSN_p sub_subst show ?thesis
        unfolding s by auto
    qed
  next
    assume "\<exists>x q1 q2. q1 \<in> poss r \<and> r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where x_r: "x \<in> vars_term r"
      and q2_mu: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    from vars x_r have x_l: "x \<in> vars_term l"
      by auto
    from lhs x_l have l_supt_x: "l \<rhd> Var x"
      using supteq_Var[of x l] unfolding supt_supteq_conv
      by (cases l, auto)
    then have supt_x: "l \<cdot> \<sigma> \<rhd> Var x \<cdot> \<sigma>"
      by (rule supt_subst)
    from q2_mu have q2_pos: "q2 \<in> poss (\<sigma> x)"
      using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
    have "Var x \<cdot> \<sigma> \<unrhd> \<sigma> x |_ q2"
      using subt_at_imp_supteq[OF q2_pos] by simp
    from supt_supteq_trans[OF supt_x this] have "s \<rhd> \<sigma> x |_ q2"
      unfolding s by simp
    with notSN_p sub_q2 show ?thesis
      by auto
  qed
qed

lemma reduced_csr_dependency_pairs_tt_finite_CSDP_on:
  assumes J: "dpp_spec J"
    and tt: "reduced_csr_dependency_pairs_tt shp J \<mu> R P = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "finite_dpp
    (False, False, CSDP_on shp (mu_of \<mu>) (set (defined_list R)) (set R), {}, {}, {}, set R)"
proof -
  interpret dpp_spec J by fact
  let ?D = "defined_list R"
  let ?P = "CSDP_on shp (mu_of \<mu>) (set ?D) (set R)"
  note tt' = tt[unfolded reduced_csr_dependency_pairs_tt_def Let_def, simplified]
  from tt' have d: "d = dpp_ops.mk J False False P [] [] [] R"
    by auto
  from tt' have cover: "\<And>dp. dp \<in> set (CSDP_list shp R \<mu> ?D) \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    by auto
  have cover': "\<And>dp. dp \<in> ?P \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    using cover unfolding CSDP_list by auto
  have finP: "finite_dpp (False, False, set P, {}, {}, {}, set R)"
    using fin unfolding d mk_sound by simp
  show ?thesis
  proof (rule finite_dpp_rename_vars[OF finP])
    fix dp
    assume "dp \<in> ?P"
    from cover'[OF this] show "\<exists>dp'. dp' \<in> set P \<and> dp =\<^sub>v dp'"
      using eq_rule_mod_vars_refl[of dp] by blast
  qed auto
qed

lemma finite_CSDP_on_imp_SN_rel:
  assumes fin: "finite_dpp (False, False, CSDP_on shp \<mu> D R, {}, {}, {}, R)"
  shows "SN_rel (rrstep (CSDP_on shp \<mu> D R)) (rstep R)"
  using fin
  unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp

lemma finite_mu_CSDP_on_imp_SN_rel:
  assumes fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN_rel (rrstep (mu_CSDP_on \<mu> D R)) (rstep R)"
  using fin
  unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp

lemma finite_mu_CSDP_on_imp_SN_csstep_if_mu_Tinf_progress:
  assumes progress: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
        (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    and fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  let ?P = "rrstep (mu_CSDP_on \<mu> D R)"
  let ?S = "rstep R"
  let ?rel = "?S\<^sup>* O ?P O ?S\<^sup>*"
  have step_ex: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using progress by blast
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<longrightarrow>
    u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    nxt t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> (csstep \<mu> R)" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] have "nxt (ts n) \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by simp
    show ?case
      using \<open>nxt (ts n) \<in> mu_Tinf \<mu> (csstep \<mu> R)\<close>
      unfolding ts_def by simp
  qed
  have ts_step: "(\<sharp> (ts n), \<sharp> (ts (Suc n))) \<in> ?rel" for n
  proof -
    from nxt[OF ts_T[of n]]
    have step: "(\<sharp> (ts n), \<sharp> (nxt (ts n))) \<in> ?rel"
      by simp
    show ?thesis
      using step unfolding ts_def by simp
  qed
  define f where "f n = \<sharp> (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel ?P ?S"
    unfolding SN_rel_on_def SN_defs
    using chain by blast
  moreover from finite_mu_CSDP_on_imp_SN_rel[OF fin]
  have "SN_rel ?P ?S" .
  ultimately show False by contradiction
qed

lemma finite_mu_CSDP_on_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
  by (rule finite_mu_CSDP_on_imp_SN_csstep_if_mu_Tinf_progress[OF _ fin],
      rule mu_Tinf_imp_mu_CSDP_relstep[OF wf _ vc D])

lemma finite_exposed_CSDP_on_imp_SN_rel:
  assumes fin: "finite_dpp (False, False, exposed_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN_rel (rrstep (exposed_CSDP_on \<mu> D R)) (rstep R)"
  using fin
  unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp

lemma finite_exposed_CSDP_on_imp_SN_csstep_if_Tinf_progress:
  assumes progress: "\<And>t. t \<in> Tinf (csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> Tinf (csstep \<mu> R) \<and>
        (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (exposed_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    and fin: "finite_dpp (False, False, exposed_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  let ?P = "rrstep (exposed_CSDP_on \<mu> D R)"
  let ?S = "rstep R"
  let ?rel = "?S\<^sup>* O ?P O ?S\<^sup>*"
  have step_ex: "\<And>t. t \<in> Tinf (csstep \<mu> R) \<Longrightarrow>
    \<exists>u. u \<in> Tinf (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using progress by blast
  have all_ex: "\<forall>t. \<exists>u. t \<in> Tinf (csstep \<mu> R) \<longrightarrow>
    u \<in> Tinf (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> Tinf (csstep \<mu> R) \<Longrightarrow>
    nxt t \<in> Tinf (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> Tinf (csstep \<mu> R)" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] have "nxt (ts n) \<in> Tinf (csstep \<mu> R)"
      by simp
    show ?case
      using \<open>nxt (ts n) \<in> Tinf (csstep \<mu> R)\<close>
      unfolding ts_def by simp
  qed
  have ts_step: "(\<sharp> (ts n), \<sharp> (ts (Suc n))) \<in> ?rel" for n
  proof -
    from nxt[OF ts_T[of n]]
    have step: "(\<sharp> (ts n), \<sharp> (nxt (ts n))) \<in> ?rel"
      by simp
    show ?thesis
      using step unfolding ts_def by simp
  qed
  define f where "f n = \<sharp> (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel ?P ?S"
    unfolding SN_rel_on_def SN_defs
    using chain by blast
  moreover from finite_exposed_CSDP_on_imp_SN_rel[OF fin]
  have "SN_rel ?P ?S" .
  ultimately show False by contradiction
qed

end

end
