(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_Switch
  imports
    CSR_Minimal_CSDP_Proofs
    CR.Orthogonality_Impl
begin

text \<open>
  Executable applicability test for the Giesl--Middeldorp switch from
  termination to innermost termination of context-sensitive rewriting.

  Root overlaps are harmless only when their critical pair is trivial.  A
  proper overlap is rejected even if its critical pair happens to be trivial:
  the proof of the switch needs the non-overlap property for proper subterms of
  left-hand sides.  Left-linearity is checked separately; Example 10 of
  Giesl--Middeldorp shows that non-overlap alone is insufficient.
\<close>

definition check_csr_orthogonal ::
  "('f::{showl,compare_order},string) rules
    \<Rightarrow> showsl check"
where
  "check_csr_orthogonal R = do {
    check_left_linear_trs R
      <+? (\<lambda>s. showsl_lit
        (STR ''the CSR is not left-linear\<newline>'') \<circ> s);
    check_allm (\<lambda>(at_root,s,t).
      check (at_root \<and> s = t)
        (showsl_lit
          (STR ''the CSR has a non-root or non-trivial overlap: '') \<circ>
         showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t))
      (critical_pairs_impl string_rename R R)
  }"

definition csr_switch_overlay ::
  "('f, string) trs \<Rightarrow> bool"
where
  "csr_switch_overlay R \<longleftrightarrow>
    left_linear_trs R \<and>
    (\<forall>b s t. (b,s,t) \<in> critical_pairs string_rename R R \<longrightarrow>
      b \<and> s = t)"

text \<open>
  This first executable criterion deliberately rejects every proper ordinary
  overlap, including overlaps at frozen positions.  At the root it admits
  only trivial critical pairs, the weak-orthogonality generalization needed
  by the confluence part of the switch proof.  A later completeness refinement
  may retain proper overlaps whose positions are frozen by the replacement
  map; it must not silently weaken the semantic premise consumed below.
\<close>

lemma check_csr_orthogonal_left_linear:
  assumes "isOK (check_csr_orthogonal R)"
  shows "left_linear_trs (set R)"
  using assms unfolding check_csr_orthogonal_def by auto

lemma check_csr_orthogonal_critical_pairs:
  assumes ok: "isOK (check_csr_orthogonal R)"
    and cp: "(at_root,s,t) \<in>
      critical_pairs string_rename (set R) (set R)"
  shows "at_root \<and> s = t"
proof -
  from cp have mem:
    "(at_root,s,t) \<in> set (critical_pairs_impl string_rename R R)"
    by simp
  from ok mem show ?thesis
    unfolding check_csr_orthogonal_def by auto
qed

lemma check_csr_orthogonal_no_proper_overlap:
  assumes ok: "isOK (check_csr_orthogonal R)"
    and cp: "(False,s,t) \<in>
      critical_pairs string_rename (set R) (set R)"
  shows False
  using check_csr_orthogonal_critical_pairs[OF ok cp] by simp

lemma check_csr_orthogonal_sound:
  assumes "isOK (check_csr_orthogonal R)"
  shows "csr_switch_overlay (set R)"
  unfolding csr_switch_overlay_def
  using check_csr_orthogonal_left_linear[OF assms]
    check_csr_orthogonal_critical_pairs[OF assms]
  by blast

lemma csr_switch_overlay_proper_lhs_instance_NF:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and lr: "(l,r) \<in> R"
    and proper: "l \<rhd> u"
    and subst_NF: "\<And>x. x \<in> vars_term l \<Longrightarrow> \<delta> x \<in> NF_trs R"
  shows "u \<cdot> \<delta> \<in> NF_trs R"
proof (rule ccontr)
  assume "u \<cdot> \<delta> \<notin> NF_trs R"
  then obtain v where step: "(u \<cdot> \<delta>,v) \<in> rstep R"
    by (auto simp: NF_iff_no_step)
  then obtain l' r' \<sigma> C where
    redex: "u \<cdot> \<delta> = C\<langle>l' \<cdot> \<sigma>\<rangle>"
    and lr': "(l',r') \<in> R"
    by auto
  have sup: "u \<cdot> \<delta> \<unrhd> l' \<cdot> \<sigma>"
    unfolding redex by auto
  from supteq_subst_cases'[OF sup]
  show False
  proof
    assume "\<exists>x. x \<in> vars_term u \<and> \<delta> x \<unrhd> l' \<cdot> \<sigma>"
    then obtain x where xu: "x \<in> vars_term u"
      and xredex: "\<delta> x \<unrhd> l' \<cdot> \<sigma>"
      by blast
    have xl: "x \<in> vars_term l"
      using proper xu supteq_imp_vars_term_subset by blast
    have redex_not_NF: "l' \<cdot> \<sigma> \<notin> NF_trs R"
      unfolding NF_iff_no_step
      using rstep_subst[OF rstep_rule[OF lr'], of \<sigma>] by blast
    from NF_subterm[OF subst_NF[OF xl] xredex]
      redex_not_NF show False by blast
  next
    assume "\<exists>w \<unlhd>u. is_Fun w \<and> l' \<cdot> \<sigma> = w \<cdot> \<delta>"
    then obtain w where wu: "u \<unrhd> w" and wfun: "is_Fun w"
      and match: "l' \<cdot> \<sigma> = w \<cdot> \<delta>"
      by blast
    from mgu_vd_complete[OF match[symmetric], of string_rename]
    obtain \<mu>1 \<mu>2 where mgu:
      "mgu_vd string_rename w l' = Some (\<mu>1,\<mu>2)"
      by auto
    have wl: "l \<rhd> w"
      by (rule supt_supteq_trans[OF proper wu])
    then obtain D where lD: "l = D\<langle>w\<rangle>" and D_ne: "D \<noteq> \<box>"
      by auto
    have cp: "(False,
        (D \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>,
        r \<cdot> \<mu>1) \<in> critical_pairs string_rename R R"
      by (rule critical_pairsI[OF lr lr' lD wfun mgu refl refl],
          simp add: D_ne)
    from ortho cp show False
      unfolding csr_switch_overlay_def by blast
  qed
qed

text \<open>
  Innermost context-sensitive rewriting is represented separately from both
  ordinary innermost rewriting and Q-restricted ordinary rewriting.  A
  context-sensitive step is innermost precisely when every proper active
  subterm of the contracted redex is a context-sensitive normal form.  Keeping
  this relation explicit prevents a proof from acquiring innermost semantics
  merely by changing the Q component of an ordinary DP problem.
\<close>

definition innermost_csstep ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_csstep \<mu> R = {(s,t). \<exists>p lr \<sigma>.
    (s,t) \<in> rstep_r_p_s R lr p \<sigma> \<and>
    csstep_cond \<mu> p s \<and>
    (\<forall>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<longrightarrow>
      u \<in> NF (csstep \<mu> R))}"

lemma af_regarded_pos_subst_prefix:
  assumes "p \<in> poss t"
  shows "af_regarded_pos \<mu> (t \<cdot> \<sigma>) p =
    af_regarded_pos \<mu> t p"
  using assms
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ss where t: "t = Fun f ss" and i: "i < length ss"
    and p: "p \<in> poss (ss ! i)" by (cases t, auto)
  from Cons show ?case unfolding t using i p by auto
qed

lemma af_regarded_pos_imp_mu_poss_local:
  assumes p: "p \<in> poss t"
    and active: "af_regarded_pos \<mu> t p"
  shows "p \<in> mu_poss \<mu> t"
  using p active
proof (induct p arbitrary: t)
  case Nil
  then show ?case by (cases t, auto)
next
  case (Cons i p)
  then obtain f ss where t: "t = Fun f ss" and i: "i < length ss"
    and active_i: "i \<in> \<mu> (f,length ss)"
    and p_pos: "p \<in> poss (ss ! i)"
    and active_p: "af_regarded_pos \<mu> (ss ! i) p"
    by (cases t, auto)
  from Cons.hyps[OF p_pos active_p] t i active_i
  show ?case by auto
qed

lemma af_regarded_pos_imp_csstep_cond_local:
  assumes pos: "p \<in> poss s" and active: "af_regarded_pos \<mu> s p"
  shows "csstep_cond \<mu> p s"
  using pos active
proof (induct p arbitrary: s)
  case Nil
  then show ?case unfolding csstep_cond_def by simp
next
  case (Cons i p)
  then obtain f ss where s: "s = Fun f ss"
    and i: "i < length ss" "i \<in> \<mu> (f,length ss)"
    and p: "p \<in> poss (ss ! i)"
    and active: "af_regarded_pos \<mu> (ss ! i) p"
    by (cases s, auto)
  from Cons.hyps[OF p active]
  have cond: "csstep_cond \<mu> p (ss ! i)" .
  show ?case unfolding s csstep_cond_def
  proof (intro allI impI)
    fix p1 j p2
    assume decomp: "i # p = p1 @ j # p2 \<and>
      i # p \<in> poss (Fun f ss)"
    show "\<exists>g us. Fun f ss |_ p1 = Fun g us \<and>
      j \<in> \<mu> (g,length us)"
    proof (cases p1)
      case Nil
      with decomp i show ?thesis by auto
    next
      case (Cons k q)
      with decomp have k: "k = i" and p_decomp: "p = q @ j # p2"
        and p_pos: "p \<in> poss (ss ! i)" using i by auto
      from cond[unfolded csstep_cond_def, rule_format, of q j p2]
        p_decomp p_pos
      obtain g us where sub: "ss ! i |_ q = Fun g us"
        and selected: "j \<in> \<mu> (g,length us)" by auto
      with Cons k i show ?thesis by auto
    qed
  qed
qed

lemma csr_switch_overlay_proper_lhs_instance_no_root:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and lr: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and tfun: "is_Fun t"
  shows "(t \<cdot> \<sigma>,u) \<notin> csrstep \<mu> R"
proof
  assume step: "(t \<cdot> \<sigma>,u) \<in> csrstep \<mu> R"
  then obtain lr' \<tau> where
    root': "(t \<cdot> \<sigma>,u) \<in> rstep_r_p_s R lr' [] \<tau>"
    unfolding csrstep_iff_rstep_root by blast
  obtain l' r' where lr'_eq: "lr' = (l',r')" by (cases lr', auto)
  have root: "(t \<cdot> \<sigma>,u) \<in> rstep_r_p_s R (l',r') [] \<tau>"
    using root' unfolding lr'_eq .
  from root have lr': "(l',r') \<in> R"
    and match: "t \<cdot> \<sigma> = l' \<cdot> \<tau>"
    unfolding rstep_r_p_s_def' by auto
  from mgu_vd_complete[OF match, of string_rename]
  obtain \<mu>1 \<mu>2 where
    mgu: "mgu_vd string_rename t l' = Some (\<mu>1,\<mu>2)"
    by auto
  from proper obtain D where lD: "l = D\<langle>t\<rangle>" and D_ne: "D \<noteq> \<box>"
    by auto
  have cp: "(False,
      (D \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>,
      r \<cdot> \<mu>1) \<in> critical_pairs string_rename R R"
    by (rule critical_pairsI[OF lr lr' lD tfun mgu refl refl],
        simp add: D_ne)
  from ortho cp show False
    unfolding csr_switch_overlay_def by blast
qed

lemma csr_switch_overlay_proper_lhs_instance_rstep:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and source: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and linear: "linear_term t"
    and step: "(t \<cdot> \<sigma>,u) \<in> rstep_r_p_s R lr' p \<rho>"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau>"
proof -
  from step have p_pos: "p \<in> poss (t \<cdot> \<sigma>)"
    and lr': "lr' \<in> R"
    and redex: "(t \<cdot> \<sigma>) |_ p = fst lr' \<cdot> \<rho>"
    and u: "u = replace_at (t \<cdot> \<sigma>) p (snd lr' \<cdot> \<rho>)"
    unfolding rstep_r_p_s_def' by auto
  from poss_subst_choice[OF p_pos]
  show ?thesis
  proof
    assume pattern: "p \<in> poss t \<and> is_Fun (t |_ p)"
    then have p_t: "p \<in> poss t" and p_fun: "is_Fun (t |_ p)"
      by auto
    have sub: "l \<rhd> t |_ p"
      by (rule supt_supteq_trans[OF proper subt_at_imp_supteq[OF p_t]])
    obtain l' r' where lr'_eq: "lr' = (l',r')" by (cases lr', auto)
    have root: "((t |_ p) \<cdot> \<sigma>,r' \<cdot> \<rho>)
        \<in> csrstep \<mu> R"
      unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
      using lr' redex p_t unfolding lr'_eq
      by (intro exI[of _ "(l',r')"] exI[of _ \<rho>], auto)
    from csr_switch_overlay_proper_lhs_instance_no_root[
      OF ortho source sub p_fun, of \<sigma> "r' \<cdot> \<rho>" \<mu>] root
    show ?thesis by contradiction
  next
    assume "\<exists>x q1 q2. q1 \<in> poss t \<and> q2 \<in> poss (\<sigma> x) \<and>
      t |_ q1 = Var x \<and> x \<in> vars_term t \<and> p = q1 @ q2 \<and>
      (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where
      q1: "q1 \<in> poss t" "t |_ q1 = Var x" "x \<in> vars_term t"
      and q2: "q2 \<in> poss (\<sigma> x)"
      and p: "p = q1 @ q2"
      by blast
    let ?v = "replace_at (\<sigma> x) q2 (snd lr' \<cdot> \<rho>)"
    let ?\<tau> = "\<sigma>(x := ?v)"
    have nested: "replace_at (t \<cdot> \<sigma>) p (snd lr' \<cdot> \<rho>) =
        replace_at (t \<cdot> \<sigma>) q1 ?v"
      unfolding p ctxt_of_pos_term_append[OF poss_imp_subst_poss[OF q1(1)]]
      using q1 q2 by simp
    have replaced: "replace_at (t \<cdot> \<sigma>) q1 ?v = t \<cdot> ?\<tau>"
      by (rule linear_term_replace_in_subst[OF linear q1(1) q1(2)], auto)
    have "u = t \<cdot> ?\<tau>" using u nested replaced by simp
    then show ?thesis by blast
  qed
qed

lemma csr_switch_overlay_proper_lhs_instance_innermost_steps:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and source: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and linear: "linear_term t"
    and steps: "(t \<cdot> \<sigma>,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau>"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  from step.hyps(2) obtain p lr' \<rho> where
    rw: "(y,z) \<in> rstep_r_p_s R lr' p \<rho>"
    unfolding innermost_csstep_def by blast
  from step.hyps(3) obtain \<tau> where y: "y = t \<cdot> \<tau>" by blast
  from csr_switch_overlay_proper_lhs_instance_rstep[
    OF ortho source proper linear rw[unfolded y]]
  show ?case .
qed

lemma csr_switch_overlay_proper_lhs_instance_innermost_step:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and source: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and linear: "linear_term t"
    and step: "(t \<cdot> \<sigma>,u) \<in> innermost_csstep \<mu> R"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau> \<and>
    (\<forall>x\<in>vars_term t. (\<sigma> x,\<tau> x) \<in>
      (innermost_csstep \<mu> R)\<^sup>*) \<and>
    (\<forall>x\<in>vars_term t - mu_vars_term \<mu> t. \<tau> x = \<sigma> x)"
proof -
  from step obtain p lr' \<rho> where
    rw: "(t \<cdot> \<sigma>,u) \<in> rstep_r_p_s R lr' p \<rho>"
    and cond: "csstep_cond \<mu> p (t \<cdot> \<sigma>)"
    and inner: "\<forall>w. mu_supt \<mu> (fst lr' \<cdot> \<rho>) w
      \<longrightarrow> w \<in> NF (csstep \<mu> R)"
    unfolding innermost_csstep_def by blast
  from rw have p_pos: "p \<in> poss (t \<cdot> \<sigma>)"
    and lr': "lr' \<in> R"
    and redex: "(t \<cdot> \<sigma>) |_ p = fst lr' \<cdot> \<rho>"
    and u: "u = replace_at (t \<cdot> \<sigma>) p (snd lr' \<cdot> \<rho>)"
    unfolding rstep_r_p_s_def' by auto
  from poss_subst_choice[OF p_pos]
  show ?thesis
  proof
    assume pattern: "p \<in> poss t \<and> is_Fun (t |_ p)"
    then have p_t: "p \<in> poss t" and p_fun: "is_Fun (t |_ p)"
      by auto
    have sub: "l \<rhd> t |_ p"
      by (rule supt_supteq_trans[OF proper subt_at_imp_supteq[OF p_t]])
    obtain l' r' where lr'_eq: "lr' = (l',r')" by (cases lr', auto)
    have root: "((t |_ p) \<cdot> \<sigma>,r' \<cdot> \<rho>)
        \<in> csrstep \<mu> R"
      unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
      using lr' redex p_t unfolding lr'_eq
      by (intro exI[of _ "(l',r')"] exI[of _ \<rho>], auto)
    from csr_switch_overlay_proper_lhs_instance_no_root[
      OF ortho source sub p_fun, of \<sigma> "r' \<cdot> \<rho>" \<mu>] root
    show ?thesis by contradiction
  next
    assume "\<exists>x q1 q2. q1 \<in> poss t \<and> q2 \<in> poss (\<sigma> x) \<and>
      t |_ q1 = Var x \<and> x \<in> vars_term t \<and> p = q1 @ q2 \<and>
      (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where
      q1: "q1 \<in> poss t" "t |_ q1 = Var x" "x \<in> vars_term t"
      and q2: "q2 \<in> poss (\<sigma> x)"
      and p: "p = q1 @ q2"
      by blast
    let ?v = "replace_at (\<sigma> x) q2 (snd lr' \<cdot> \<rho>)"
    let ?\<tau> = "\<sigma>(x := ?v)"
    have local_rw: "(\<sigma> x,?v) \<in> rstep_r_p_s R lr' q2 \<rho>"
      unfolding rstep_r_p_s_def'
      using lr' redex q1 q2 unfolding p
      by (auto simp: subt_at_append)
    have active_p: "af_regarded_pos \<mu> (t \<cdot> \<sigma>) p"
      by (rule csstep_cond_imp_af_regarded_pos[OF cond p_pos])
    have local_active: "af_regarded_pos \<mu> (\<sigma> x) q2"
      using active_p q1 unfolding p af_regarded_pos_append by simp
    have active_q1_subst: "af_regarded_pos \<mu> (t \<cdot> \<sigma>) q1"
      using active_p unfolding p af_regarded_pos_append by blast
    have active_q1: "af_regarded_pos \<mu> t q1"
      using active_q1_subst
      unfolding af_regarded_pos_subst_prefix[OF q1(1)] .
    have q1_mu: "q1 \<in> mu_poss \<mu> t"
      by (rule af_regarded_pos_imp_mu_poss_local[OF q1(1) active_q1])
    have x_active: "x \<in> mu_vars_term \<mu> t"
      using q1_mu q1(2) unfolding mu_vars_term_def by blast
    have local_cond: "csstep_cond \<mu> q2 (\<sigma> x)"
      by (rule af_regarded_pos_imp_csstep_cond_local[OF q2 local_active])
    have local_step: "(\<sigma> x,?v) \<in> innermost_csstep \<mu> R"
      unfolding innermost_csstep_def using local_rw local_cond inner by blast
    have nested: "replace_at (t \<cdot> \<sigma>) p (snd lr' \<cdot> \<rho>) =
        replace_at (t \<cdot> \<sigma>) q1 ?v"
      unfolding p ctxt_of_pos_term_append[OF poss_imp_subst_poss[OF q1(1)]]
      using q1 q2 by simp
    have replaced: "replace_at (t \<cdot> \<sigma>) q1 ?v = t \<cdot> ?\<tau>"
      by (rule linear_term_replace_in_subst[OF linear q1(1) q1(2)], auto)
    have vars: "\<forall>y\<in>vars_term t. (\<sigma> y,?\<tau> y) \<in>
        (innermost_csstep \<mu> R)\<^sup>*"
    proof (intro ballI)
      fix y
      assume "y \<in> vars_term t"
      show "(\<sigma> y,?\<tau> y) \<in> (innermost_csstep \<mu> R)\<^sup>*"
      proof (cases "y = x")
        case True
        with local_step show ?thesis by simp
      next
        case False
        then show ?thesis by simp
      qed
    qed
    have inactive: "\<forall>y\<in>vars_term t - mu_vars_term \<mu> t.
        ?\<tau> y = \<sigma> y"
      using x_active by auto
    have result: "u = t \<cdot> ?\<tau>" using u nested replaced by simp
    show ?thesis
      by (rule exI[of _ ?\<tau>], use result vars inactive in auto)
  qed
qed

lemma csr_switch_overlay_proper_lhs_instance_innermost_steps_vars:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and source: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and linear: "linear_term t"
    and steps: "(t \<cdot> \<sigma>,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau> \<and>
    (\<forall>x\<in>vars_term t. (\<sigma> x,\<tau> x) \<in>
      (innermost_csstep \<mu> R)\<^sup>*) \<and>
    (\<forall>x\<in>vars_term t - mu_vars_term \<mu> t. \<tau> x = \<sigma> x)"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  from step.hyps(3) obtain \<tau> where y: "y = t \<cdot> \<tau>"
    and old: "\<forall>x\<in>vars_term t. (\<sigma> x,\<tau> x) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    and old_inactive: "\<forall>x\<in>vars_term t - mu_vars_term \<mu> t.
      \<tau> x = \<sigma> x"
    by blast
  from csr_switch_overlay_proper_lhs_instance_innermost_step[
    OF ortho source proper linear step.hyps(2)[unfolded y]]
  obtain \<delta> where z: "z = t \<cdot> \<delta>"
    and new: "\<forall>x\<in>vars_term t. (\<tau> x,\<delta> x) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    and new_inactive: "\<forall>x\<in>vars_term t - mu_vars_term \<mu> t.
      \<delta> x = \<tau> x"
    by blast
  have composed: "\<forall>x\<in>vars_term t. (\<sigma> x,\<delta> x) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    using old new by (meson rtrancl_trans)
  have inactive: "\<forall>x\<in>vars_term t - mu_vars_term \<mu> t.
      \<delta> x = \<sigma> x"
    using old_inactive new_inactive by auto
  show ?case using z composed inactive by blast
qed

lemma innermost_csstep_subset_csstep:
  "innermost_csstep \<mu> R \<subseteq> csstep \<mu> R"
  unfolding innermost_csstep_def csstep_def csstep_p_def by auto

lemma SN_csstep_imp_SN_innermost_csstep:
  assumes "SN (csstep \<mu> R)"
  shows "SN (innermost_csstep \<mu> R)"
  by (rule SN_subset[OF assms innermost_csstep_subset_csstep])

lemma csstep_cond_Cons_FunI:
  assumes i: "i < length ss" "i \<in> \<mu> (f, length ss)"
    and cond: "csstep_cond \<mu> p (ss ! i)"
  shows "csstep_cond \<mu> (i # p) (Fun f ss)"
  unfolding csstep_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume decomp: "i # p = p1 @ j # p2 \<and> i # p \<in> poss (Fun f ss)"
  show "\<exists>g us. Fun f ss |_ p1 = Fun g us \<and>
    j \<in> \<mu> (g, length us)"
  proof (cases p1)
    case Nil
    with decomp i show ?thesis by auto
  next
    case (Cons k q)
    with decomp have k: "k = i" and p_decomp: "p = q @ j # p2"
      and p_pos: "p \<in> poss (ss ! i)"
      using i by auto
    from cond[unfolded csstep_cond_def, rule_format, of q j p2]
      p_decomp p_pos
    obtain g us where sub: "ss ! i |_ q = Fun g us"
      and active: "j \<in> \<mu> (g, length us)"
      by auto
    with Cons k i show ?thesis by auto
  qed
qed

lemma csstep_active_argI:
  assumes i: "i < length ss" "i \<in> \<mu> (f, length ss)"
    and step: "(ss ! i, u) \<in> csstep \<mu> R"
  shows "(Fun f ss, Fun f (ss[i := u])) \<in> csstep \<mu> R"
proof -
  from step obtain p lr \<sigma> where
    rw: "(ss ! i, u) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (ss ! i)"
    unfolding csstep_def csstep_p_def by auto
  have rw': "(Fun f ss, Fun f (ss[i := u])) \<in>
      rstep_r_p_s R lr (i # p) \<sigma>"
    using rw i unfolding rstep_r_p_s_def'
    by (auto simp: upd_conv_take_nth_drop)
  have cond': "csstep_cond \<mu> (i # p) (Fun f ss)"
    by (rule csstep_cond_Cons_FunI[OF i cond])
  show ?thesis
    unfolding csstep_def csstep_p_def
    using rw' cond' by blast
qed

lemma innermost_csstep_active_argI:
  assumes i: "i < length ss" "i \<in> \<mu> (f, length ss)"
    and step: "(ss ! i, u) \<in> innermost_csstep \<mu> R"
  shows "(Fun f ss, Fun f (ss[i := u])) \<in> innermost_csstep \<mu> R"
proof -
  from step obtain p lr \<sigma> where
    rw: "(ss ! i, u) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (ss ! i)"
    and inner: "\<forall>v. mu_supt \<mu> (fst lr \<cdot> \<sigma>) v \<longrightarrow>
      v \<in> NF (csstep \<mu> R)"
    unfolding innermost_csstep_def by auto
  have rw': "(Fun f ss, Fun f (ss[i := u])) \<in>
      rstep_r_p_s R lr (i # p) \<sigma>"
    using rw i unfolding rstep_r_p_s_def'
    by (auto simp: upd_conv_take_nth_drop)
  have cond': "csstep_cond \<mu> (i # p) (Fun f ss)"
    by (rule csstep_cond_Cons_FunI[OF i cond])
  show ?thesis
    unfolding innermost_csstep_def
    using rw' cond' inner by blast
qed

lemma innermost_cssteps_active_argI:
  assumes i: "i < length ss" "i \<in> \<mu> (f, length ss)"
    and steps: "(ss ! i,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
  shows "(Fun f ss, Fun f (ss[i := u])) \<in>
    (innermost_csstep \<mu> R)\<^sup>*"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case using i by simp
next
  case (step y z)
  have len: "length (ss[i := y]) = length ss" by simp
  have nth: "(ss[i := y]) ! i = y" using i by simp
  have lifted: "(Fun f (ss[i := y]), Fun f ((ss[i := y])[i := z]))
      \<in> innermost_csstep \<mu> R"
    by (rule innermost_csstep_active_argI,
        use i len nth step.hyps(2) in auto)
  have updates: "(ss[i := y])[i := z] = ss[i := z]"
    using i by simp
  from step.hyps(3) lifted show ?case
    unfolding updates by auto
qed

lemma innermost_cssteps_active_argsI:
  assumes len: "length us = length ss"
    and active: "\<And>i. i < length ss \<Longrightarrow>
      i \<in> \<mu> (f, length ss) \<Longrightarrow>
      (ss ! i,us ! i) \<in> (innermost_csstep \<mu> R)\<^sup>*"
    and inactive: "\<And>i. i < length ss \<Longrightarrow>
      i \<notin> \<mu> (f, length ss) \<Longrightarrow> us ! i = ss ! i"
  shows "(Fun f ss,Fun f us) \<in> (innermost_csstep \<mu> R)\<^sup>*"
proof -
  have prefix: "n \<le> length ss \<Longrightarrow>
      (Fun f ss,Fun f (take n us @ drop n ss)) \<in>
        (innermost_csstep \<mu> R)\<^sup>*" for n
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then have n: "n < length ss" by simp
    let ?vs = "take n us @ drop n ss"
    let ?ws = "take (Suc n) us @ drop (Suc n) ss"
    have lens: "length ?vs = length ss"
      using len n by simp
    have nth: "?vs ! n = ss ! n"
      using n len by (simp add: nth_append)
    have update: "?vs[n := us ! n] = ?ws"
      using n len
      by (subst upd_conv_take_nth_drop,
          simp_all add: take_Suc_conv_app_nth)
    show ?case
    proof (cases "n \<in> \<mu> (f,length ss)")
      case True
      from active[OF n True] have local:
        "(?vs ! n,us ! n) \<in> (innermost_csstep \<mu> R)\<^sup>*"
        unfolding nth .
      have n_vs: "n < length ?vs" using n lens by simp
      have active_vs: "n \<in> \<mu> (f,length ?vs)"
        using True lens by simp
      from innermost_cssteps_active_argI[OF n_vs active_vs local]
      have "(Fun f ?vs,Fun f (?vs[n := us ! n])) \<in>
          (innermost_csstep \<mu> R)\<^sup>*"
        by simp
      with Suc.hyps Suc.prems show ?thesis
        unfolding update by auto
    next
      case False
      have nth_value: "us ! n = ?vs ! n"
        using inactive[OF n False] nth by simp
      have same_update: "?vs[n := us ! n] = ?vs"
        using n lens nth_value by simp
      have eq: "?vs = ?ws"
        using update same_update by simp
      with Suc.hyps Suc.prems show ?thesis by simp
    qed
  qed
  from prefix[of "length ss"] show ?thesis
    using len by simp
qed

lemma innermost_csstep_mu_pos_lift:
  assumes p: "p \<in> mu_poss \<mu> t"
    and step: "(t |_ p,u) \<in> innermost_csstep \<mu> R"
  shows "(t,replace_at t p u) \<in> innermost_csstep \<mu> R"
  using p step
proof (induct t arbitrary: p u)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    with Fun show ?thesis by simp
  next
    case (Cons i q)
    from Fun.prems Cons have i: "i < length ss"
      and active: "i \<in> \<mu> (f,length ss)"
      and q: "q \<in> mu_poss \<mu> (ss ! i)"
      and local: "(ss ! i |_ q,u) \<in> innermost_csstep \<mu> R"
      by auto
    from Fun.hyps[OF nth_mem[OF i] q local]
    have lifted: "(ss ! i,replace_at (ss ! i) q u) \<in>
        innermost_csstep \<mu> R" .
    have outer: "(Fun f ss,
        Fun f (ss[i := replace_at (ss ! i) q u])) \<in>
        innermost_csstep \<mu> R"
      by (rule innermost_csstep_active_argI[OF i active lifted])
    have target: "replace_at (Fun f ss) (i # q) u =
        Fun f (ss[i := replace_at (ss ! i) q u])"
      using i q by (simp add: upd_conv_take_nth_drop)
    show ?thesis unfolding Cons target using outer .
  qed
qed

lemma SN_on_innermost_csstep_mu_pos:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_poss \<mu> t"
    and SN: "SN_on (innermost_csstep \<mu> R) {t}"
  shows "SN_on (innermost_csstep \<mu> R) {t |_ p}"
proof (rule ccontr)
  assume not_SN: "\<not> SN_on (innermost_csstep \<mu> R) {t |_ p}"
  then obtain f where f0: "f 0 = t |_ p"
    and chain: "\<And>i. (f i,f (Suc i)) \<in> innermost_csstep \<mu> R"
    unfolding SN_on_def by auto
  define g where "g i = replace_at t p (f i)" for i
  have p_pos: "p \<in> poss t" using p mu_poss_imp_poss by blast
  have g0: "g 0 = t"
    unfolding g_def f0 by (rule replace_at_ident[OF p_pos refl])
  have gstep: "(g i,g (Suc i)) \<in> innermost_csstep \<mu> R" for i
  proof -
    have f_fun: "is_Fun (f i)"
    proof (cases "f i")
      case (Var x)
      from chain[of i] innermost_csstep_subset_csstep
      have "(Var x,f (Suc i)) \<in> csstep \<mu> R"
        unfolding Var by blast
      with csstep_Var_empty_wf[OF wf, of x "f (Suc i)" \<mu>]
      show ?thesis by blast
    next
      case (Fun f ss)
      then show ?thesis by simp
    qed
    have p_mu: "p \<in> mu_poss \<mu> (g i)"
      unfolding g_def
      by (rule mu_poss_replace_at_below[OF p _ p_pos], auto simp: f_fun)
    have sub: "g i |_ p = f i"
      unfolding g_def by (rule replace_at_subt_at[OF p_pos])
    have "(g i,replace_at (g i) p (f (Suc i))) \<in>
        innermost_csstep \<mu> R"
      by (rule innermost_csstep_mu_pos_lift[OF p_mu],
          unfold sub, rule chain)
    moreover have "replace_at (g i) p (f (Suc i)) = g (Suc i)"
      unfolding g_def by (rule replace_at_overwrite[OF p_pos])
    ultimately show ?thesis by simp
  qed
  from SN[unfolded SN_on_def] g0 gstep show False by blast
qed

lemma terminating_or_mu_Tinf_active_arg_SN:
  assumes wf: "wf_trs R"
    and i: "i < length ss" "i \<in> \<mu> (f,length ss)"
    and redex: "SN_on (csstep \<mu> R) {Fun f ss} \<or>
      Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "SN_on (csstep \<mu> R) {ss ! i}"
proof (rule disjE[OF redex])
  assume SN: "SN_on (csstep \<mu> R) {Fun f ss}"
  have root_pos: "[] \<in> mu_poss \<mu> (ss ! i)"
    by (cases "ss ! i", auto)
  have pos: "[i] \<in> mu_poss \<mu> (Fun f ss)"
    using i root_pos by auto
  from SN_on_mu_pos[OF wf pos SN] show ?thesis
    using i by simp
next
  assume T: "Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  have root_pos: "[] \<in> mu_poss \<mu> (ss ! i)"
    by (cases "ss ! i", auto)
  have proper: "mu_supt \<mu> (Fun f ss) (ss ! i)"
    unfolding mu_supt_def
    by (intro exI[of _ i] exI[of _ "[]"], use i root_pos in auto)
  from T proper show ?thesis
    unfolding mu_Tinf_def by blast
qed

lemma csstep_at_mu_posI:
  assumes pos: "p \<in> mu_poss \<mu> s"
    and step: "(s |_ p, u) \<in> csstep \<mu> R"
  shows "(s, replace_at s p u) \<in> csstep \<mu> R"
  using pos step
proof (induct s arbitrary: p u)
  case (Var x)
  then have "p = []" by auto
  with Var show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    with Fun.prems show ?thesis by simp
  next
    case (Cons i q)
    from Fun.prems(1)[unfolded Cons]
    have i: "i < length ss" "i \<in> \<mu> (f, length ss)"
      and q: "q \<in> mu_poss \<mu> (ss ! i)"
      by auto
    from Fun.prems(2)[unfolded Cons] i
    have substep: "(ss ! i |_ q, u) \<in> csstep \<mu> R"
      by simp
    from Fun.hyps[OF nth_mem[OF i(1)] q substep]
    have argstep: "(ss ! i, replace_at (ss ! i) q u) \<in> csstep \<mu> R" .
    from csstep_active_argI[OF i argstep] Cons i
    show ?thesis by (simp add: upd_conv_take_nth_drop)
  qed
qed

lemma NF_csstep_mu_pos:
  assumes NF: "s \<in> NF (csstep \<mu> R)"
    and pos: "p \<in> mu_poss \<mu> s"
  shows "s |_ p \<in> NF (csstep \<mu> R)"
  unfolding NF_iff_no_step
proof (intro allI notI)
  fix u
  assume step: "(s |_ p, u) \<in> csstep \<mu> R"
  from csstep_at_mu_posI[OF pos step]
  show False using NF unfolding NF_iff_no_step by blast
qed

lemma af_regarded_pos_imp_csstep_cond:
  assumes pos: "p \<in> poss s" and active: "af_regarded_pos \<mu> s p"
  shows "csstep_cond \<mu> p s"
  using pos active
proof (induct p arbitrary: s)
  case Nil
  then show ?case unfolding csstep_cond_def by simp
next
  case (Cons i p)
  then obtain f ss where s: "s = Fun f ss"
    and i: "i < length ss" "i \<in> \<mu> (f, length ss)"
    and p: "p \<in> poss (ss ! i)"
    and active: "af_regarded_pos \<mu> (ss ! i) p"
    by (cases s, auto)
  from Cons.hyps[OF p active]
  have "csstep_cond \<mu> p (ss ! i)" .
  from csstep_cond_Cons_FunI[OF i this]
  show ?case unfolding s .
qed

lemma csstep_cond_iff_af_regarded_pos:
  assumes "p \<in> poss s"
  shows "csstep_cond \<mu> p s \<longleftrightarrow> af_regarded_pos \<mu> s p"
  using assms csstep_cond_imp_af_regarded_pos
    af_regarded_pos_imp_csstep_cond by blast

lemma af_regarded_pos_imp_mu_poss:
  assumes pos: "p \<in> poss s" and active: "af_regarded_pos \<mu> s p"
  shows "p \<in> mu_poss \<mu> s"
  using pos active
proof (induct p arbitrary: s)
  case Nil
  then show ?case by (cases s, auto)
next
  case (Cons i p)
  then show ?case
    by (cases s, auto simp: nth_mem)
qed

lemma af_regarded_pos_parallel_replace_at:
  fixes p q :: pos
  assumes par: "p \<bottom> q" and p: "p \<in> poss s" and q: "q \<in> poss s"
    and active: "af_regarded_pos \<mu> s q"
  shows "af_regarded_pos \<mu> (replace_at s p u) q"
  using assms
proof (induct s arbitrary: p q)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ss)
  from Fun.prems(1) have p_ne: "p \<noteq> []" and q_ne: "q \<noteq> []"
    by (cases p; cases q; auto)+
  from p_ne q_ne obtain i p' j q' where
    p_eq: "p = i # p'" and q_eq: "q = j # q'"
    by (cases p; cases q; auto)
  from Fun.prems(2,3)[unfolded p_eq q_eq]
  have i: "i < length ss" and j: "j < length ss"
    and p': "p' \<in> poss (ss ! i)" and q': "q' \<in> poss (ss ! j)"
    by auto
  from Fun.prems(4)[unfolded q_eq]
  have j_active: "j \<in> \<mu> (f, length ss)"
    and q_active: "af_regarded_pos \<mu> (ss ! j) q'"
    by auto
  have repl: "replace_at (Fun f ss) p u =
      Fun f (ss[i := replace_at (ss ! i) p' u])"
    unfolding p_eq using i by (simp add: upd_conv_take_nth_drop)
  show ?case
  proof (cases "i = j")
    case False
    with i j q_eq j_active q_active
    show ?thesis unfolding repl by simp
  next
    case True
    from Fun.prems(1)[unfolded p_eq q_eq True]
    have par': "p' \<bottom> q'" by simp
    have q_i: "q' \<in> poss (ss ! i)" using q' True by simp
    have q_active_i: "af_regarded_pos \<mu> (ss ! i) q'"
      using q_active True by simp
    from Fun.hyps[OF nth_mem[OF i] par' p' q_i q_active_i]
    have rec: "af_regarded_pos \<mu>
      (replace_at (ss ! i) p' u) q'" .
    from i q_eq True j_active rec
    show ?thesis unfolding repl by simp
  qed
qed

lemma csstep_cond_parallel_replace_at:
  fixes p q :: pos
  assumes par: "p \<bottom> q" and p: "p \<in> poss s" and q: "q \<in> poss s"
    and cond: "csstep_cond \<mu> q s"
  shows "csstep_cond \<mu> q (replace_at s p u)"
proof -
  have q_new: "q \<in> poss (replace_at s p u)"
    using parallel_poss_replace_at[OF par p, of u] q by simp
  have active: "af_regarded_pos \<mu> s q"
    by (rule csstep_cond_imp_af_regarded_pos[OF cond q])
  from af_regarded_pos_parallel_replace_at[OF par p q active]
  show ?thesis
    by (rule af_regarded_pos_imp_csstep_cond[OF q_new])
qed

lemma csr_switch_overlay_same_position:
  fixes R :: "('f, string) trs" and p :: pos
  assumes ortho: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and one: "(s,t) \<in> rstep_r_p_s R (l1,r1) p \<sigma>1"
    and two: "(s,u) \<in> rstep_r_p_s R (l2,r2) p \<sigma>2"
  shows "t = u"
proof -
  from one have lr1: "(l1,r1) \<in> R" and p: "p \<in> poss s"
    and lhs1: "s |_ p = l1 \<cdot> \<sigma>1"
    and t: "t = replace_at s p (r1 \<cdot> \<sigma>1)"
    unfolding rstep_r_p_s_def' by auto
  from two have lr2: "(l2,r2) \<in> R"
    and lhs2: "s |_ p = l2 \<cdot> \<sigma>2"
    and u: "u = replace_at s p (r2 \<cdot> \<sigma>2)"
    unfolding rstep_r_p_s_def' by auto
  from lhs1 lhs2 have ident: "l1 \<cdot> \<sigma>1 = l2 \<cdot> \<sigma>2"
    by simp
  from mgu_vd_complete[OF ident, of string_rename]
  obtain \<mu>1 \<mu>2 \<rho> where
    mgu: "mgu_vd string_rename l1 l2 = Some (\<mu>1,\<mu>2)"
    and s1: "\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<rho>"
    and s2: "\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<rho>"
    by blast
  from lr1 wf have fun_l1: "is_Fun l1"
    unfolding wf_trs_def
    by (cases l1, auto)
  have cp: "(True, r2 \<cdot> \<mu>2, r1 \<cdot> \<mu>1) \<in>
      critical_pairs string_rename R R"
    by (rule critical_pairsI[OF lr1 lr2 _ fun_l1 mgu, of \<box>], auto)
  from ortho cp have rhs: "r2 \<cdot> \<mu>2 = r1 \<cdot> \<mu>1"
    unfolding csr_switch_overlay_def by blast
  have "r1 \<cdot> \<sigma>1 = r2 \<cdot> \<sigma>2"
    unfolding s1 s2 using rhs by simp
  then show ?thesis unfolding t u by simp
qed

lemma innermost_csstep_no_strict_nested:
  fixes p q :: pos
  assumes one_at: "(s,t) \<in> rstep_r_p_s R lr1 p \<sigma>1"
    and two_at: "(s,u) \<in> rstep_r_p_s R lr2 q \<sigma>2"
    and cond1: "csstep_cond \<mu> p s"
    and inner1: "\<forall>v. mu_supt \<mu> (fst lr1 \<cdot> \<sigma>1) v \<longrightarrow>
      v \<in> NF (csstep \<mu> R)"
    and cond2: "csstep_cond \<mu> q s"
    and below: "p <\<^sub>p q"
  shows False
proof -
  from below obtain d where q: "q = p @ d" and d_ne: "d \<noteq> []"
    unfolding less_pos_def' by blast
  from one_at have p_pos: "p \<in> poss s"
    and at_p: "s |_ p = fst lr1 \<cdot> \<sigma>1"
    unfolding rstep_r_p_s_def' by auto
  from two_at have q_pos: "q \<in> poss s"
    and at_q: "s |_ q = fst lr2 \<cdot> \<sigma>2"
    and lr2: "lr2 \<in> R"
    unfolding rstep_r_p_s_def' by auto
  have active_q: "af_regarded_pos \<mu> s q"
    by (rule csstep_cond_imp_af_regarded_pos[OF cond2 q_pos])
  from active_q[unfolded q af_regarded_pos_append]
  have active_d: "af_regarded_pos \<mu> (s |_ p) d" by blast
  have d_pos: "d \<in> poss (s |_ p)"
    using q_pos unfolding q by simp
  have d_mu: "d \<in> mu_poss \<mu> (fst lr1 \<cdot> \<sigma>1)"
    using af_regarded_pos_imp_mu_poss[OF d_pos active_d]
    unfolding at_p .
  have redex: "(fst lr1 \<cdot> \<sigma>1) |_ d = fst lr2 \<cdot> \<sigma>2"
  proof -
    have "(s |_ p) |_ d = fst lr2 \<cdot> \<sigma>2"
      using at_q q p_pos by (simp add: subt_at_append)
    then show ?thesis using at_p by simp
  qed
  have proper: "mu_supt \<mu> (fst lr1 \<cdot> \<sigma>1)
      (fst lr2 \<cdot> \<sigma>2)"
    using d_mu d_ne redex unfolding mu_supt_def
    by (cases d, auto)
  have nf: "fst lr2 \<cdot> \<sigma>2 \<in> NF (csstep \<mu> R)"
    by (rule inner1[rule_format, OF proper])
  have root: "(fst lr2 \<cdot> \<sigma>2, snd lr2 \<cdot> \<sigma>2)
      \<in> csrstep \<mu> R"
    unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
    using lr2 by (intro exI[of _ lr2] exI[of _ \<sigma>2], auto)
  have "(fst lr2 \<cdot> \<sigma>2, snd lr2 \<cdot> \<sigma>2)
      \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by blast
  with nf show False unfolding NF_iff_no_step by blast
qed

lemma innermost_csstep_parallel_residual:
  fixes p q :: pos
  assumes one_at: "(s,t) \<in> rstep_r_p_s R lr1 p \<sigma>1"
    and two_at: "(s,u) \<in> rstep_r_p_s R lr2 q \<sigma>2"
    and p_cond: "csstep_cond \<mu> p s"
    and p_inner: "\<forall>w. mu_supt \<mu> (fst lr1 \<cdot> \<sigma>1) w
      \<longrightarrow> w \<in> NF (csstep \<mu> R)"
    and q_cond: "csstep_cond \<mu> q s"
    and q_inner: "\<forall>w. mu_supt \<mu> (fst lr2 \<cdot> \<sigma>2) w
      \<longrightarrow> w \<in> NF (csstep \<mu> R)"
    and par: "p \<bottom> q"
  shows "\<exists>v. (t,v) \<in> innermost_csstep \<mu> R \<and>
    (u,v) \<in> innermost_csstep \<mu> R"
proof -
  obtain l1 r1 where lr1: "lr1 = (l1,r1)" by (cases lr1, auto)
  obtain l2 r2 where lr2: "lr2 = (l2,r2)" by (cases lr2, auto)
  let ?v = "(ctxt_of_pos_term p u)\<langle>r1 \<cdot> \<sigma>1\<rangle>"
  from parallel_steps[OF one_at[unfolded lr1] two_at[unfolded lr2] par]
  have t_v: "(t,?v) \<in> rstep_r_p_s R lr2 q \<sigma>2"
    and u_v: "(u,?v) \<in> rstep_r_p_s R lr1 p \<sigma>1"
    unfolding lr1 lr2 by auto
  from one_at have p_pos: "p \<in> poss s"
    and t: "t = replace_at s p (snd lr1 \<cdot> \<sigma>1)"
    unfolding rstep_r_p_s_def' by auto
  from two_at have q_pos: "q \<in> poss s"
    and u: "u = replace_at s q (snd lr2 \<cdot> \<sigma>2)"
    unfolding rstep_r_p_s_def' by auto
  have q_cond_t: "csstep_cond \<mu> q t"
    unfolding t by (rule csstep_cond_parallel_replace_at[OF par p_pos q_pos q_cond])
  have p_cond_u: "csstep_cond \<mu> p u"
    unfolding u
    by (rule csstep_cond_parallel_replace_at[OF parallel_pos_sym[OF par]
          q_pos p_pos p_cond])
  have tv_inner: "(t,?v) \<in> innermost_csstep \<mu> R"
    unfolding innermost_csstep_def using t_v q_cond_t q_inner by blast
  have uv_inner: "(u,?v) \<in> innermost_csstep \<mu> R"
    unfolding innermost_csstep_def using u_v p_cond_u p_inner by blast
  show ?thesis using tv_inner uv_inner by blast
qed

lemma csr_switch_overlay_innermost_csstep_weak_diamond:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
  shows "w\<diamond> (innermost_csstep \<mu> R)"
  unfolding weak_diamond_def
proof
  fix t u
  assume peak: "(t,u) \<in> (innermost_csstep \<mu> R)\<inverse> O
      innermost_csstep \<mu> R - Id"
  then obtain s where st: "(s,t) \<in> innermost_csstep \<mu> R"
    and su: "(s,u) \<in> innermost_csstep \<mu> R"
    and ne: "t \<noteq> u" by auto
  from st obtain p lr1 \<sigma>1 where
    one_at: "(s,t) \<in> rstep_r_p_s R lr1 p \<sigma>1"
    and p_cond: "csstep_cond \<mu> p s"
    and p_inner: "\<forall>w. mu_supt \<mu> (fst lr1 \<cdot> \<sigma>1) w
      \<longrightarrow> w \<in> NF (csstep \<mu> R)"
    unfolding innermost_csstep_def by blast
  from su obtain q lr2 \<sigma>2 where
    two_at: "(s,u) \<in> rstep_r_p_s R lr2 q \<sigma>2"
    and q_cond: "csstep_cond \<mu> q s"
    and q_inner: "\<forall>w. mu_supt \<mu> (fst lr2 \<cdot> \<sigma>2) w
      \<longrightarrow> w \<in> NF (csstep \<mu> R)"
    unfolding innermost_csstep_def by blast
  show "(t,u) \<in> innermost_csstep \<mu> R O
      (innermost_csstep \<mu> R)\<inverse>"
  proof (cases "p = q")
    case True
    obtain l1 r1 where lr1: "lr1 = (l1,r1)" by (cases lr1, auto)
    obtain l2 r2 where lr2: "lr2 = (l2,r2)" by (cases lr2, auto)
    have two_at_p: "(s,u) \<in> rstep_r_p_s R (l2,r2) p \<sigma>2"
      using two_at True unfolding lr2 by simp
    from csr_switch_overlay_same_position[OF ortho wf
        one_at[unfolded lr1] two_at_p] ne
    show ?thesis by contradiction
  next
    case False
    from pos_cases[of p q] False
    consider (p_below) "p <\<^sub>p q" | (q_below) "q <\<^sub>p p" |
      (parallel) "p \<bottom> q"
      by (auto simp: prefix_order.le_less)
    then show ?thesis
    proof cases
      case p_below
      from innermost_csstep_no_strict_nested[OF one_at two_at p_cond
          p_inner q_cond p_below]
      show ?thesis by blast
    next
      case q_below
      from innermost_csstep_no_strict_nested[OF two_at one_at q_cond
          q_inner p_cond q_below]
      show ?thesis by blast
    next
      case parallel
      from innermost_csstep_parallel_residual[OF one_at two_at p_cond p_inner
          q_cond q_inner parallel]
      show ?thesis by auto
    qed
  qed
qed

theorem csr_switch_overlay_innermost_csstep_CR:
  fixes R :: "('f, string) trs"
  assumes "csr_switch_overlay R" "wf_trs R"
  shows "CR (innermost_csstep \<mu> R)"
  by (rule weak_diamond_imp_CR[OF
        csr_switch_overlay_innermost_csstep_weak_diamond[OF assms]])

lemma mu_supt_FunE:
  assumes "mu_supt \<mu> (Fun f ss) u"
  obtains i q where "i < length ss" "i \<in> \<mu> (f, length ss)"
    "q \<in> mu_poss \<mu> (ss ! i)" "u = ss ! i |_ q"
  using assms unfolding mu_supt_def by auto

lemma csrstep_active_args_NF_imp_innermost:
  assumes root: "(Fun f ss, t) \<in> csrstep \<mu> R"
    and args_NF: "\<And>i. i < length ss \<Longrightarrow>
      i \<in> \<mu> (f, length ss) \<Longrightarrow>
      ss ! i \<in> NF (csstep \<mu> R)"
  shows "(Fun f ss, t) \<in> innermost_csstep \<mu> R"
proof -
  from root obtain lr \<sigma> where
    rw: "(Fun f ss, t) \<in> rstep_r_p_s R lr [] \<sigma>"
    unfolding csrstep_iff_rstep_root by blast
  from rw have source: "fst lr \<cdot> \<sigma> = Fun f ss"
    unfolding rstep_r_p_s_def' by auto
  have inner: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
  proof -
    fix u
    assume "mu_supt \<mu> (fst lr \<cdot> \<sigma>) u"
    then have "mu_supt \<mu> (Fun f ss) u"
      unfolding source .
    then obtain i q where i: "i < length ss" "i \<in> \<mu> (f, length ss)"
      and q: "q \<in> mu_poss \<mu> (ss ! i)" and u: "u = ss ! i |_ q"
      by (elim mu_supt_FunE)
    from NF_csstep_mu_pos[OF args_NF[OF i] q]
    show "u \<in> NF (csstep \<mu> R)"
      unfolding u .
  qed
  show ?thesis
    using rw inner
    by (cases lr, auto simp: innermost_csstep_def csstep_cond_def)
qed

lemma csstep_imp_innermost_csstep_exists:
  assumes wf: "wf_trs R" and step: "(s, t) \<in> csstep \<mu> R"
  shows "\<exists>u. (s, u) \<in> innermost_csstep \<mu> R"
  using step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems
  show ?case by contradiction
next
  case (Fun f ss)
  show ?case
  proof (cases "\<exists>i<length ss. i \<in> \<mu> (f, length ss) \<and>
      ss ! i \<notin> NF (csstep \<mu> R)")
    case True
    then obtain i where i: "i < length ss" "i \<in> \<mu> (f, length ss)"
      and not_NF: "ss ! i \<notin> NF (csstep \<mu> R)"
      by blast
    from not_NF obtain v where substep: "(ss ! i, v) \<in> csstep \<mu> R"
      unfolding NF_iff_no_step by blast
    from Fun.hyps[OF nth_mem[OF i(1)], of v, OF substep]
    obtain u where inner: "(ss ! i, u) \<in> innermost_csstep \<mu> R"
      by blast
    from innermost_csstep_active_argI[OF i inner]
    show ?thesis by blast
  next
    case False
    then have args_NF: "\<And>i. i < length ss \<Longrightarrow>
        i \<in> \<mu> (f, length ss) \<Longrightarrow>
        ss ! i \<in> NF (csstep \<mu> R)"
      by blast
    from Fun.prems have split:
      "(Fun f ss, t) \<in> csrstep \<mu> R \<or>
       (Fun f ss, t) \<in> csnrstep \<mu> R"
      unfolding csstep_root_nonroot by blast
    show ?thesis
    proof (rule disjE[OF split])
      assume root: "(Fun f ss, t) \<in> csrstep \<mu> R"
      from csrstep_active_args_NF_imp_innermost[OF root args_NF]
      show ?thesis by blast
    next
      assume nonroot: "(Fun f ss, t) \<in> csnrstep \<mu> R"
      from nonroot obtain i ts where i: "i < length ss" "i \<in> \<mu> (f, length ss)"
        and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
        by (elim csnrstep_FunE)
      from args_NF[OF i] substep show ?thesis
        unfolding NF_iff_no_step by blast
    qed
  qed
qed

lemma NF_innermost_csstep_csstep:
  assumes wf: "wf_trs R"
  shows "NF (innermost_csstep \<mu> R) = NF (csstep \<mu> R)"
proof
  show "NF (innermost_csstep \<mu> R) \<subseteq> NF (csstep \<mu> R)"
    unfolding NF_iff_no_step
    using csstep_imp_innermost_csstep_exists[OF wf] by blast
  show "NF (csstep \<mu> R) \<subseteq> NF (innermost_csstep \<mu> R)"
    unfolding NF_iff_no_step
    using innermost_csstep_subset_csstep by blast
qed

lemma SN_innermost_csstep_reaches_csnf:
  assumes wf: "wf_trs R"
    and SN: "SN_on (innermost_csstep \<mu> R) {s}"
  shows "\<exists>t. (s,t) \<in> (innermost_csstep \<mu> R)\<^sup>* \<and>
    t \<in> NF (csstep \<mu> R)"
proof -
  from SN_on_imp_normalizability[OF SN]
  obtain t where steps: "(s,t) \<in> (innermost_csstep \<mu> R)\<^sup>*"
    and NF: "t \<in> NF (innermost_csstep \<mu> R)"
    by auto
  from NF have "t \<in> NF (csstep \<mu> R)"
    unfolding NF_innermost_csstep_csstep[OF wf] .
  with steps show ?thesis by blast
qed

definition innermost_csnf ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term"
where
  "innermost_csnf \<mu> R s = (SOME t.
    (s,t) \<in> (innermost_csstep \<mu> R)\<^sup>* \<and>
    t \<in> NF (csstep \<mu> R))"

lemma innermost_csnf:
  assumes "\<exists>t. (s,t) \<in> (innermost_csstep \<mu> R)\<^sup>* \<and>
    t \<in> NF (csstep \<mu> R)"
  shows "(s, innermost_csnf \<mu> R s) \<in>
      (innermost_csstep \<mu> R)\<^sup>* \<and>
    innermost_csnf \<mu> R s \<in> NF (csstep \<mu> R)"
proof -
  from someI_ex[OF assms] show ?thesis
    unfolding innermost_csnf_def by auto
qed

lemma innermost_csnf_from_SN:
  assumes wf: "wf_trs R"
    and SN: "SN_on (innermost_csstep \<mu> R) {s}"
  shows "(s, innermost_csnf \<mu> R s) \<in>
      (innermost_csstep \<mu> R)\<^sup>* \<and>
    innermost_csnf \<mu> R s \<in> NF (csstep \<mu> R)"
  by (rule innermost_csnf[OF
      SN_innermost_csstep_reaches_csnf[OF wf SN]])

lemma innermost_csnf_unique:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and SN: "SN_on (innermost_csstep \<mu> R) {s}"
    and steps: "(s,t) \<in> (innermost_csstep \<mu> R)\<^sup>*"
    and nf: "t \<in> NF (csstep \<mu> R)"
  shows "innermost_csnf \<mu> R s = t"
proof -
  from innermost_csnf_from_SN[OF wf SN]
  have chosen_steps: "(s,innermost_csnf \<mu> R s) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    and chosen_nf: "innermost_csnf \<mu> R s \<in>
      NF (csstep \<mu> R)" by auto
  have nf_inner: "t \<in> NF (innermost_csstep \<mu> R)"
    using nf unfolding NF_innermost_csstep_csstep[OF wf] .
  have chosen_nf_inner: "innermost_csnf \<mu> R s \<in>
      NF (innermost_csstep \<mu> R)"
    using chosen_nf unfolding NF_innermost_csstep_csstep[OF wf] .
  have joined: "(innermost_csnf \<mu> R s,t) \<in>
      (innermost_csstep \<mu> R)\<^sup>\<down>"
    by (rule CR_divergence_imp_join[
        OF csr_switch_overlay_innermost_csstep_CR[OF ortho wf]
          chosen_steps steps])
  show ?thesis
    by (rule join_NF_imp_eq[OF joined chosen_nf_inner nf_inner])
qed

lemma innermost_csnf_step_invariant:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and SN: "SN_on (innermost_csstep \<mu> R) {s}"
    and steps: "(s,t) \<in> (innermost_csstep \<mu> R)\<^sup>*"
  shows "innermost_csnf \<mu> R s = innermost_csnf \<mu> R t"
proof -
  from steps_preserve_SN_on[OF steps SN]
  have SN_t: "SN_on (innermost_csstep \<mu> R) {t}" .
  from innermost_csnf_from_SN[OF wf SN_t]
  have t_nf_steps: "(t,innermost_csnf \<mu> R t) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    and t_nf: "innermost_csnf \<mu> R t \<in> NF (csstep \<mu> R)"
    by auto
  have "(s,innermost_csnf \<mu> R t) \<in>
      (innermost_csstep \<mu> R)\<^sup>*"
    using steps t_nf_steps by auto
  from innermost_csnf_unique[OF ortho wf SN this t_nf]
  show ?thesis .
qed

fun csr_innermost_variants ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term set"
where
  "csr_innermost_variants \<mu> R (Var x) =
    (let B = {Var x}
     in B \<union> (if SN_on (csstep \<mu> R) {Var x}
       then {innermost_csnf \<mu> R u |u.
         u \<in> B \<and> SN_on (innermost_csstep \<mu> R) {u}}
       else {}))"
| "csr_innermost_variants \<mu> R (Fun f ss) =
    (let B = {Fun f us |us.
       length us = length ss \<and>
       (\<forall>i<length ss. us ! i \<in> csr_innermost_variants \<mu> R (ss ! i))}
     in B \<union> (if SN_on (csstep \<mu> R) {Fun f ss}
       then {innermost_csnf \<mu> R u |u.
         u \<in> B \<and> SN_on (innermost_csstep \<mu> R) {u}}
       else {}))"

definition csr_innermost_variants0 ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term set"
where
  "csr_innermost_variants0 \<mu> R s = (case s of
      Var x \<Rightarrow> {Var x}
    | Fun f ss \<Rightarrow> {Fun f us |us.
        length us = length ss \<and>
        (\<forall>i<length ss.
          us ! i \<in> csr_innermost_variants \<mu> R (ss ! i))})"

lemma csr_innermost_variants0_Var [simp]:
  "csr_innermost_variants0 \<mu> R (Var x) = {Var x}"
  unfolding csr_innermost_variants0_def by simp

lemma csr_innermost_variants0_Fun [simp]:
  "csr_innermost_variants0 \<mu> R (Fun f ss) =
    {Fun f us |us.
      length us = length ss \<and>
      (\<forall>i<length ss.
        us ! i \<in> csr_innermost_variants \<mu> R (ss ! i))}"
  unfolding csr_innermost_variants0_def by simp

text \<open>
  These are the paper's @{term r} and @{term r0} constructions.  The choice of
  a normal form is kept explicit.  Uniqueness will follow from confluence of
  innermost context-sensitive rewriting under the checked non-overlap premise;
  no executable checker is allowed to depend on the Hilbert choice itself.
\<close>

lemma csr_innermost_variants0_subset:
  "csr_innermost_variants0 \<mu> R s \<subseteq>
    csr_innermost_variants \<mu> R s"
  by (cases s, auto simp: csr_innermost_variants0_def Let_def)

lemma csr_innermost_variants_cases:
  "u \<in> csr_innermost_variants \<mu> R s \<longleftrightarrow>
    u \<in> csr_innermost_variants0 \<mu> R s \<or>
    (SN_on (csstep \<mu> R) {s} \<and>
      (\<exists>v. v \<in> csr_innermost_variants0 \<mu> R s \<and>
        SN_on (innermost_csstep \<mu> R) {v} \<and>
        u = innermost_csnf \<mu> R v))"
  by (cases s, auto simp: csr_innermost_variants0_def Let_def)

lemma csr_innermost_variants_csnf_closed:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and source_SN: "SN_on (csstep \<mu> R) {s}"
    and member: "v \<in> csr_innermost_variants \<mu> R s"
    and v_SN: "SN_on (innermost_csstep \<mu> R) {v}"
  shows "innermost_csnf \<mu> R v \<in>
    csr_innermost_variants \<mu> R s"
  using member[unfolded csr_innermost_variants_cases]
proof
  assume base: "v \<in> csr_innermost_variants0 \<mu> R s"
  show ?thesis
    unfolding csr_innermost_variants_cases
    using source_SN base v_SN by blast
next
  assume normalized: "SN_on (csstep \<mu> R) {s} \<and>
    (\<exists>w. w \<in> csr_innermost_variants0 \<mu> R s \<and>
      SN_on (innermost_csstep \<mu> R) {w} \<and>
      v = innermost_csnf \<mu> R w)"
  then obtain w where w_SN: "SN_on (innermost_csstep \<mu> R) {w}"
    and v: "v = innermost_csnf \<mu> R w" by blast
  from innermost_csnf_from_SN[OF wf w_SN]
  have v_NF: "v \<in> NF (csstep \<mu> R)"
    unfolding v by blast
  have fixed: "innermost_csnf \<mu> R v = v"
    by (rule innermost_csnf_unique[OF ortho wf v_SN],
        use v_NF in auto)
  show ?thesis unfolding fixed using member .
qed

lemma csr_innermost_variants_self:
  "s \<in> csr_innermost_variants \<mu> R s"
proof (induct s)
  case (Var x)
  then show ?case by (simp add: Let_def)
next
  case (Fun f ss)
  have "\<forall>i<length ss. ss ! i \<in>
      csr_innermost_variants \<mu> R (ss ! i)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ss"
    show "ss ! i \<in> csr_innermost_variants \<mu> R (ss ! i)"
      by (rule Fun.hyps, use i in auto)
  qed
  then show ?case by (auto simp: Let_def)
qed

lemma csr_innermost_variants_nonempty:
  "csr_innermost_variants \<mu> R s \<noteq> {}"
  using csr_innermost_variants_self[of s \<mu> R] by blast

lemma csr_innermost_variants0_linear_instance:
  assumes linear: "linear_term t"
    and children: "\<And>f ts i \<rho> v. t = Fun f ts \<Longrightarrow>
      i < length ts \<Longrightarrow> linear_term (ts ! i) \<Longrightarrow>
      v \<in> csr_innermost_variants \<mu> R (ts ! i \<cdot> \<rho>) \<Longrightarrow>
      \<exists>\<tau>. v = ts ! i \<cdot> \<tau> \<and>
        (\<forall>x\<in>vars_term (ts ! i).
          \<tau> x \<in> csr_innermost_variants \<mu> R (\<rho> x))"
    and member: "u \<in> csr_innermost_variants0 \<mu> R (t \<cdot> \<sigma>)"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau> \<and>
    (\<forall>x\<in>vars_term t.
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
proof (cases t)
  case (Var x)
  with member have u_member:
      "u \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
    using csr_innermost_variants0_subset by auto
  let ?\<tau> = "\<sigma>(x := u)"
  show ?thesis
    unfolding Var using u_member by (intro exI[of _ ?\<tau>], auto)
next
  case (Fun f ts)
  from linear have partition: "is_partition (map vars_term ts)"
    and linear_ts: "\<forall>s\<in>set ts. linear_term s"
    unfolding Fun by auto
  from member obtain us where u: "u = Fun f us"
    and len: "length us = length ts"
    and us: "\<forall>i<length ts. us ! i \<in>
      csr_innermost_variants \<mu> R (ts ! i \<cdot> \<sigma>)"
    unfolding Fun by auto
  have local: "\<forall>i<length ts. \<exists>\<tau>.
      us ! i = ts ! i \<cdot> \<tau> \<and>
      (\<forall>x\<in>vars_term (ts ! i).
        \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    have linear_i: "linear_term (ts ! i)"
      using linear_ts i by auto
    show "\<exists>\<tau>. us ! i = ts ! i \<cdot> \<tau> \<and>
      (\<forall>x\<in>vars_term (ts ! i).
        \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
      by (rule children[where f=f and ts=ts and i=i and \<rho>=\<sigma>
            and v="us ! i"],
          use Fun i linear_i us in auto)
  qed
  have local': "\<forall>i. \<exists>\<tau>. i < length ts \<longrightarrow>
      (us ! i = ts ! i \<cdot> \<tau> \<and>
       (\<forall>x\<in>vars_term (ts ! i).
        \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)))"
    using local by blast
  from choice[OF local'] obtain \<tau>s where chosen: "\<forall>i.
      i < length ts \<longrightarrow>
      (us ! i = ts ! i \<cdot> \<tau>s i \<and>
       (\<forall>x\<in>vars_term (ts ! i).
        \<tau>s i x \<in> csr_innermost_variants \<mu> R (\<sigma> x)))"
    by blast
  have local_eq: "\<forall>i<length ts. us ! i = ts ! i \<cdot> \<tau>s i"
    using chosen by blast
  have local_member: "\<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i).
      \<tau>s i x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
    using chosen by blast
  from subst_merge[OF partition, of \<tau>s]
  obtain \<tau> where merge: "\<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i).
      \<tau> x = \<tau>s i x" by blast
  have terms: "\<forall>i<length ts. ts ! i \<cdot> \<tau> = us ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    have "ts ! i \<cdot> \<tau> = ts ! i \<cdot> \<tau>s i"
      unfolding term_subst_eq_conv using merge i by blast
    also have "... = us ! i" using local_eq i by auto
    finally show "ts ! i \<cdot> \<tau> = us ! i" .
  qed
  have inst: "u = Fun f ts \<cdot> \<tau>"
    using u len terms unfolding Fun
    by (auto intro!: nth_equalityI)
  have vars: "\<forall>x\<in>vars_term (Fun f ts).
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
  proof (intro ballI)
    fix x
    assume x_fun: "x \<in> vars_term (Fun f ts)"
    then obtain q where q: "q \<in> set ts" and xq: "x \<in> vars_term q"
      by auto
    from q obtain i where i: "i < length ts" and qi: "ts ! i = q"
      by (metis in_set_conv_nth)
    have x: "x \<in> vars_term (ts ! i)" using xq unfolding qi .
    show "\<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
      using merge local_member i x by auto
  qed
  show ?thesis unfolding Fun using inst vars by blast
qed

theorem csr_switch_overlay_proper_lhs_variants_instance:
  fixes R :: "('f, string) trs"
  assumes ortho: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and source: "(l,r) \<in> R"
    and proper: "l \<rhd> t"
    and linear: "linear_term t"
    and member: "u \<in> csr_innermost_variants \<mu> R (t \<cdot> \<sigma>)"
  shows "\<exists>\<tau>. u = t \<cdot> \<tau> \<and>
    (\<forall>x\<in>vars_term t.
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
  using proper linear member
proof (induct t arbitrary: \<sigma> u rule: term.induct)
  case (Var x)
  let ?\<tau> = "\<sigma>(x := u)"
  show ?case
    by (rule exI[of _ ?\<tau>], use Var in auto)
next
  case (Fun f ts)
  have base: "\<And>v. v \<in> csr_innermost_variants0 \<mu> R
      (Fun f ts \<cdot> \<sigma>) \<Longrightarrow>
      \<exists>\<tau>. v = Fun f ts \<cdot> \<tau> \<and>
        (\<forall>x\<in>vars_term (Fun f ts).
          \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
  proof -
    fix v
    assume v: "v \<in> csr_innermost_variants0 \<mu> R
      (Fun f ts \<cdot> \<sigma>)"
    show "\<exists>\<tau>. v = Fun f ts \<cdot> \<tau> \<and>
      (\<forall>x\<in>vars_term (Fun f ts).
        \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
    proof (rule csr_innermost_variants0_linear_instance[OF Fun.prems(2)])
      fix g ss i \<rho> w
      assume eq: "Fun f ts = Fun g ss"
        and i: "i < length ss"
        and lin: "linear_term (ss ! i)"
        and w: "w \<in> csr_innermost_variants \<mu> R (ss ! i \<cdot> \<rho>)"
      from eq have g: "g = f" and ss: "ss = ts" by auto
      have child: "Fun f ts \<rhd> ts ! i" using i unfolding ss by auto
      have child_l: "l \<rhd> ts ! i"
        by (rule supt_trans[OF Fun.prems(1) child])
      show "\<exists>\<tau>. w = ss ! i \<cdot> \<tau> \<and>
        (\<forall>x\<in>vars_term (ss ! i).
          \<tau> x \<in> csr_innermost_variants \<mu> R (\<rho> x))"
        unfolding ss
        by (rule Fun.hyps[OF nth_mem[OF i[unfolded ss]] child_l
              lin[unfolded ss] w[unfolded ss]])
    next
      show "v \<in> csr_innermost_variants0 \<mu> R
          (Fun f ts \<cdot> \<sigma>)" by (rule v)
    qed
  qed
  from Fun.prems(3)[unfolded csr_innermost_variants_cases]
  show ?case
  proof
    assume "u \<in> csr_innermost_variants0 \<mu> R
      (Fun f ts \<cdot> \<sigma>)"
    from base[OF this] show ?thesis .
  next
    assume normalized: "SN_on (csstep \<mu> R) {Fun f ts \<cdot> \<sigma>} \<and>
      (\<exists>v. v \<in> csr_innermost_variants0 \<mu> R
          (Fun f ts \<cdot> \<sigma>) \<and>
        SN_on (innermost_csstep \<mu> R) {v} \<and>
        u = innermost_csnf \<mu> R v)"
    then obtain v where source_SN:
        "SN_on (csstep \<mu> R) {Fun f ts \<cdot> \<sigma>}"
      and v0: "v \<in> csr_innermost_variants0 \<mu> R
        (Fun f ts \<cdot> \<sigma>)"
      and v_SN: "SN_on (innermost_csstep \<mu> R) {v}"
      and u: "u = innermost_csnf \<mu> R v" by blast
    from base[OF v0] obtain \<sigma>' where v: "v = Fun f ts \<cdot> \<sigma>'"
      and sigma_member: "\<forall>x\<in>vars_term (Fun f ts).
        \<sigma>' x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
      by blast
    from innermost_csnf_from_SN[OF wf v_SN]
    have vu: "(v,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
      and u_NF: "u \<in> NF (csstep \<mu> R)" unfolding u by auto
    from csr_switch_overlay_proper_lhs_instance_innermost_steps_vars[
      OF ortho source Fun.prems(1) Fun.prems(2),
      of \<sigma>' u \<mu>]
    obtain \<tau> where u_instance: "u = Fun f ts \<cdot> \<tau>"
      and sigma_steps: "\<forall>x\<in>vars_term (Fun f ts).
        (\<sigma>' x,\<tau> x) \<in> (innermost_csstep \<mu> R)\<^sup>*"
      and inactive: "\<forall>x\<in>vars_term (Fun f ts) -
        mu_vars_term \<mu> (Fun f ts). \<tau> x = \<sigma>' x"
      using vu[unfolded v] by blast
    have tau_member: "\<forall>x\<in>vars_term (Fun f ts).
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
    proof (intro ballI)
      fix x
      assume x: "x \<in> vars_term (Fun f ts)"
      show "\<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
      proof (cases "x \<in> mu_vars_term \<mu> (Fun f ts)")
        case False
        with inactive x sigma_member show ?thesis by auto
      next
        case True
        then obtain p where p: "p \<in> mu_poss \<mu> (Fun f ts)"
          and at: "Fun f ts |_ p = Var x"
          unfolding mu_vars_term_def by blast
        have p_sigma': "p \<in> mu_poss \<mu> (Fun f ts \<cdot> \<sigma>')"
          by (rule mu_poss_subst_lift[OF p])
        have p_sigma: "p \<in> mu_poss \<mu> (Fun f ts \<cdot> \<sigma>)"
          by (rule mu_poss_subst_lift[OF p])
        have p_pos: "p \<in> poss (Fun f ts)"
          using p mu_poss_imp_poss by blast
        have at_sigma': "(Fun f ts \<cdot> \<sigma>') |_ p = \<sigma>' x"
          using subt_at_subst[OF p_pos, of \<sigma>'] at by simp
        have at_sigma: "(Fun f ts \<cdot> \<sigma>) |_ p = \<sigma> x"
          using subt_at_subst[OF p_pos, of \<sigma>] at by simp
        have local_SN: "SN_on (innermost_csstep \<mu> R) {\<sigma>' x}"
          using SN_on_innermost_csstep_mu_pos[OF wf p_sigma' v_SN[unfolded v]]
          unfolding at_sigma' .
        have original_SN: "SN_on (csstep \<mu> R) {\<sigma> x}"
          using SN_on_mu_pos[OF wf p_sigma source_SN]
          unfolding at_sigma .
        have p_tau: "p \<in> mu_poss \<mu> (Fun f ts \<cdot> \<tau>)"
          by (rule mu_poss_subst_lift[OF p])
        have at_tau: "(Fun f ts \<cdot> \<tau>) |_ p = \<tau> x"
          using subt_at_subst[OF p_pos, of \<tau>] at by simp
        have tau_NF: "\<tau> x \<in> NF (csstep \<mu> R)"
          using NF_csstep_mu_pos[OF u_NF[unfolded u_instance] p_tau]
          unfolding at_tau .
        from sigma_member[rule_format, OF x, unfolded
            csr_innermost_variants_cases]
        show ?thesis
        proof
          assume sigma0: "\<sigma>' x \<in>
            csr_innermost_variants0 \<mu> R (\<sigma> x)"
          have chosen: "innermost_csnf \<mu> R (\<sigma>' x) = \<tau> x"
            by (rule innermost_csnf_unique[OF ortho wf local_SN
                  sigma_steps[rule_format, OF x] tau_NF])
          show ?thesis
            unfolding csr_innermost_variants_cases
          proof (rule disjI2, intro conjI)
            show "SN_on (csstep \<mu> R) {\<sigma> x}" by (rule original_SN)
            show "\<exists>w. w \<in> csr_innermost_variants0 \<mu> R (\<sigma> x) \<and>
                SN_on (innermost_csstep \<mu> R) {w} \<and>
                \<tau> x = innermost_csnf \<mu> R w"
              by (intro exI[of _ "\<sigma>' x"], use sigma0 local_SN chosen in auto)
          qed
        next
          assume normalized_x: "SN_on (csstep \<mu> R) {\<sigma> x} \<and>
            (\<exists>w. w \<in> csr_innermost_variants0 \<mu> R (\<sigma> x) \<and>
              SN_on (innermost_csstep \<mu> R) {w} \<and>
              \<sigma>' x = innermost_csnf \<mu> R w)"
          then obtain w where w_SN: "SN_on (innermost_csstep \<mu> R) {w}"
            and sigma'_eq: "\<sigma>' x = innermost_csnf \<mu> R w"
            by blast
          have sigma'_NF: "\<sigma>' x \<in> NF (csstep \<mu> R)"
            unfolding sigma'_eq
            using innermost_csnf_from_SN[OF wf w_SN] by blast
          have sigma'_NF_inner: "\<sigma>' x \<in>
              NF (innermost_csstep \<mu> R)"
            using sigma'_NF innermost_csstep_subset_csstep
            unfolding NF_iff_no_step by blast
          have eq: "\<tau> x = \<sigma>' x"
            using sigma_steps[rule_format, OF x] sigma'_NF_inner
            by (induct rule: rtrancl_induct, auto simp: NF_iff_no_step)
          show ?thesis using sigma_member x unfolding eq by auto
        qed
      qed
    qed
    show ?thesis using u_instance tau_member by blast
  qed
qed

lemma csr_switch_overlay_lhs_variants0_instance:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and lr: "(l,r) \<in> R"
    and member: "u \<in> csr_innermost_variants0 \<mu> R (l \<cdot> \<sigma>)"
  shows "\<exists>\<tau>. u = l \<cdot> \<tau> \<and>
    (\<forall>x\<in>vars_term l.
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x))"
proof -
  have linear: "linear_term l"
    using ortho lr
    unfolding csr_switch_overlay_def left_linear_trs_def by blast
  from wf lr obtain f ts where lhs: "l = Fun f ts"
    unfolding wf_trs_def by blast
  then have lhs_fun: "is_Fun l" by simp
  show ?thesis
  proof (rule csr_innermost_variants0_linear_instance[
      OF linear _ member])
    fix f ts i \<rho> v
    assume l: "l = Fun f ts" and i: "i < length ts"
      and linear_i: "linear_term (ts ! i)"
      and v: "v \<in> csr_innermost_variants \<mu> R (ts ! i \<cdot> \<rho>)"
    have proper: "l \<rhd> ts ! i"
      unfolding l using i by auto
    show "\<exists>\<tau>. v = ts ! i \<cdot> \<tau> \<and>
      (\<forall>x\<in>vars_term (ts ! i).
        \<tau> x \<in> csr_innermost_variants \<mu> R (\<rho> x))"
      by (rule csr_switch_overlay_proper_lhs_variants_instance[
          OF ortho wf lr proper linear_i v])
  qed
qed

lemma csr_innermost_variants_substitution:
  assumes vars: "\<And>x. x \<in> vars_term t \<Longrightarrow>
    \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
  shows "t \<cdot> \<tau> \<in> csr_innermost_variants \<mu> R (t \<cdot> \<sigma>)"
  using vars
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have args: "\<forall>i<length ts. ts ! i \<cdot> \<tau> \<in>
      csr_innermost_variants \<mu> R (ts ! i \<cdot> \<sigma>)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    show "ts ! i \<cdot> \<tau> \<in>
      csr_innermost_variants \<mu> R (ts ! i \<cdot> \<sigma>)"
    proof (rule Fun.hyps[OF nth_mem[OF i]])
      fix x
      assume x: "x \<in> vars_term (ts ! i)"
      show "\<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
        by (rule Fun.prems, use i x in auto)
    qed
  qed
  show ?case
    by (rule csr_innermost_variants0_subset[THEN subsetD],
        auto simp: args)
qed

lemma csr_innermost_variants0_substitution_Fun:
  assumes vars: "\<And>x. x \<in> vars_term (Fun f ts) \<Longrightarrow>
    \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
  shows "Fun f ts \<cdot> \<tau> \<in>
    csr_innermost_variants0 \<mu> R (Fun f ts \<cdot> \<sigma>)"
proof -
  have "\<forall>i<length ts. ts ! i \<cdot> \<tau> \<in>
      csr_innermost_variants \<mu> R (ts ! i \<cdot> \<sigma>)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    show "ts ! i \<cdot> \<tau> \<in>
      csr_innermost_variants \<mu> R (ts ! i \<cdot> \<sigma>)"
    proof (rule csr_innermost_variants_substitution)
      fix x
      assume x: "x \<in> vars_term (ts ! i)"
      show "\<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
        by (rule vars, use i x in auto)
    qed
  qed
  then show ?thesis by auto
qed

lemma csr_root_step_variants0_simulation:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and root: "(s,t) \<in> csrstep \<mu> R"
    and redex: "SN_on (csstep \<mu> R) {s} \<or>
      s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and member: "s' \<in> csr_innermost_variants0 \<mu> R s"
    and inner_SN: "SN_on (innermost_csstep \<mu> R) {s'}"
  shows "\<exists>t'. t' \<in> csr_innermost_variants \<mu> R t \<and>
    (s',t') \<in> (innermost_csstep \<mu> R)\<^sup>+"
proof -
  from root obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf_trs_imp_lhs_Fun[OF wf lr]
  obtain f ls where l: "l = Fun f ls" by blast
  from wf lr have vars_r: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by blast
  from csr_switch_overlay_lhs_variants0_instance[
      OF ortho wf lr member[unfolded s]]
  obtain \<tau> where s': "s' = l \<cdot> \<tau>"
    and tau_member: "\<forall>x\<in>vars_term l.
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
    by blast
  let ?as = "map (\<lambda>q. q \<cdot> \<tau>) ls"
  let ?bs = "map_index (\<lambda>i a.
    if i \<in> \<mu> (f,length ls) then innermost_csnf \<mu> R a else a) ?as"
  have s'_as: "s' = Fun f ?as" unfolding s' l by simp
  have len_as: "length ?as = length ls" by simp
  have len_bs: "length ?bs = length ?as" by simp
  have as_member: "i < length ls \<Longrightarrow>
      ?as ! i \<in> csr_innermost_variants \<mu> R (ls ! i \<cdot> \<sigma>)"
      for i
  proof -
    assume i: "i < length ls"
    have local_vars: "\<And>x. x \<in> vars_term (ls ! i) \<Longrightarrow>
      \<tau> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
      using tau_member i unfolding l by auto
    show ?thesis
      by (simp add: i, rule csr_innermost_variants_substitution[OF local_vars])
  qed
  have as_SN: "i < length ls \<Longrightarrow>
      i \<in> \<mu> (f,length ls) \<Longrightarrow>
      SN_on (innermost_csstep \<mu> R) {?as ! i}" for i
  proof -
    assume i: "i < length ls" and active: "i \<in> \<mu> (f,length ls)"
    have root_pos: "[] \<in> mu_poss \<mu> (?as ! i)"
      by (cases "?as ! i", auto)
    have pos: "[i] \<in> mu_poss \<mu> (Fun f ?as)"
      using i active root_pos by auto
    from SN_on_innermost_csstep_mu_pos[OF wf pos inner_SN[unfolded s'_as]]
    show ?thesis using i by simp
  qed
  have original_SN: "i < length ls \<Longrightarrow>
      i \<in> \<mu> (f,length ls) \<Longrightarrow>
      SN_on (csstep \<mu> R) {ls ! i \<cdot> \<sigma>}" for i
  proof -
    assume i: "i < length ls" and active: "i \<in> \<mu> (f,length ls)"
    have source: "s = Fun f (map (\<lambda>q. q \<cdot> \<sigma>) ls)"
      unfolding s l by simp
    have source_redex:
        "SN_on (csstep \<mu> R) {Fun f (map (\<lambda>q. q \<cdot> \<sigma>) ls)} \<or>
         Fun f (map (\<lambda>q. q \<cdot> \<sigma>) ls) \<in>
           mu_Tinf \<mu> (csstep \<mu> R)"
      using redex unfolding source .
    from terminating_or_mu_Tinf_active_arg_SN[
      where ss="map (\<lambda>q. q \<cdot> \<sigma>) ls" and f=f and i=i,
      OF wf _ _ source_redex]
    show ?thesis using i active by simp
  qed
  have local_steps: "i < length ?as \<Longrightarrow>
      i \<in> \<mu> (f,length ?as) \<Longrightarrow>
      (?as ! i,?bs ! i) \<in> (innermost_csstep \<mu> R)\<^sup>*" for i
  proof -
    assume i: "i < length ?as" and active: "i \<in> \<mu> (f,length ?as)"
    have i': "i < length ls" using i by simp
    have active': "i \<in> \<mu> (f,length ls)" using active by simp
    from innermost_csnf_from_SN[OF wf as_SN[OF i' active']]
    show ?thesis using i active by simp
  qed
  have local_inactive: "i < length ?as \<Longrightarrow>
      i \<notin> \<mu> (f,length ?as) \<Longrightarrow> ?bs ! i = ?as ! i" for i
    by simp
  have lifted: "(s',Fun f ?bs) \<in> (innermost_csstep \<mu> R)\<^sup>*"
    unfolding s'_as
    by (rule innermost_cssteps_active_argsI[OF len_bs local_steps
          local_inactive])
  have bs_member: "i < length ls \<Longrightarrow>
      ?bs ! i \<in> csr_innermost_variants \<mu> R (ls ! i \<cdot> \<sigma>)"
      for i
  proof -
    assume i: "i < length ls"
    show ?thesis
    proof (cases "i \<in> \<mu> (f,length ls)")
      case True
      from csr_innermost_variants_csnf_closed[
        OF ortho wf original_SN[OF i True] as_member[OF i]
          as_SN[OF i True]]
      show ?thesis using i True by simp
    next
      case False
      show ?thesis using as_member[OF i] i False by simp
    qed
  qed
  have bs0: "Fun f ?bs \<in>
      csr_innermost_variants0 \<mu> R (l \<cdot> \<sigma>)"
    unfolding l using len_bs bs_member by auto
  from csr_switch_overlay_lhs_variants0_instance[OF ortho wf lr bs0]
  obtain \<delta> where lhs: "Fun f ?bs = l \<cdot> \<delta>"
    and delta_member: "\<forall>x\<in>vars_term l.
      \<delta> x \<in> csr_innermost_variants \<mu> R (\<sigma> x)"
    by blast
  have target_member: "r \<cdot> \<delta> \<in>
      csr_innermost_variants \<mu> R (r \<cdot> \<sigma>)"
    by (rule csr_innermost_variants_substitution,
        use delta_member vars_r in blast)
  have root_delta: "(l \<cdot> \<delta>,r \<cdot> \<delta>) \<in> csrstep \<mu> R"
    unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
    using lr by (intro exI[of _ "(l,r)"] exI[of _ \<delta>], auto)
  have bs_NF: "i < length ?bs \<Longrightarrow>
      i \<in> \<mu> (f,length ?bs) \<Longrightarrow>
      ?bs ! i \<in> NF (csstep \<mu> R)" for i
  proof -
    assume i: "i < length ?bs" and active: "i \<in> \<mu> (f,length ?bs)"
    have i': "i < length ls" using i len_bs by simp
    have active': "i \<in> \<mu> (f,length ls)"
      using active len_bs by simp
    from innermost_csnf_from_SN[OF wf as_SN[OF i' active']]
    show ?thesis using i i' active active' len_bs by simp
  qed
  have final_step: "(Fun f ?bs,r \<cdot> \<delta>) \<in>
      innermost_csstep \<mu> R"
    by (rule csrstep_active_args_NF_imp_innermost[
        OF root_delta[folded lhs] bs_NF])
  have plus: "(s',r \<cdot> \<delta>) \<in> (innermost_csstep \<mu> R)\<^sup>+"
    by (rule rtrancl_into_trancl1[OF lifted final_step])
  show ?thesis unfolding t using target_member plus by blast
qed

text \<open>
  The later executable innermost processor reuses the separately named
  named RTA'08 CS-DP construction.  Keeping that construction in the
  minimal CS-DP theory avoids a second, extension-local definition of the same
  ordinary and migrating-variable pair basis.  What is new here is the checked
  orthogonal switch and its innermost chain semantics, not a renamed copy of
  the pairs.
\<close>

end
