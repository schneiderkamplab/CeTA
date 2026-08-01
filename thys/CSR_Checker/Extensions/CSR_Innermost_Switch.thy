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
  have conv: "(innermost_csnf \<mu> R s,t) \<in>
      (innermost_csstep \<mu> R)\<^sup>\<leftrightarrow>\<^sup>*"
  proof -
    have forward: "(s,innermost_csnf \<mu> R s) \<in>
        (innermost_csstep \<mu> R)\<^sup>\<leftrightarrow>\<^sup>*"
      by (rule conversionI'[OF chosen_steps])
    have backward: "(innermost_csnf \<mu> R s,s) \<in>
        (innermost_csstep \<mu> R)\<^sup>\<leftrightarrow>\<^sup>*"
      using conversion_sym forward unfolding sym_def by blast
    have onward: "(s,t) \<in> (innermost_csstep \<mu> R)\<^sup>\<leftrightarrow>\<^sup>*"
      by (rule conversionI'[OF steps])
    show ?thesis
      using conversion_trans backward onward unfolding trans_def by blast
  qed
  from CR_NF_conv[OF csr_switch_overlay_innermost_csstep_CR[OF ortho wf]
      nf_inner conv]
  show ?thesis using chosen_nf_inner by simp
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

text \<open>
  The later executable innermost processor reuses the separately named
  named RTA'08 CS-DP construction.  Keeping that construction in the
  minimal CS-DP theory avoids a second, extension-local definition of the same
  ordinary and migrating-variable pair basis.  What is new here is the checked
  orthogonal switch and its innermost chain semantics, not a renamed copy of
  the pairs.
\<close>

end
