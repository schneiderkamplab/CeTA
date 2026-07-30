(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Improved_CSDP_Proofs
  imports
    "CSR_Checker_Core.CSR_Checker"
begin

text \<open>
  The improved CS-DP construction of Alarcón, Emmes, Fuhs, Giesl,
  Gutiérrez, Lucas, Schneider-Kamp, and Thiemann replaces collapsing
  dependency pairs by pairs through a fresh unary unhiding symbol.

  We formulate the semantic sets independently from their executable list
  implementation.  This lets the checker accept a conservative finite
  superset, as emitted by Ferrum, while the soundness proof only uses the
  pairs required by the construction.
\<close>

definition inactive_fun_subterm_on ::
  "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "inactive_fun_subterm_on \<mu> r t \<longleftrightarrow>
    (\<exists>p. p \<in> fun_poss r \<and> p \<notin> mu_fun_poss \<mu> r \<and> r |_ p = t)"

definition hidden_term_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "hidden_term_on \<mu> D R t \<longleftrightarrow>
    root t \<in> Some ` D \<and> (\<exists>l r. (l,r) \<in> R \<and> inactive_fun_subterm_on \<mu> r t)"

definition hides_position_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f \<times> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "hides_position_on \<mu> D R fn i \<longleftrightarrow>
    (\<exists>l r p f ts. (l,r) \<in> R \<and> p \<in> fun_poss r \<and>
      p \<notin> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      fn = (f, length ts) \<and>
      i < length ts \<and> i \<in> \<mu> (f, length ts) \<and>
      (\<exists>q. q \<in> mu_poss \<mu> (ts ! i) \<and>
        (is_Var ((ts ! i) |_ q) \<or> root ((ts ! i) |_ q) \<in> Some ` D)))"

inductive hiding_context_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> bool"
for \<mu> D R
where
  hole[intro]: "hiding_context_on \<mu> D R \<box>"
| more[intro]: "hides_position_on \<mu> D R
      (f, Suc (length bef + length aft)) (length bef) \<Longrightarrow>
    hiding_context_on \<mu> D R C \<Longrightarrow>
    hiding_context_on \<mu> D R (More f bef C aft)"

definition hidden_instance_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "hidden_instance_on \<mu> D R t \<longleftrightarrow>
    (\<exists>h \<sigma>. hidden_term_on \<mu> D R h \<and> t = h \<cdot> \<sigma>)"

definition has_hiding_property ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) term) set \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "has_hiding_property \<mu> D R A u \<longleftrightarrow>
    u \<in> mu_Tinf \<mu> A \<and>
    (\<forall>s t. u \<rhd> s \<longrightarrow> \<not> mu_supt \<mu> u s \<longrightarrow>
      (s = t \<or> mu_supt \<mu> s t) \<longrightarrow>
      t \<in> mu_Tinf \<mu> A \<longrightarrow>
      (\<exists>C h \<sigma>. hiding_context_on \<mu> D R C \<and>
        hidden_term_on \<mu> D R h \<and> s = C\<langle>h \<cdot> \<sigma>\<rangle> \<and> t = h \<cdot> \<sigma>))"

lemma Tinf_has_hiding_property:
  assumes T: "u \<in> Tinf A"
  shows "has_hiding_property \<mu> D R A u"
proof -
  have mu_T: "u \<in> mu_Tinf \<mu> A"
    by (rule Tinf_imp_mu_Tinf[OF T])
  show ?thesis
    unfolding has_hiding_property_def
  proof (intro conjI allI impI)
    show "u \<in> mu_Tinf \<mu> A"
      by (rule mu_T)
  next
    fix s t
    assume us: "u \<rhd> s"
      and inactive: "\<not> mu_supt \<mu> u s"
      and st: "s = t \<or> mu_supt \<mu> s t"
      and tT: "t \<in> mu_Tinf \<mu> A"
    have ut: "u \<rhd> t"
    using st
    proof
      assume "s = t"
      with us show ?thesis by simp
    next
      assume "mu_supt \<mu> s t"
      from us mu_supt_imp_supt[OF this] show ?thesis
        by (rule supt_trans)
    qed
    from T ut have "SN_on A {t}"
      unfolding Tinf_def by auto
    moreover from tT have "\<not> SN_on A {t}"
      unfolding mu_Tinf_def by auto
    ultimately show "\<exists>C h \<sigma>. hiding_context_on \<mu> D R C \<and>
      hidden_term_on \<mu> D R h \<and> s = C\<langle>h \<cdot> \<sigma>\<rangle> \<and> t = h \<cdot> \<sigma>"
      by contradiction
  qed
qed

lemma mu_Tinf_defined_root:
  assumes wf: "wf_trs R"
    and T: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  obtains f ts where "t = Fun f ts" and "defined R (f,length ts)"
proof -
  from T have notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    unfolding mu_Tinf_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN]
  obtain p f ts where p: "p \<in> mu_fun_poss \<mu> t"
    and sub: "t |_ p = Fun f ts"
    and def: "defined R (f,length ts)"
    and subT: "t |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  have "p = []"
  proof (rule ccontr)
    assume "p \<noteq> []"
    then obtain i q where pq: "p = i # q"
      by (cases p) auto
    have p_mu: "p \<in> mu_poss \<mu> t"
      by (rule mu_fun_poss_imp_mu_poss[OF p])
    have active: "mu_supt \<mu> t (t |_ p)"
      unfolding mu_supt_def
      apply (rule exI[of _ i])
      apply (rule exI[of _ q])
      using p_mu pq by simp
    from T active have "SN_on (csstep \<mu> R) {t |_ p}"
      unfolding mu_Tinf_def by auto
    moreover from subT have "\<not> SN_on (csstep \<mu> R) {t |_ p}"
      unfolding mu_Tinf_def by auto
    ultimately show False by contradiction
  qed
  with sub have "t = Fun f ts" by simp
  then show ?thesis
    by (rule that[OF _ def])
qed

definition collapsing_mu_CSDP_on ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow> 'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "collapsing_mu_CSDP_on shp U \<mu> R =
    {(sharp_term shp l, Fun U [Var x]) | l r x.
      (l,r) \<in> R \<and> x \<in> mu_vars_term \<mu> r \<and> x \<notin> mu_vars_term \<mu> l}"

definition hidden_mu_CSDP_on ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "hidden_mu_CSDP_on shp U \<mu> D R =
    {(Fun U [t], sharp_term shp t) | t.
      hidden_term_on \<mu> D R t}"

definition improved_mu_CSDP_on ::
  "('f::{showl, compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow>
    'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "improved_mu_CSDP_on shp U \<mu> D R =
    mu_CSDP_on shp \<mu> D R \<union>
    collapsing_mu_CSDP_on shp U \<mu> R \<union>
    hidden_mu_CSDP_on shp U \<mu> D R"

lemma hidden_term_on_is_Fun:
  assumes "hidden_term_on \<mu> D R t"
  shows "is_Fun t"
  using assms unfolding hidden_term_on_def
  by (cases t, auto)

lemma hiding_context_on_comp:
  assumes "hiding_context_on \<mu> D R C"
    and "hiding_context_on \<mu> D R D'"
  shows "hiding_context_on \<mu> D R (C \<circ>\<^sub>c D')"
  using assms(1)
proof (induct rule: hiding_context_on.induct)
  case hole
  then show ?case using assms(2) by simp
next
  case (more f bef aft C)
  then show ?case by auto
qed

lemma hiding_context_on_subst:
  assumes "hiding_context_on \<mu> D R C"
  shows "hiding_context_on \<mu> D R (C \<cdot>\<^sub>c \<sigma>)"
  using assms
proof (induct rule: hiding_context_on.induct)
  case hole
  show ?case by (simp, rule hiding_context_on.hole)
next
  case (more f bef aft C)
  then show ?case by auto
qed

lemma mu_fun_poss_append_prefix:
  assumes "p @ q \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> t"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case
    by (cases p) auto
qed

lemma mu_poss_fun_poss_imp_mu_fun_poss:
  assumes "p \<in> mu_poss \<mu> t" and "p \<in> fun_poss t"
  shows "p \<in> mu_fun_poss \<mu> t"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case
    by (cases p) auto
qed

lemma mu_poss_append_prefix:
  assumes "p @ q \<in> mu_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> t"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case
    by (cases p) auto
qed

lemma mu_fun_poss_append_suffix:
  assumes pq: "p @ q \<in> mu_fun_poss \<mu> t"
    and p: "p \<in> poss t"
  shows "q \<in> mu_fun_poss \<mu> (t |_ p)"
  using pq p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  from Cons.prems obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts"
    and pq: "p @ q \<in> mu_fun_poss \<mu> (ts ! i)"
    and p: "p \<in> poss (ts ! i)"
    by (cases t, auto)
  show ?case
    unfolding t using Cons.hyps[OF pq p] i by simp
qed

lemma mu_poss_replace_at_below:
  assumes p: "p \<in> mu_poss \<mu> t"
    and le: "p \<le>\<^sub>p q"
    and q: "q \<in> poss t"
    and root: "p \<noteq> q \<or> is_Fun u"
  shows "p \<in> mu_poss \<mu> (replace_at t q u)"
  using p le q root
proof (induct t arbitrary: p q)
  case (Var x)
  then show ?case by (cases u) auto
next
  case (Fun f ts)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      by (cases q; cases u) (use Fun.prems in auto)
  next
    case (Cons i p')
    from Fun.prems(1)[unfolded Cons]
    have i: "i < length ts" "i \<in> \<mu> (f,length ts)"
      and p': "p' \<in> mu_poss \<mu> (ts ! i)"
      by auto
    from Fun.prems(2) Cons obtain q' where q: "q = i # q'"
      and le': "p' \<le>\<^sub>p q'"
      by (cases q) auto
    have q'_poss: "q' \<in> poss (ts ! i)"
      using Fun.prems(3) Cons q by auto
    have rec: "p' \<in> mu_poss \<mu> (replace_at (ts ! i) q' u)"
      by (rule Fun.hyps[OF nth_mem[OF i(1)] p' le' q'_poss],
          use Fun.prems(4) Cons q in auto)
    show ?thesis
      unfolding Cons q using i rec q'_poss by (simp add: nth_append)
  qed
qed

lemma csstep_new_inactive_subterm_rhs:
  assumes wf: "wf_trs R"
    and step: "(u,v) \<in> csstep \<mu> R"
    and vs: "v \<rhd> s"
    and inactive: "\<not> mu_supt \<mu> v s"
    and new: "\<not> u \<rhd> s"
    and s_fun: "is_Fun s"
  obtains l r \<sigma> p q where
    "(l,r) \<in> R"
    "p \<in> mu_fun_poss \<mu> u"
    "u |_ p = l \<cdot> \<sigma>"
    "q \<in> fun_poss r"
    "q \<notin> mu_fun_poss \<mu> r"
    "s = (r |_ q) \<cdot> \<sigma>"
proof -
  from step obtain p lr \<sigma> where rst:
      "(u,v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p u"
    unfolding csstep_def csstep_p_def by auto
  obtain l r where lr_pair: "lr = (l,r)"
    by (cases lr)
  from rst[unfolded rstep_r_p_s_def' lr_pair]
  have lr: "(l,r) \<in> R"
    and p_poss: "p \<in> poss u"
    and redex: "u |_ p = l \<cdot> \<sigma>"
    and v: "v = replace_at u p (r \<cdot> \<sigma>)"
    by auto
  from wf lr have lhs_fun: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  have p_active: "p \<in> mu_fun_poss \<mu> u"
    by (rule csstep_redex_mu_fun_poss[OF wf],
        unfold csstep_p_def, use rst cond in blast)
  from supt_imp_subt_at_nepos[OF vs]
  obtain i q' where iq_poss: "i # q' \<in> poss v"
    and iq_sub: "v |_ (i # q') = s"
    by blast
  let ?q = "i # q'"
  have q_ne: "?q \<noteq> []" by simp
  consider (above) "?q \<le>\<^sub>p p"
    | (below) "p \<le>\<^sub>p ?q"
    | (parallel) "?q \<bottom> p"
    using parallel_pos by blast
  then show ?thesis
  proof cases
    case above
    from prefixE[OF above]
    obtain a where p_eq: "p = ?q @ a" by blast
    have q_mu_u: "?q \<in> mu_poss \<mu> u"
      using mu_fun_poss_append_prefix[OF p_active[unfolded p_eq]] .
    have q_poss_u: "?q \<in> poss u"
      using p_poss p_eq unfolding poss_append_poss by auto
    have root: "?q \<noteq> p \<or> is_Fun (r \<cdot> \<sigma>)"
    proof (cases "?q = p")
      case True
      then have "r \<cdot> \<sigma> = s"
        using iq_sub p_poss unfolding v
        by (simp add: replace_at_subt_at)
      with s_fun show ?thesis by simp
    qed simp
    have q_mu_v: "?q \<in> mu_poss \<mu> v"
      unfolding v
      by (rule mu_poss_replace_at_below[
          OF q_mu_u above p_poss root])
    have "mu_supt \<mu> v s"
      unfolding mu_supt_def using q_mu_v iq_sub by blast
    with inactive show ?thesis by contradiction
  next
    case parallel
    have q_poss_u: "?q \<in> poss u"
      using parallel_poss_replace_at[
          OF parallel_pos_sym[OF parallel] p_poss, of "r \<cdot> \<sigma>"]
        iq_poss unfolding v by simp
    have q_sub_u: "u |_ ?q = s"
      using parallel_replace_at_subt_at[
          OF parallel_pos_sym[OF parallel] p_poss q_poss_u,
          of "r \<cdot> \<sigma>"]
        iq_sub unfolding v by simp
    have "u \<rhd> s"
      using subt_at_nepos_imp_supt[OF q_poss_u] q_sub_u by simp
    with new show ?thesis by contradiction
  next
    case below
    from prefixE[OF below]
    obtain a where q: "?q = p @ a" by blast
    have a_poss: "a \<in> poss (r \<cdot> \<sigma>)"
      using iq_poss p_poss unfolding v q poss_append_poss
      by (simp add: replace_at_subt_at)
    have p_poss_v: "p \<in> poss v"
      unfolding v
      by (rule replace_at_below_poss[OF p_poss prefix_order.order_refl])
    have vp: "v |_ p = r \<cdot> \<sigma>"
      unfolding v by (rule replace_at_subt_at[OF p_poss])
    have s: "(r \<cdot> \<sigma>) |_ a = s"
      using iq_sub p_poss_v unfolding q vp[symmetric]
      by (simp add: subt_at_append)
    from poss_subst_choice[OF a_poss]
    show ?thesis
    proof
      assume orig: "a \<in> poss r \<and> is_Fun (r |_ a)"
      have a_fun: "a \<in> fun_poss r"
        by (rule poss_is_Fun_fun_poss, use orig in auto)
      have s_inst: "s = (r |_ a) \<cdot> \<sigma>"
        using s orig by simp
      have a_inactive: "a \<notin> mu_fun_poss \<mu> r"
      proof
        assume a_active: "a \<in> mu_fun_poss \<mu> r"
        have a_active_inst: "a \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
          by (rule mu_fun_poss_subst_lift[OF a_active])
        have q_active: "?q \<in> mu_fun_poss \<mu> v"
          unfolding v q
          by (rule mu_fun_poss_replace_at_append[OF p_active a_active_inst])
        have "mu_supt \<mu> v s"
          unfolding mu_supt_def
          using mu_fun_poss_imp_mu_poss[OF q_active] iq_sub q_ne by (cases ?q, auto)
        with inactive show False by contradiction
      qed
      show ?thesis
        by (rule that[OF lr p_active redex a_fun a_inactive s_inst])
    next
      assume subst_case: "\<exists>x q1 q2.
        q1 \<in> poss r \<and> q2 \<in> poss (\<sigma> x) \<and>
        r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
        a = q1 @ q2 \<and> (r \<cdot> \<sigma>) |_ a = \<sigma> x |_ q2"
      then obtain x q1 q2 where
        subst: "q1 \<in> poss r" "q2 \<in> poss (\<sigma> x)"
          "r |_ q1 = Var x" "x \<in> vars_term r"
          "a = q1 @ q2" "(r \<cdot> \<sigma>) |_ a = \<sigma> x |_ q2"
        by blast
      from vars subst(4) have x_l: "x \<in> vars_term l" by auto
      have l_supt_var: "l \<rhd> Var x"
        using lhs_fun x_l supteq_Var[of x l]
        unfolding supt_supteq_conv by (cases l, auto)
      have l_supt_x: "l \<cdot> \<sigma> \<rhd> \<sigma> x"
        using supt_subst[OF l_supt_var, of \<sigma>] by simp
      have sx: "\<sigma> x \<unrhd> s"
        using subst(2) subst(6) s subt_at_imp_supteq by auto
      have redex_supt: "l \<cdot> \<sigma> \<rhd> s"
        by (rule supt_supteq_trans[OF l_supt_x sx])
      have u_supt_redex: "u \<unrhd> l \<cdot> \<sigma>"
        using subt_at_imp_supteq[OF p_poss] redex by simp
      have "u \<rhd> s"
        using u_supt_redex redex_supt
        by (meson supteq_supt_trans)
      from new this show ?thesis by simp
    qed
  qed
qed

lemma inactive_rhs_active_context_hiding_claim:
  assumes lr: "(l,r) \<in> R"
    and p_fun: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss \<mu> r"
    and sub: "r |_ p = h"
    and q: "q \<in> mu_poss \<mu> h"
    and target: "is_Var (h |_ q) \<or> root (h |_ q) \<in> Some ` D"
  shows "hiding_context_on \<mu> D R (ctxt_of_pos_term q h)"
  using p_fun inactive sub q target
proof (induct q arbitrary: h p)
  case Nil
  show ?case by (simp, rule hiding_context_on.hole)
next
  case (Cons i q)
  note p_fun = Cons.prems(1)
  note inactive = Cons.prems(2)
  note sub = Cons.prems(3)
  from Cons.prems(4) obtain f ts where
    h: "h = Fun f ts"
    and i: "i < length ts" "i \<in> \<mu> (f,length ts)"
    and q_mu: "q \<in> mu_poss \<mu> (ts ! i)"
    by (cases h) auto
  have target':
    "is_Var ((ts ! i) |_ q) \<or> root ((ts ! i) |_ q) \<in> Some ` D"
    using Cons.prems(5) i unfolding h by simp
  have sub_fun: "r |_ p = Fun f ts"
    by (rule HOL.trans[OF sub h])
  have hide: "hides_position_on \<mu> D R (f,length ts) i"
    unfolding hides_position_on_def
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p_fun inactive sub_fun i q_mu target' by auto
  have tail: "hiding_context_on \<mu> D R
      (ctxt_of_pos_term q (ts ! i))"
  proof (cases q)
    case Nil
    have "hiding_context_on \<mu> D R \<box>"
      by (rule hiding_context_on.hole)
    then show ?thesis unfolding Nil by simp
  next
    case (Cons j qs)
    have iq_poss: "i # q \<in> poss h"
      using i q_mu mu_poss_imp_poss unfolding h by auto
    have p_poss: "p \<in> poss r"
      using p_fun fun_poss_imp_poss by blast
    have piq_poss: "p @ (i # q) \<in> poss r"
      using p_poss iq_poss sub
      unfolding poss_append_poss by auto
    have q_ne: "q \<noteq> []"
      unfolding Cons by simp
    have pi_q_poss: "(p @ [i]) @ q \<in> poss r"
      using piq_poss by simp
    have pi_fun: "p @ [i] \<in> fun_poss r"
      by (rule fun_poss_append_poss[OF pi_q_poss q_ne])
    have pi_inactive: "p @ [i] \<notin> mu_fun_poss \<mu> r"
    proof
      assume active: "p @ [i] \<in> mu_fun_poss \<mu> r"
      have p_mu: "p \<in> mu_poss \<mu> r"
        by (rule mu_fun_poss_append_prefix[OF active])
      have "p \<in> mu_fun_poss \<mu> r"
        by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF p_mu p_fun])
      with inactive show False by contradiction
    qed
    have pi_sub: "r |_ (p @ [i]) = ts ! i"
      using sub i p_poss unfolding h
      by (simp add: subt_at_append)
    show ?thesis
      by (rule Cons.hyps[
          OF pi_fun pi_inactive pi_sub q_mu target'])
  qed
  show ?case
    unfolding h ctxt_of_pos_term.simps
    by (rule hiding_context_on.more[OF _ tail], use hide i in simp)
qed

lemma inactive_rhs_active_defined_hidden_claim:
  assumes lr: "(l,r) \<in> R"
    and p_fun: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss \<mu> r"
    and sub: "r |_ p = h"
    and q: "q \<in> mu_fun_poss \<mu> h"
    and root: "root (h |_ q) \<in> Some ` D"
  shows "hidden_term_on \<mu> D R (h |_ q)"
proof -
  have p_poss: "p \<in> poss r"
    using p_fun fun_poss_imp_poss by blast
  have q_poss: "q \<in> poss h"
    using q mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
  have pq_fun: "p @ q \<in> fun_poss r"
  proof -
    have pq_poss: "p @ q \<in> poss r"
      using p_poss q_poss sub unfolding poss_append_poss by auto
    have sub_fun: "is_Fun (h |_ q)"
      using root by (cases "h |_ q") auto
    have "r |_ (p @ q) = h |_ q"
      using p_poss sub by (simp add: subt_at_append)
    then have at_fun: "is_Fun (r |_ (p @ q))"
      using sub_fun by simp
    show ?thesis
      by (rule poss_is_Fun_fun_poss[OF pq_poss at_fun])
  qed
  have pq_inactive: "p @ q \<notin> mu_fun_poss \<mu> r"
  proof
    assume active: "p @ q \<in> mu_fun_poss \<mu> r"
    have p_mu: "p \<in> mu_poss \<mu> r"
      by (rule mu_fun_poss_append_prefix[OF active])
    have "p \<in> mu_fun_poss \<mu> r"
      by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF p_mu p_fun])
    with inactive show False by contradiction
  qed
  have pq_sub: "r |_ (p @ q) = h |_ q"
    using p_poss sub by (simp add: subt_at_append)
  show ?thesis
    unfolding hidden_term_on_def inactive_fun_subterm_on_def
    using root lr pq_fun pq_inactive pq_sub by blast
qed

lemma csstep_hiding_property_preserve:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and step: "(u,v) \<in> csstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    and vT: "v \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "has_hiding_property \<mu> D R (csstep \<mu> R) v"
proof -
  from hp have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  show ?thesis
    unfolding has_hiding_property_def
  proof (intro conjI allI impI)
    show "v \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by (rule vT)
  next
    fix s t
    assume vs: "v \<rhd> s"
      and inactive_v: "\<not> mu_supt \<mu> v s"
      and st: "s = t \<or> mu_supt \<mu> s t"
      and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    from mu_Tinf_defined_root[OF wf tT]
    obtain f ts where t: "t = Fun f ts"
      and f_def: "defined R (f,length ts)" .
    have fD: "(f,length ts) \<in> D"
      using defs f_def by auto
    have t_fun: "is_Fun t"
      unfolding t by simp
    have s_fun: "is_Fun s"
      using st t_fun
      unfolding mu_supt_def by (cases s, auto)
    show "\<exists>C h \<sigma>. hiding_context_on \<mu> D R C \<and>
      hidden_term_on \<mu> D R h \<and> s = C\<langle>h \<cdot> \<sigma>\<rangle> \<and> t = h \<cdot> \<sigma>"
    proof (cases "u \<rhd> s")
      case True
      have inactive_u: "\<not> mu_supt \<mu> u s"
      proof
        assume active: "mu_supt \<mu> u s"
        from uT active have sn_s: "SN_on (csstep \<mu> R) {s}"
          unfolding mu_Tinf_def by auto
        have sn_t: "SN_on (csstep \<mu> R) {t}"
        using st
        proof
          assume "s = t"
          with sn_s show ?thesis by simp
        next
          assume active_st: "mu_supt \<mu> s t"
          from active_st obtain i q where pos: "i # q \<in> mu_poss \<mu> s"
            and sub: "s |_ (i # q) = t"
            unfolding mu_supt_def by auto
          show ?thesis
            using SN_on_mu_pos[OF wf pos sn_s] sub by simp
        qed
        from tT have "\<not> SN_on (csstep \<mu> R) {t}"
          unfolding mu_Tinf_def by auto
        with sn_t show False by contradiction
      qed
      from hp True inactive_u st tT
      show ?thesis
        unfolding has_hiding_property_def by blast
    next
      case False
      from csstep_new_inactive_subterm_rhs[
          OF wf step vs inactive_v False s_fun]
      obtain l r \<sigma> p q where lr: "(l,r) \<in> R"
        and p_active: "p \<in> mu_fun_poss \<mu> u"
        and redex: "u |_ p = l \<cdot> \<sigma>"
        and q_fun: "q \<in> fun_poss r"
        and q_inactive: "q \<notin> mu_fun_poss \<mu> r"
        and s: "s = (r |_ q) \<cdot> \<sigma>"
        .
      let ?h = "r |_ q"
      have q_poss: "q \<in> poss r"
        using q_fun fun_poss_imp_poss by blast
      have h_fun: "is_Fun ?h"
        using fun_poss_fun_conv[OF q_fun] by auto
      have k_active: "\<exists>k. k \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>) \<and>
        (?h \<cdot> \<sigma>) |_ k = t"
      using st
      proof
        assume eq: "s = t"
        have "[] \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>)"
          using h_fun by (cases ?h, auto)
        moreover have "(?h \<cdot> \<sigma>) |_ [] = t"
          using eq s by simp
        ultimately show ?thesis by blast
      next
        assume active_st: "mu_supt \<mu> s t"
        then obtain i k where pos: "i # k \<in> mu_poss \<mu> s"
          and sub: "s |_ (i # k) = t"
          unfolding mu_supt_def by auto
        have fun_pos: "i # k \<in> fun_poss s"
          by (rule poss_is_Fun_fun_poss[
              OF mu_poss_imp_poss[OF pos] t_fun[unfolded sub[symmetric]]])
        have active: "i # k \<in> mu_fun_poss \<mu> s"
          by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF pos fun_pos])
        show ?thesis
          by (rule exI[of _ "i # k"], use active sub s in auto)
      qed
      then obtain k where k_active: "k \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>)"
        and hk: "(?h \<cdot> \<sigma>) |_ k = t"
        by blast
      from mu_fun_poss_subst_cases_aux_mu[OF k_active]
      show ?thesis
      proof
        assume orig: "k \<in> mu_fun_poss \<mu> ?h \<and>
          (?h \<cdot> \<sigma>) |_ k = (?h |_ k) \<cdot> \<sigma>"
        have k_h: "k \<in> mu_fun_poss \<mu> ?h"
          using orig by auto
        have target: "root (?h |_ k) \<in> Some ` D"
        proof -
          from k_h obtain g us where base: "?h |_ k = Fun g us"
            using mu_fun_poss_imp_fun_poss fun_poss_fun_conv by blast
          from hk orig t base have g: "g = f" and len: "length us = length ts"
            by auto
          show ?thesis
            unfolding base using fD g len by auto
        qed
        have hidden: "hidden_term_on \<mu> D R (?h |_ k)"
          by (rule inactive_rhs_active_defined_hidden_claim[
              OF lr q_fun q_inactive refl k_h target])
        have C: "hiding_context_on \<mu> D R (ctxt_of_pos_term k ?h)"
          by (rule inactive_rhs_active_context_hiding_claim[
              OF lr q_fun q_inactive refl
                mu_fun_poss_imp_mu_poss[OF k_h]],
              use target in auto)
        have C_subst:
          "hiding_context_on \<mu> D R (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)"
          by (rule hiding_context_on_subst[OF C])
        have k_poss: "k \<in> poss ?h"
          using k_h mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
        have fill_h: "?h =
            (ctxt_of_pos_term k ?h)\<langle>?h |_ k\<rangle>"
          using ctxt_supt_id[OF k_poss] by simp
        have fill: "s = (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)
            \<langle>(?h |_ k) \<cdot> \<sigma>\<rangle>"
        proof -
          have "?h \<cdot> \<sigma> =
              ((ctxt_of_pos_term k ?h)\<langle>?h |_ k\<rangle>) \<cdot> \<sigma>"
            using fill_h by simp
          also have "... = (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)
              \<langle>(?h |_ k) \<cdot> \<sigma>\<rangle>"
            by (rule subst_apply_term_ctxt_apply_distrib)
          finally show ?thesis
            unfolding s .
        qed
        have target_inst: "t = (?h |_ k) \<cdot> \<sigma>"
          using hk orig by auto
        show ?thesis
          using C_subst hidden fill target_inst by blast
      next
        assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> ?h \<and>
          ?h |_ q1 = Var x \<and> x \<in> vars_term ?h \<and> k = q1 @ q2 \<and>
          q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
          (?h \<cdot> \<sigma>) |_ k = \<sigma> x |_ q2"
        then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> ?h"
          and hq1: "?h |_ q1 = Var x"
          and xh: "x \<in> vars_term ?h"
          and k: "k = q1 @ q2"
          and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
          and sub_t: "(?h \<cdot> \<sigma>) |_ k = \<sigma> x |_ q2"
          by blast
        from lr wf have lhs: "is_Fun l"
          and vars: "vars_term r \<subseteq> vars_term l"
          unfolding wf_trs_def by (cases l, auto)
        have x_r: "x \<in> vars_term r"
          using xh q_poss vars_term_subt_at[OF q_poss] by auto
        from vars x_r have x_l: "x \<in> vars_term l" by auto
        have l_supt_var: "l \<rhd> Var x"
          using lhs x_l supteq_Var[of x l]
          unfolding supt_supteq_conv by (cases l, auto)
        have redex_supt_x: "l \<cdot> \<sigma> \<rhd> \<sigma> x"
          using supt_subst[OF l_supt_var, of \<sigma>] by simp
        have p_poss: "p \<in> poss u"
          using p_active mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
        have u_supteq_redex: "u \<unrhd> l \<cdot> \<sigma>"
          using subt_at_imp_supteq[OF p_poss] redex by simp
        have u_supt_x: "u \<rhd> \<sigma> x"
          using u_supteq_redex redex_supt_x
          by (meson supteq_supt_trans)
        have inactive_x: "\<not> mu_supt \<mu> u (\<sigma> x)"
        proof
          assume active: "mu_supt \<mu> u (\<sigma> x)"
          from uT active have sn_x: "SN_on (csstep \<mu> R) {\<sigma> x}"
            unfolding mu_Tinf_def by auto
          have sn_t: "SN_on (csstep \<mu> R) {t}"
            using SN_on_mu_pos[OF wf
                mu_fun_poss_imp_mu_poss[OF q2] sn_x]
              hk sub_t by simp
          from tT have "\<not> SN_on (csstep \<mu> R) {t}"
            unfolding mu_Tinf_def by auto
          with sn_t show False by contradiction
        qed
        have x_to_t: "\<sigma> x = t \<or> mu_supt \<mu> (\<sigma> x) t"
        proof (cases q2)
          case Nil
          with hk sub_t show ?thesis by simp
        next
          case (Cons i qs)
          have pos: "i # qs \<in> mu_poss \<mu> (\<sigma> x)"
            using q2 Cons mu_fun_poss_imp_mu_poss by blast
          have "\<sigma> x |_ (i # qs) = t"
            using hk sub_t Cons by simp
          with pos show ?thesis
            unfolding mu_supt_def by blast
        qed
        from hp u_supt_x inactive_x x_to_t tT
        obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
          and hidden: "hidden_term_on \<mu> D R h"
          and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
          and th: "t = h \<cdot> \<tau>"
          unfolding has_hiding_property_def by blast
        have outer: "hiding_context_on \<mu> D R (ctxt_of_pos_term q1 ?h)"
          by (rule inactive_rhs_active_context_hiding_claim[
              OF lr q_fun q_inactive refl q1],
              use hq1 in auto)
        have outer_subst:
          "hiding_context_on \<mu> D R (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)"
          by (rule hiding_context_on_subst[OF outer])
        have composed: "hiding_context_on \<mu> D R
            ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)"
          by (rule hiding_context_on_comp[OF outer_subst C])
        have fill_h: "?h = (ctxt_of_pos_term q1 ?h)\<langle>Var x\<rangle>"
          using ctxt_supt_id[OF mu_poss_imp_poss[OF q1]] hq1 by simp
        have fill: "s =
            ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)
              \<langle>h \<cdot> \<tau>\<rangle>"
        proof -
          have "?h \<cdot> \<sigma> =
              ((ctxt_of_pos_term q1 ?h)\<langle>Var x\<rangle>) \<cdot> \<sigma>"
            using fill_h by simp
          also have "... = (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)
              \<langle>\<sigma> x\<rangle>"
          proof -
            have "((ctxt_of_pos_term q1 ?h)\<langle>Var x\<rangle>) \<cdot> \<sigma> =
                (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)
                  \<langle>Var x \<cdot> \<sigma>\<rangle>"
              by (rule subst_apply_term_ctxt_apply_distrib)
            then show ?thesis by simp
          qed
          also have "... = (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)
              \<langle>C\<langle>h \<cdot> \<tau>\<rangle>\<rangle>"
            unfolding sx by simp
          also have "... =
              ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)
                \<langle>h \<cdot> \<tau>\<rangle>"
            by simp
          finally show ?thesis
            unfolding s .
        qed
        show ?thesis
          using composed hidden fill th by blast
      qed
    qed
  qed
qed

lemma csnrsteps_hiding_property_preserve:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and steps: "(u,v) \<in> (csnrstep \<mu> R)\<^sup>*"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    and vT: "v \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "has_hiding_property \<mu> D R (csstep \<mu> R) v"
  using steps hp vT
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y,z) \<in> csstep \<mu> R"
    using step.hyps(2) unfolding csstep_root_nonroot by auto
  from step.prems(2) have notSN_z:
      "\<not> SN_on (csstep \<mu> R) {z}"
    unfolding mu_Tinf_def by auto
  have notSN_y: "\<not> SN_on (csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz notSN_z])
  from step.prems(1) have uT:
      "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  have yT: "y \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[
        OF wf step.hyps(1) uT notSN_y])
  have hp_y: "has_hiding_property \<mu> D R (csstep \<mu> R) y"
    by (rule step.hyps(3)[OF step.prems(1) yT])
  show ?case
    by (rule csstep_hiding_property_preserve[
        OF wf defs yz hp_y step.prems(2)])
qed

lemma inactive_rhs_instance_hiding:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and lr: "(l,r) \<in> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (l \<cdot> \<sigma>)"
    and q_fun: "q \<in> fun_poss r"
    and q_inactive: "q \<notin> mu_fun_poss \<mu> r"
    and st: "(r |_ q) \<cdot> \<sigma> = t \<or>
      mu_supt \<mu> ((r |_ q) \<cdot> \<sigma>) t"
    and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "\<exists>C h \<tau>. hiding_context_on \<mu> D R C \<and>
    hidden_term_on \<mu> D R h \<and>
    (r |_ q) \<cdot> \<sigma> = C\<langle>h \<cdot> \<tau>\<rangle> \<and> t = h \<cdot> \<tau>"
proof -
  let ?h = "r |_ q"
  have q_poss: "q \<in> poss r"
    using q_fun fun_poss_imp_poss by blast
  have h_fun: "is_Fun ?h"
    using fun_poss_fun_conv[OF q_fun] by auto
  from mu_Tinf_defined_root[OF wf tT]
  obtain f ts where t: "t = Fun f ts"
    and f_def: "defined R (f,length ts)" .
  have fD: "(f,length ts) \<in> D"
    using defs f_def by auto
  have t_fun: "is_Fun t" unfolding t by simp
  have k_active: "\<exists>k. k \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>) \<and>
      (?h \<cdot> \<sigma>) |_ k = t"
    using st
  proof
    assume eq: "?h \<cdot> \<sigma> = t"
    have "[] \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>)"
      using h_fun by (cases ?h, auto)
    moreover have "(?h \<cdot> \<sigma>) |_ [] = t" using eq by simp
    ultimately show ?thesis by blast
  next
    assume active: "mu_supt \<mu> (?h \<cdot> \<sigma>) t"
    then obtain i k where pos: "i # k \<in> mu_poss \<mu> (?h \<cdot> \<sigma>)"
      and sub: "(?h \<cdot> \<sigma>) |_ (i # k) = t"
      unfolding mu_supt_def by auto
    have fun_pos: "i # k \<in> fun_poss (?h \<cdot> \<sigma>)"
      by (rule poss_is_Fun_fun_poss[
          OF mu_poss_imp_poss[OF pos] t_fun[unfolded sub[symmetric]]])
    have active': "i # k \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>)"
      by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF pos fun_pos])
    show ?thesis
      by (rule exI[of _ "i # k"], use active' sub in auto)
  qed
  then obtain k where k_active: "k \<in> mu_fun_poss \<mu> (?h \<cdot> \<sigma>)"
    and hk: "(?h \<cdot> \<sigma>) |_ k = t" by blast
  from mu_fun_poss_subst_cases_aux_mu[OF k_active]
  show ?thesis
  proof
    assume orig: "k \<in> mu_fun_poss \<mu> ?h \<and>
      (?h \<cdot> \<sigma>) |_ k = (?h |_ k) \<cdot> \<sigma>"
    have k_h: "k \<in> mu_fun_poss \<mu> ?h" using orig by auto
    have target: "root (?h |_ k) \<in> Some ` D"
    proof -
      from k_h obtain g us where base: "?h |_ k = Fun g us"
        using mu_fun_poss_imp_fun_poss fun_poss_fun_conv by blast
      from hk orig t base have g: "g = f" and len: "length us = length ts"
        by auto
      show ?thesis unfolding base using fD g len by auto
    qed
    have hidden: "hidden_term_on \<mu> D R (?h |_ k)"
      by (rule inactive_rhs_active_defined_hidden_claim[
          OF lr q_fun q_inactive refl k_h target])
    have C: "hiding_context_on \<mu> D R (ctxt_of_pos_term k ?h)"
      by (rule inactive_rhs_active_context_hiding_claim[
          OF lr q_fun q_inactive refl mu_fun_poss_imp_mu_poss[OF k_h]],
          use target in auto)
    have C_subst:
      "hiding_context_on \<mu> D R (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)"
      by (rule hiding_context_on_subst[OF C])
    have k_poss: "k \<in> poss ?h"
      using k_h mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
    have fill_h: "?h = (ctxt_of_pos_term k ?h)\<langle>?h |_ k\<rangle>"
      using ctxt_supt_id[OF k_poss] by simp
    have fill: "?h \<cdot> \<sigma> =
        (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)
          \<langle>(?h |_ k) \<cdot> \<sigma>\<rangle>"
    proof -
      have "?h \<cdot> \<sigma> =
          ((ctxt_of_pos_term k ?h)\<langle>?h |_ k\<rangle>) \<cdot> \<sigma>"
        using fill_h by simp
      also have "... = (ctxt_of_pos_term k ?h \<cdot>\<^sub>c \<sigma>)
          \<langle>(?h |_ k) \<cdot> \<sigma>\<rangle>"
        by (rule subst_apply_term_ctxt_apply_distrib)
      finally show ?thesis .
    qed
    have target_inst: "t = (?h |_ k) \<cdot> \<sigma>"
      using hk orig by auto
    show ?thesis using C_subst hidden fill target_inst by blast
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> ?h \<and>
      ?h |_ q1 = Var x \<and> x \<in> vars_term ?h \<and> k = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
      (?h \<cdot> \<sigma>) |_ k = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> ?h"
      and hq1: "?h |_ q1 = Var x" and xh: "x \<in> vars_term ?h"
      and k: "k = q1 @ q2" and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_t: "(?h \<cdot> \<sigma>) |_ k = \<sigma> x |_ q2" by blast
    from lr wf have lhs: "is_Fun l"
      and vars: "vars_term r \<subseteq> vars_term l"
      unfolding wf_trs_def by (cases l, auto)
    have x_r: "x \<in> vars_term r"
      using xh q_poss vars_term_subt_at[OF q_poss] by auto
    from vars x_r have x_l: "x \<in> vars_term l" by auto
    have l_supt_var: "l \<rhd> Var x"
      using lhs x_l supteq_Var[of x l]
      unfolding supt_supteq_conv by (cases l, auto)
    have source_supt_x: "l \<cdot> \<sigma> \<rhd> \<sigma> x"
      using supt_subst[OF l_supt_var, of \<sigma>] by simp
    from hp have sourceT: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      unfolding has_hiding_property_def by auto
    have inactive_x: "\<not> mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
    proof
      assume active: "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
      from sourceT active have sn_x: "SN_on (csstep \<mu> R) {\<sigma> x}"
        unfolding mu_Tinf_def by auto
      have sn_t: "SN_on (csstep \<mu> R) {t}"
        using SN_on_mu_pos[OF wf mu_fun_poss_imp_mu_poss[OF q2] sn_x]
          hk sub_t by simp
      from tT have "\<not> SN_on (csstep \<mu> R) {t}"
        unfolding mu_Tinf_def by auto
      with sn_t show False by contradiction
    qed
    have x_to_t: "\<sigma> x = t \<or> mu_supt \<mu> (\<sigma> x) t"
    proof (cases q2)
      case Nil
      with hk sub_t show ?thesis by simp
    next
      case (Cons i qs)
      have pos: "i # qs \<in> mu_poss \<mu> (\<sigma> x)"
        using q2 Cons mu_fun_poss_imp_mu_poss by blast
      have "\<sigma> x |_ (i # qs) = t" using hk sub_t Cons by simp
      with pos show ?thesis unfolding mu_supt_def by blast
    qed
    from hp source_supt_x inactive_x x_to_t tT
    obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
      and hidden: "hidden_term_on \<mu> D R h"
      and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
      and th: "t = h \<cdot> \<tau>"
      unfolding has_hiding_property_def by blast
    have outer: "hiding_context_on \<mu> D R (ctxt_of_pos_term q1 ?h)"
      by (rule inactive_rhs_active_context_hiding_claim[
          OF lr q_fun q_inactive refl q1], use hq1 in auto)
    have outer_subst:
      "hiding_context_on \<mu> D R (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)"
      by (rule hiding_context_on_subst[OF outer])
    have composed: "hiding_context_on \<mu> D R
        ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)"
      by (rule hiding_context_on_comp[OF outer_subst C])
    have fill_h: "?h = (ctxt_of_pos_term q1 ?h)\<langle>Var x\<rangle>"
      using ctxt_supt_id[OF mu_poss_imp_poss[OF q1]] hq1 by simp
    have fill: "?h \<cdot> \<sigma> =
        ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)
          \<langle>h \<cdot> \<tau>\<rangle>"
    proof -
      have "?h \<cdot> \<sigma> =
          ((ctxt_of_pos_term q1 ?h)\<langle>Var x\<rangle>) \<cdot> \<sigma>"
        using fill_h by simp
      also have "... = (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)
          \<langle>Var x \<cdot> \<sigma>\<rangle>"
        by (rule subst_apply_term_ctxt_apply_distrib)
      also have "... = (ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>)
          \<langle>C\<langle>h \<cdot> \<tau>\<rangle>\<rangle>"
        using sx by simp
      also have "... =
          ((ctxt_of_pos_term q1 ?h \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C)
            \<langle>h \<cdot> \<tau>\<rangle>" by simp
      finally show ?thesis .
    qed
    show ?thesis using composed hidden fill th by blast
  qed
qed

lemma csrstep_hiding_property_active_target:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and active: "t = w \<or> mu_supt \<mu> t w"
    and wT: "w \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "has_hiding_property \<mu> D R (csstep \<mu> R) w"
proof -
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from mu_Tinf_defined_root[OF wf wT]
  obtain wf0 ws where w: "w = Fun wf0 ws"
    and w_def: "defined R (wf0,length ws)" .
  have w_fun: "is_Fun w" unfolding w by simp
  show ?thesis
    unfolding has_hiding_property_def
  proof (intro conjI allI impI)
    show "w \<in> mu_Tinf \<mu> (csstep \<mu> R)" by (rule wT)
  next
    fix a b
    assume wa: "w \<rhd> a"
      and inactive_a: "\<not> mu_supt \<mu> w a"
      and ab: "a = b \<or> mu_supt \<mu> a b"
      and bT: "b \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    from mu_Tinf_defined_root[OF wf bT]
    obtain bf bs where b: "b = Fun bf bs"
      and b_def: "defined R (bf,length bs)" .
    have b_fun: "is_Fun b" unfolding b by simp
    have a_fun: "is_Fun a"
      using ab b_fun unfolding mu_supt_def by (cases a, auto)
    show "\<exists>C h \<tau>. hiding_context_on \<mu> D R C \<and>
      hidden_term_on \<mu> D R h \<and> a = C\<langle>h \<cdot> \<tau>\<rangle> \<and> b = h \<cdot> \<tau>"
    proof (cases "s \<rhd> a")
      case True
      have inactive_s: "\<not> mu_supt \<mu> s a"
      proof
        assume active_sa: "mu_supt \<mu> s a"
        from sT active_sa have sn_a: "SN_on (csstep \<mu> R) {a}"
          unfolding mu_Tinf_def by auto
        have sn_b: "SN_on (csstep \<mu> R) {b}"
          using ab
        proof
          assume "a = b"
          with sn_a show ?thesis by simp
        next
          assume active_ab: "mu_supt \<mu> a b"
          then obtain i q where pos: "i # q \<in> mu_poss \<mu> a"
            and sub: "a |_ (i # q) = b"
            unfolding mu_supt_def by auto
          show ?thesis using SN_on_mu_pos[OF wf pos sn_a] sub by simp
        qed
        from bT have "\<not> SN_on (csstep \<mu> R) {b}"
          unfolding mu_Tinf_def by auto
        with sn_b show False by contradiction
      qed
      from hp True inactive_s ab bT
      show ?thesis unfolding has_hiding_property_def by blast
    next
      case False
      have p_w: "\<exists>p. p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>) \<and>
          (r \<cdot> \<sigma>) |_ p = w"
        using active
      proof
        assume "t = w"
        then have eq: "r \<cdot> \<sigma> = w" unfolding t .
        have "[] \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
          using w_fun eq by (cases "r \<cdot> \<sigma>", auto)
        moreover have "(r \<cdot> \<sigma>) |_ [] = w" using eq by simp
        ultimately show ?thesis by blast
      next
        assume tw: "mu_supt \<mu> t w"
        then obtain i p where pos: "i # p \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
          and sub: "(r \<cdot> \<sigma>) |_ (i # p) = w"
          unfolding t mu_supt_def by auto
        have fun_pos: "i # p \<in> fun_poss (r \<cdot> \<sigma>)"
          by (rule poss_is_Fun_fun_poss[
              OF mu_poss_imp_poss[OF pos] w_fun[unfolded sub[symmetric]]])
        have active': "i # p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
          by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF pos fun_pos])
        show ?thesis by (rule exI[of _ "i # p"], use active' sub in auto)
      qed
      then obtain p where p_active: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
        and rp: "(r \<cdot> \<sigma>) |_ p = w" by blast
      from supt_imp_subt_at_nepos[OF wa]
      obtain i q where iq_poss: "i # q \<in> poss w"
        and iq_sub: "w |_ (i # q) = a" by blast
      let ?q = "i # q"
      have q_fun: "?q \<in> fun_poss w"
        by (rule poss_is_Fun_fun_poss[OF iq_poss a_fun[unfolded iq_sub[symmetric]]])
      have q_inactive: "?q \<notin> mu_fun_poss \<mu> w"
      proof
        assume q_active: "?q \<in> mu_fun_poss \<mu> w"
        have "mu_supt \<mu> w a"
          unfolding mu_supt_def
          using mu_fun_poss_imp_mu_poss[OF q_active] iq_sub by blast
        with inactive_a show False by contradiction
      qed
      have p_poss: "p \<in> poss (r \<cdot> \<sigma>)"
        using p_active mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
      have pq_poss: "p @ ?q \<in> poss (r \<cdot> \<sigma>)"
        using p_poss iq_poss rp unfolding poss_append_poss by auto
      have pq_sub: "(r \<cdot> \<sigma>) |_ (p @ ?q) = a"
        using p_poss rp iq_sub by (simp add: subt_at_append)
      have pq_inactive: "p @ ?q \<notin> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
      proof
        assume pq_active: "p @ ?q \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
        have "?q \<in> mu_fun_poss \<mu> ((r \<cdot> \<sigma>) |_ p)"
          by (rule mu_fun_poss_append_suffix[OF pq_active p_poss])
        with q_inactive rp show False by simp
      qed
      from poss_subst_choice[OF pq_poss]
      show ?thesis
      proof
        assume orig: "p @ ?q \<in> poss r \<and> is_Fun (r |_ (p @ ?q))"
        have base_fun: "p @ ?q \<in> fun_poss r"
          by (rule poss_is_Fun_fun_poss, use orig in auto)
        have base_inst: "a = (r |_ (p @ ?q)) \<cdot> \<sigma>"
          using pq_sub orig by simp
        have base_inactive: "p @ ?q \<notin> mu_fun_poss \<mu> r"
        proof
          assume base_active: "p @ ?q \<in> mu_fun_poss \<mu> r"
          from mu_fun_poss_subst_lift[OF base_active, of \<sigma>]
          pq_inactive show False by contradiction
        qed
        have st': "(r |_ (p @ ?q)) \<cdot> \<sigma> = b \<or>
            mu_supt \<mu> ((r |_ (p @ ?q)) \<cdot> \<sigma>) b"
          using ab base_inst by simp
        from inactive_rhs_instance_hiding[
            OF wf defs lr hp[unfolded s] base_fun base_inactive st' bT]
        show ?thesis using base_inst by blast
      next
        assume subst_case: "\<exists>x q1 q2. q1 \<in> poss r \<and>
          q2 \<in> poss (\<sigma> x) \<and> r |_ q1 = Var x \<and>
          x \<in> vars_term r \<and> p @ ?q = q1 @ q2 \<and>
          (r \<cdot> \<sigma>) |_ (p @ ?q) = \<sigma> x |_ q2"
        then obtain x q1 q2 where q2: "q2 \<in> poss (\<sigma> x)"
          and x_r: "x \<in> vars_term r"
          and sub_a: "(r \<cdot> \<sigma>) |_ (p @ ?q) = \<sigma> x |_ q2"
          by blast
        from vars x_r have x_l: "x \<in> vars_term l" by auto
        have l_supt_var: "l \<rhd> Var x"
          using lhs x_l supteq_Var[of x l]
          unfolding supt_supteq_conv by (cases l, auto)
        have source_supt_x: "l \<cdot> \<sigma> \<rhd> \<sigma> x"
          using supt_subst[OF l_supt_var, of \<sigma>] by simp
        have xa: "\<sigma> x \<unrhd> a"
          using subt_at_imp_supteq[OF q2] sub_a pq_sub by simp
        have "s \<rhd> a"
          unfolding s using source_supt_x xa
          by (meson supt_supteq_trans)
        with False show ?thesis by contradiction
      qed
    qed
  qed
qed

lemma inactive_rhs_active_context_hiding:
  assumes lr: "(l,r) \<in> R"
    and p_fun: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss \<mu> r"
    and sub: "r |_ p = h"
    and q: "q \<in> mu_poss \<mu> h"
    and target: "is_Var (h |_ q) \<or> root (h |_ q) \<in> Some ` D"
  shows "hiding_context_on \<mu> D R (ctxt_of_pos_term q h)"
  using p_fun inactive sub q target
proof (induct q arbitrary: h p)
  case Nil
  show ?case by (simp, rule hiding_context_on.hole)
next
  case (Cons i q)
  note p_fun = Cons.prems(1)
  note inactive = Cons.prems(2)
  note sub = Cons.prems(3)
  from Cons.prems(4) obtain f ts where
    h: "h = Fun f ts"
    and i: "i < length ts" "i \<in> \<mu> (f,length ts)"
    and q_mu: "q \<in> mu_poss \<mu> (ts ! i)"
    by (cases h) auto
  have target':
    "is_Var ((ts ! i) |_ q) \<or> root ((ts ! i) |_ q) \<in> Some ` D"
    using Cons.prems(5) i unfolding h by simp
  have sub_fun: "r |_ p = Fun f ts"
    by (rule HOL.trans[OF sub h])
  have hide: "hides_position_on \<mu> D R (f,length ts) i"
    unfolding hides_position_on_def
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p_fun inactive sub_fun i q_mu target' by auto
  have tail: "hiding_context_on \<mu> D R
      (ctxt_of_pos_term q (ts ! i))"
  proof (cases q)
    case Nil
    have "hiding_context_on \<mu> D R \<box>"
      by (rule hiding_context_on.hole)
    then show ?thesis unfolding Nil by simp
  next
    case (Cons j qs)
    have iq_poss: "i # q \<in> poss h"
      using i q_mu mu_poss_imp_poss unfolding h by auto
    have p_poss: "p \<in> poss r"
      using p_fun fun_poss_imp_poss by blast
    have piq_poss: "p @ (i # q) \<in> poss r"
      using p_poss iq_poss sub
      unfolding poss_append_poss by auto
    have q_ne: "q \<noteq> []"
      unfolding Cons by simp
    have pi_q_poss: "(p @ [i]) @ q \<in> poss r"
      using piq_poss by simp
    have pi_fun: "p @ [i] \<in> fun_poss r"
      by (rule fun_poss_append_poss[OF pi_q_poss q_ne])
    have pi_inactive: "p @ [i] \<notin> mu_fun_poss \<mu> r"
    proof
      assume active: "p @ [i] \<in> mu_fun_poss \<mu> r"
      have p_mu: "p \<in> mu_poss \<mu> r"
        by (rule mu_fun_poss_append_prefix[OF active])
      have "p \<in> mu_fun_poss \<mu> r"
        by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF p_mu p_fun])
      with inactive show False by contradiction
    qed
    have pi_sub: "r |_ (p @ [i]) = ts ! i"
      using sub i p_poss unfolding h
      by (simp add: subt_at_append)
    show ?thesis
      by (rule Cons.hyps[
          OF pi_fun pi_inactive pi_sub q_mu target'])
  qed
  show ?case
    unfolding h ctxt_of_pos_term.simps
    by (rule hiding_context_on.more[OF _ tail], use hide i in simp)
qed

lemma collapsing_mu_CSDP_onI:
  assumes "(l,r) \<in> R"
    and "x \<in> mu_vars_term \<mu> r"
    and "x \<notin> mu_vars_term \<mu> l"
  shows "(sharp_term shp l, Fun U [Var x]) \<in> collapsing_mu_CSDP_on shp U \<mu> R"
  using assms unfolding collapsing_mu_CSDP_on_def by blast

lemma hidden_mu_CSDP_onI:
  assumes "hidden_term_on \<mu> D R t"
  shows "(Fun U [t], sharp_term shp t) \<in> hidden_mu_CSDP_on shp U \<mu> D R"
  using assms unfolding hidden_mu_CSDP_on_def by blast

lemma improved_mu_CSDP_on_mu:
  "mu_CSDP_on shp \<mu> D R \<subseteq> improved_mu_CSDP_on shp U \<mu> D R"
  unfolding improved_mu_CSDP_on_def by auto

lemma improved_mu_CSDP_on_collapsing:
  "collapsing_mu_CSDP_on shp U \<mu> R \<subseteq> improved_mu_CSDP_on shp U \<mu> D R"
  unfolding improved_mu_CSDP_on_def by auto

lemma improved_mu_CSDP_on_hidden:
  "hidden_mu_CSDP_on shp U \<mu> D R \<subseteq> improved_mu_CSDP_on shp U \<mu> D R"
  unfolding improved_mu_CSDP_on_def by auto

definition improved_csdp_coverage ::
  "('f::{showl, compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow>
    'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "improved_csdp_coverage shp U \<mu> D R P \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    collapsing_mu_CSDP_on shp U \<mu> R \<subseteq> P \<and>
    hidden_mu_CSDP_on shp U \<mu> D R \<subseteq> P \<and>
    (\<forall>f ts i. hides_position_on \<mu> D R (f,length ts) i \<longrightarrow>
      i < length ts \<longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rrstep P)"

lemma improved_csdp_coverage_mu:
  assumes "improved_csdp_coverage shp U \<mu> D R P"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding improved_csdp_coverage_def by auto

lemma improved_csdp_coverage_collapsing:
  assumes "improved_csdp_coverage shp U \<mu> D R P"
  shows "collapsing_mu_CSDP_on shp U \<mu> R \<subseteq> P"
  using assms unfolding improved_csdp_coverage_def by auto

lemma improved_csdp_coverage_hidden:
  assumes "improved_csdp_coverage shp U \<mu> D R P"
  shows "hidden_mu_CSDP_on shp U \<mu> D R \<subseteq> P"
  using assms unfolding improved_csdp_coverage_def by auto

lemma hiding_context_unhides:
  assumes cover: "improved_csdp_coverage shp U \<mu> D R P"
    and C: "hiding_context_on \<mu> D R C"
  shows "(Fun U [C\<langle>t\<rangle>], Fun U [t]) \<in> (rrstep P)\<^sup>*"
  using C
proof (induct rule: hiding_context_on.induct)
  case hole
  then show ?case by simp
next
  case (more f bef aft C)
  let ?whole = "Fun f (bef @ C\<langle>t\<rangle> # aft)"
  have i: "length bef < length (bef @ C\<langle>t\<rangle> # aft)"
    by simp
  have nth: "(bef @ C\<langle>t\<rangle> # aft) ! length bef = C\<langle>t\<rangle>"
    by simp
  have hide: "hides_position_on \<mu> D R
      (f,length (bef @ C\<langle>t\<rangle> # aft)) (length bef)"
    using more.hyps(1) by simp
  from cover[unfolded improved_csdp_coverage_def]
  have projections: "\<And>f ts i. hides_position_on \<mu> D R (f,length ts) i \<Longrightarrow>
    i < length ts \<Longrightarrow> (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rrstep P"
    by blast
  from projections[OF hide i] nth have step:
    "(Fun U [?whole], Fun U [C\<langle>t\<rangle>]) \<in> rrstep P"
    by simp
  from step more.hyps(3) show ?case
    by auto
qed

lemma hidden_instance_unhides:
  assumes cover: "improved_csdp_coverage shp U \<mu> D R P"
    and hidden: "hidden_term_on \<mu> D R h"
  shows "(Fun U [h \<cdot> \<sigma>], sharp_term shp (h \<cdot> \<sigma>)) \<in> rrstep P"
proof -
  from hidden_mu_CSDP_onI[OF hidden]
  have pair: "(Fun U [h], sharp_term shp h) \<in> P"
    using improved_csdp_coverage_hidden[OF cover] by blast
  have sharp: "sharp_term shp (h \<cdot> \<sigma>) = sharp_term shp h \<cdot> \<sigma>"
    using hidden_term_on_is_Fun[OF hidden]
    by (cases h, auto)
  show ?thesis
    using pair sharp by auto
qed

lemma collapsing_instance_step:
  assumes cover: "improved_csdp_coverage shp U \<mu> D R P"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), Fun U [\<sigma> x]) \<in> rrstep P"
proof -
  from collapsing_mu_CSDP_onI[OF lr xr xl]
  have pair: "(sharp_term shp l, Fun U [Var x])
    \<in> collapsing_mu_CSDP_on shp U \<mu> R" .
  then have pairP: "(sharp_term shp l, Fun U [Var x]) \<in> P"
    using improved_csdp_coverage_collapsing[OF cover] by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis
    using pairP sharp by auto
qed

lemma collapsing_hiding_path:
  assumes cover: "improved_csdp_coverage shp U \<mu> D R P"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
    and C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
  shows "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp (h \<cdot> \<tau>))
    \<in> (rrstep P)\<^sup>+"
proof -
  have first: "(sharp_term shp (l \<cdot> \<sigma>), Fun U [\<sigma> x]) \<in> rrstep P"
    by (rule collapsing_instance_step[OF cover lr xr xl lhs])
  have middle: "(Fun U [\<sigma> x], Fun U [h \<cdot> \<tau>]) \<in> (rrstep P)\<^sup>*"
    using hiding_context_unhides[OF cover C, of "h \<cdot> \<tau>"] sx by simp
  have last: "(Fun U [h \<cdot> \<tau>], sharp_term shp (h \<cdot> \<tau>)) \<in> rrstep P"
    by (rule hidden_instance_unhides[OF cover hidden])
  from first middle have prefix:
    "(sharp_term shp (l \<cdot> \<sigma>), Fun U [h \<cdot> \<tau>]) \<in> (rrstep P)\<^sup>+"
    by (meson r_into_trancl rtrancl_into_trancl2)
  from prefix last show ?thesis
    by (rule trancl_into_trancl)
qed

lemma csrstep_hiding_rhs_imp_improved_path:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "improved_csdp_coverage shp U \<mu> D R P"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = u \<or> mu_supt \<mu> t u) \<and>
    (sharp_term shp s, sharp_term shp u) \<in> (rrstep P)\<^sup>+"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_rhs: "t = ?u \<or> mu_supt \<mu> t ?u"
  proof (cases p)
    case Nil
    with t show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have "(r \<cdot> \<sigma>) |_ (i # q) = ?u"
      unfolding Cons by simp
    then have "mu_supt \<mu> (r \<cdot> \<sigma>) ?u"
      unfolding mu_supt_def using pos by blast
    with t show ?thesis by simp
  qed
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts"
      by auto
    from defs def len have fD: "(f, length ts) \<in> D"
      by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l"
        using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    have dp0:
      "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp ((r |_ p) \<cdot> \<sigma>))
        \<in> rrstep (mu_CSDP_on shp \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    have mono: "rrstep (mu_CSDP_on shp \<mu> D R) \<subseteq> rrstep P"
      by (rule rrstep_mono[OF improved_csdp_coverage_mu[OF cover]])
    from dp0 mono have
      "(sharp_term shp s, sharp_term shp ?u) \<in> rrstep P"
      unfolding s sub_subst by auto
    with T_p active_rhs show ?thesis by (blast intro: r_into_trancl)
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and x_r: "x \<in> vars_term r"
      and p: "p = q1 @ q2"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2"
      by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs sT[unfolded s] True q2])
      with notSN_p u show ?thesis by simp
    next
      case False
      from vars x_r have x_l: "x \<in> vars_term l" by auto
      from lhs x_l have l_supt_x: "l \<rhd> Var x"
        using supteq_Var[of x l] unfolding supt_supteq_conv
        by (cases l, auto)
      have s_supt_x: "s \<rhd> \<sigma> x"
        using supt_subst[OF l_supt_x, of \<sigma>] unfolding s by simp
      have not_mu_supt_x: "\<not> mu_supt \<mu> s (\<sigma> x)"
      proof
        assume active: "mu_supt \<mu> s (\<sigma> x)"
        from sT active have snx: "SN_on (csstep \<mu> R) {\<sigma> x}"
          unfolding mu_Tinf_def by auto
        have snu: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
          by (rule SN_on_mu_subterm[OF wf q2 snx])
        with notSN_p u show False by simp
      qed
      have active_u: "\<sigma> x = ?u \<or> mu_supt \<mu> (\<sigma> x) ?u"
      proof (cases q2)
        case Nil
        with u show ?thesis by simp
      next
        case (Cons i q)
        from q2 have ip: "i # q \<in> mu_poss \<mu> (\<sigma> x)"
          using mu_fun_poss_imp_mu_poss Cons by blast
        have sub: "\<sigma> x |_ (i # q) = ?u"
          using u Cons by simp
        show ?thesis
          unfolding mu_supt_def using ip sub by blast
      qed
      from hp s_supt_x not_mu_supt_x active_u T_p
      obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
        and hidden: "hidden_term_on \<mu> D R h"
        and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
        and uh: "?u = h \<cdot> \<tau>"
        unfolding has_hiding_property_def by blast
      have path:
        "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp (h \<cdot> \<tau>))
          \<in> (rrstep P)\<^sup>+"
        by (rule collapsing_hiding_path[
              where shp=shp and U=U and \<mu>=\<mu> and D=D and R=R and P=P
                and l=l and r=r and x=x and \<sigma>=\<sigma> and C=C and h=h and \<tau>=\<tau>,
              OF cover lr xr_mu False lhs C hidden sx])
      with T_p active_rhs show ?thesis
        unfolding s uh by blast
    qed
  qed
qed

lemma hiding_imp_improved_relstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) t"
    and cover: "improved_csdp_coverage shp U \<mu> D R P"
  shows "\<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
    (sharp_term shp t, sharp_term shp u) \<in>
      (rstep R)\<^sup>* O (rrstep P)\<^sup>+ O (rstep R)\<^sup>*"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}"
    by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    by (rule csnrsteps_hiding_property_preserve[OF wf defs pref hp sT])
  from csrstep_hiding_rhs_imp_improved_path[
      OF wf root hp_s notSN_v defs cover]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "v = u \<or> mu_supt \<mu> v u"
    and pair_path:
      "(sharp_term shp s, sharp_term shp u) \<in> (rrstep P)\<^sup>+"
    by blast
  have hp_u: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    by (rule csrstep_hiding_property_active_target[
        OF wf defs root hp_s active uT])
  have prefix: "(sharp_term shp t, sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have suffix: "(sharp_term shp u, sharp_term shp u) \<in> (rstep R)\<^sup>*"
    by simp
  show ?thesis using hp_u prefix pair_path suffix by blast
qed

theorem finite_improved_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "improved_csdp_coverage shp U \<mu> D R P"
    and fin: "finite_dpp (False, False, P, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_hiding_property \<mu> D R (csstep \<mu> R) t0"
    by (rule Tinf_has_hiding_property[OF t0_T])
  let ?A = "(rstep R)\<^sup>* O rrstep P O (rstep R)\<^sup>*"
  let ?B = "(rstep R)\<^sup>* O (rrstep P)\<^sup>+ O (rstep R)\<^sup>*"
  have step_ex: "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term shp t, sharp_term shp u) \<in> ?B"
    by (rule hiding_imp_improved_relstep[OF wf defs _ cover])
  have all_ex: "\<forall>t. \<exists>u.
      has_hiding_property \<mu> D R (csstep \<mu> R) t \<longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term shp t, sharp_term shp u) \<in> ?B"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt:
    "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) (nxt t) \<and>
      (sharp_term shp t, sharp_term shp (nxt t)) \<in> ?B"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step:
      "(sharp_term shp (ts n), sharp_term shp (ts (Suc n))) \<in> ?B"
    for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?B"
    unfolding f_def using ts_step by simp
  have B_sub: "?B \<subseteq> ?A\<^sup>+"
    by regexp
  have not_A_trancl: "\<not> SN (?A\<^sup>+)"
  proof -
    have "\<not> SN ?B"
      unfolding SN_defs using chain by blast
    then show ?thesis
      using SN_subset[of "?A\<^sup>+" ?B] B_sub by blast
  qed
  have sn_A: "SN ?A"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def
    by simp
  have "SN (?A\<^sup>+)"
    by (rule SN_imp_SN_trancl[OF sn_A])
  with not_A_trancl show False by contradiction
qed

definition conservative_csdp_coverage ::
  "('f::{showl, compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow>
    'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "conservative_csdp_coverage shp U \<mu> D R P S \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    collapsing_mu_CSDP_on shp U \<mu> R \<subseteq> P \<and>
    R \<subseteq> S \<and>
    (\<forall>f ts i. i < length ts \<longrightarrow> i \<in> \<mu> (f, length ts) \<longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S) \<and>
    (\<forall>f ts. (f, length ts) \<in> D \<longrightarrow>
      (Fun U [Fun f ts], sharp_term shp (Fun f ts)) \<in> rstep S)"

lemma conservative_csdp_coverage_mu:
  assumes "conservative_csdp_coverage shp U \<mu> D R P S"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding conservative_csdp_coverage_def by auto

lemma conservative_csdp_coverage_collapsing:
  assumes "conservative_csdp_coverage shp U \<mu> D R P S"
  shows "collapsing_mu_CSDP_on shp U \<mu> R \<subseteq> P"
  using assms unfolding conservative_csdp_coverage_def by auto

lemma conservative_csdp_coverage_rules:
  assumes "conservative_csdp_coverage shp U \<mu> D R P S"
  shows "R \<subseteq> S"
  using assms unfolding conservative_csdp_coverage_def by auto

lemma active_path_unhides:
  assumes cover: "conservative_csdp_coverage shp U \<mu> D R P S"
    and p: "p \<in> mu_fun_poss \<mu> t"
  shows "(Fun U [t], Fun U [t |_ p]) \<in> (rstep S)\<^sup>*"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis by simp
  next
    case (Cons i q)
    from Fun.prems[unfolded Cons]
    have i: "i < length ts" "i \<in> \<mu> (f, length ts)"
      and q: "q \<in> mu_fun_poss \<mu> (ts ! i)"
      by auto
    from cover[unfolded conservative_csdp_coverage_def]
    have projections: "\<And>f ts i. i < length ts \<Longrightarrow> i \<in> \<mu> (f, length ts) \<Longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
      by blast
    have first: "(Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
      by (rule projections[OF i])
    have rest: "(Fun U [ts ! i], Fun U [ts ! i |_ q]) \<in> (rstep S)\<^sup>*"
      by (rule Fun.hyps[OF nth_mem[OF i(1)] q])
    from first rest have
      "(Fun U [Fun f ts], Fun U [ts ! i |_ q]) \<in> (rstep S)\<^sup>*"
      by auto
    then show ?thesis
      unfolding Cons using i by simp
  qed
qed

lemma conservative_defined_mark:
  assumes cover: "conservative_csdp_coverage shp U \<mu> D R P S"
    and fD: "(f, length ts) \<in> D"
  shows "(Fun U [Fun f ts], sharp_term shp (Fun f ts)) \<in> rstep S"
  using cover fD unfolding conservative_csdp_coverage_def by blast

lemma conservative_collapsing_instance_step:
  assumes cover: "conservative_csdp_coverage shp U \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), Fun U [\<sigma> x]) \<in> rrstep P"
proof -
  have pair: "(sharp_term shp l, Fun U [Var x])
      \<in> collapsing_mu_CSDP_on shp U \<mu> R"
    by (rule collapsing_mu_CSDP_onI[OF lr xr xl])
  then have pairP: "(sharp_term shp l, Fun U [Var x]) \<in> P"
    using conservative_csdp_coverage_collapsing[OF cover] by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis
    using pairP sharp by auto
qed

lemma csrstep_mu_Tinf_rhs_imp_conservative_relstep:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "conservative_csdp_coverage shp U \<mu> D R P S"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (sharp_term shp s, sharp_term shp u)
      \<in> (rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      ?u = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts"
      by auto
    from defs def len have fD: "(f, length ts) \<in> D"
      by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l"
        using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    have dp0:
      "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp ((r |_ p) \<cdot> \<sigma>))
        \<in> rrstep (mu_CSDP_on shp \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    have mono: "rrstep (mu_CSDP_on shp \<mu> D R) \<subseteq> rrstep P"
      by (rule rrstep_mono[OF conservative_csdp_coverage_mu[OF cover]])
    from dp0 mono have dp:
      "(sharp_term shp s, sharp_term shp ?u) \<in> rrstep P"
      unfolding s sub_subst by auto
    have refl1: "(sharp_term shp s, sharp_term shp s) \<in> (rstep S)\<^sup>*"
      by simp
    have refl2: "(sharp_term shp ?u, sharp_term shp ?u) \<in> (rstep S)\<^sup>*"
      by simp
    with T_p dp refl1 show ?thesis by blast
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2"
      by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs sT[unfolded s] True q2])
      with notSN_p u show ?thesis by simp
    next
      case False
      have dp: "(sharp_term shp s, Fun U [\<sigma> x]) \<in> rrstep P"
        unfolding s
        by (rule conservative_collapsing_instance_step[OF cover lr xr_mu False lhs])
      have projections: "(Fun U [\<sigma> x], Fun U [?u]) \<in> (rstep S)\<^sup>*"
        using active_path_unhides[OF cover q2] u by simp
      from defs def have fD: "(f, length us) \<in> D"
        by auto
      have mark: "(Fun U [?u], sharp_term shp ?u) \<in> rstep S"
        using conservative_defined_mark[OF cover fD] sub_inst by simp
      from projections mark have suffix:
        "(Fun U [\<sigma> x], sharp_term shp ?u) \<in> (rstep S)\<^sup>*"
        by auto
      have prefix: "(sharp_term shp s, sharp_term shp s) \<in> (rstep S)\<^sup>*"
        by simp
      with T_p dp suffix show ?thesis by blast
    qed
  qed
qed

lemma mu_Tinf_imp_conservative_relstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "conservative_csdp_coverage shp U \<mu> D R P S"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (sharp_term shp t, sharp_term shp u)
      \<in> (rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
proof -
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}"
    by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  from csrstep_mu_Tinf_rhs_imp_conservative_relstep[
      OF wf root sT notSN_v defs cover]
  obtain u a b where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and sa: "(sharp_term shp s,a) \<in> (rstep S)\<^sup>*"
    and ab: "(a,b) \<in> rrstep P"
    and bu: "(b,sharp_term shp u) \<in> (rstep S)\<^sup>*"
    by blast
  have prefR: "(sharp_term shp t, sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have rmono: "rstep R \<subseteq> rstep S"
    by (rule rstep_mono[OF conservative_csdp_coverage_rules[OF cover]])
  have prefS: "(sharp_term shp t, sharp_term shp s) \<in> (rstep S)\<^sup>*"
    using prefR rtrancl_mono[OF rmono] by blast
  have ta: "(sharp_term shp t,a) \<in> (rstep S)\<^sup>*"
    by (rule rtrancl_trans[OF prefS sa])
  with uT ab bu show ?thesis by blast
qed

lemma finite_conservative_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "conservative_csdp_coverage shp U \<mu> D R P S"
    and fin: "finite_dpp (False, False, P, {}, {}, {}, S)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  let ?PS = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  have step_ex: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
      (sharp_term shp t, sharp_term shp u) \<in> ?PS"
    by (rule mu_Tinf_imp_conservative_relstep[OF wf _ defs cover])
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<longrightarrow>
    u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
      (sharp_term shp t, sharp_term shp u) \<in> ?PS"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    nxt t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
      (sharp_term shp t, sharp_term shp (nxt t)) \<in> ?PS"
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
    then show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n), sharp_term shp (ts (Suc n))) \<in> ?PS"
    for n
  proof -
    from nxt[OF ts_T[of n]]
    have "(sharp_term shp (ts n), sharp_term shp (nxt (ts n))) \<in> ?PS"
      by simp
    then show ?thesis unfolding ts_def by simp
  qed
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?PS"
    unfolding f_def using ts_step by simp
  have not_rel: "\<not> SN_rel (rrstep P) (rstep S)"
    unfolding SN_rel_on_def SN_defs using chain by blast
  have rel: "SN_rel (rrstep P) (rstep S)"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  from not_rel rel show False by contradiction
qed

definition conservative_projection_rules_list ::
  "'f \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, string) rules"
where
  "conservative_projection_rules_list U \<mu> F =
    concat (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]) F)"

definition conservative_marking_rules_list ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, string) rules"
where
  "conservative_marking_rules_list shp U D =
    map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in (Fun U [Fun f xs], sharp_term shp (Fun f xs))) D"

definition collapsing_mu_CSDP_list ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow> 'f muL \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "collapsing_mu_CSDP_list shp U \<mu> R =
    concat (map (\<lambda>(l,r).
      map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
        [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
          x \<notin> set (mu_vars_term_list \<mu> l)]) R)"

definition hidden_mu_CSDP_list ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow> 'f muL \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "hidden_mu_CSDP_list shp U \<mu> D R =
    concat (map (\<lambda>(l,r).
      map (\<lambda>p. (Fun U [r |_ p], sharp_term shp (r |_ p)))
        [p \<leftarrow> fun_poss_list r.
          p \<notin> set (mu_fun_poss_list \<mu> r) \<and>
          root (r |_ p) \<in> Some ` set D]) R)"

lemma mu_CSDP_list_split_semantics:
  "set (mu_CSDP_list Sharp R \<mu> D) =
    CSR_Checker_Base.mu_CSDP_on Sharp (mu_of \<mu>) (set D) (set R)"
  using CSR_Checker_Base.mu_CSDP_list[of Sharp R \<mu> D]
  by simp

lemma collapsing_mu_CSDP_list:
  "set (collapsing_mu_CSDP_list shp U \<mu> R) =
    collapsing_mu_CSDP_on shp U (mu_of \<mu>) (set R)"
proof (intro equalityI subsetI)
  fix dp
  assume "dp \<in> set (collapsing_mu_CSDP_list shp U \<mu> R)"
  then obtain rs where rs_mem:
      "rs \<in> set (map (\<lambda>(l,r).
        map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
          [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
            x \<notin> set (mu_vars_term_list \<mu> l)]) R)"
    and dp_mem: "dp \<in> set rs"
    unfolding collapsing_mu_CSDP_list_def
    by (simp only: set_concat, blast)
  from rs_mem obtain l r where lr: "(l,r) \<in> set R"
    and rs: "rs = map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
      [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
        x \<notin> set (mu_vars_term_list \<mu> l)]"
    unfolding set_map by (auto split: prod.splits)
  from dp_mem[unfolded rs] obtain x where
    xr: "x \<in> set (mu_vars_term_list \<mu> r)"
    and xl: "x \<notin> set (mu_vars_term_list \<mu> l)"
    and dp: "dp = (sharp_term shp l, Fun U [Var x])"
    by auto
  show "dp \<in> collapsing_mu_CSDP_on shp U (mu_of \<mu>) (set R)"
    unfolding collapsing_mu_CSDP_on_def
    using lr xr xl dp by auto
next
  fix dp
  assume "dp \<in> collapsing_mu_CSDP_on shp U (mu_of \<mu>) (set R)"
  then obtain l r x where lr: "(l,r) \<in> set R"
    and xr: "x \<in> set (mu_vars_term_list \<mu> r)"
    and xl: "x \<notin> set (mu_vars_term_list \<mu> l)"
    and dp: "dp = (sharp_term shp l, Fun U [Var x])"
    unfolding collapsing_mu_CSDP_on_def
    by auto
  let ?rs = "map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
    [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
      x \<notin> set (mu_vars_term_list \<mu> l)]"
  have rs_mem: "?rs \<in> set (map (\<lambda>(l,r).
      map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
        [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
          x \<notin> set (mu_vars_term_list \<mu> l)]) R)"
    unfolding set_map
  proof (rule image_eqI[of _ _ "(l,r)"])
    show "?rs = (case (l,r) of (l,r) \<Rightarrow>
      map (\<lambda>x. (sharp_term shp l, Fun U [Var x]))
        [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
          x \<notin> set (mu_vars_term_list \<mu> l)])"
      by (simp only: case_prod_conv)
    show "(l,r) \<in> set R"
      by (rule lr)
  qed
  have dp_mem: "dp \<in> set ?rs"
    using xr xl dp by auto
  show "dp \<in> set (collapsing_mu_CSDP_list shp U \<mu> R)"
    unfolding collapsing_mu_CSDP_list_def
    using rs_mem dp_mem by (simp only: set_concat, blast)
qed

lemma hidden_mu_CSDP_list:
  "set (hidden_mu_CSDP_list shp U \<mu> D R) =
    hidden_mu_CSDP_on shp U (mu_of \<mu>) (set D) (set R)"
  unfolding hidden_mu_CSDP_list_def hidden_mu_CSDP_on_def
    hidden_term_on_def inactive_fun_subterm_on_def
  by (auto simp: set_concat split: term.splits prod.splits)

definition hides_position_list ::
  "'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "hides_position_list \<mu> D R f n i =
    list_ex (\<lambda>(l,r). list_ex (\<lambda>p.
      p \<notin> set (mu_fun_poss_list \<mu> r) \<and>
      (case r |_ p of
        Var x \<Rightarrow> False
      | Fun g ts \<Rightarrow>
          g = f \<and> length ts = n \<and>
          i < length ts \<and> i \<in> mu_of \<mu> (g,length ts) \<and>
          list_ex (\<lambda>q.
            is_Var ((ts ! i) |_ q) \<or>
            root ((ts ! i) |_ q) \<in> Some ` set D)
            (mu_poss_list \<mu> (ts ! i))))
      (fun_poss_list r)) R"

definition improved_projection_pairs_list ::
  "'f \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, string) rules"
where
  "improved_projection_pairs_list U \<mu> D R =
    concat (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])
      (remdups (funas_trs_list R)))"

lemma hides_position_list:
  "hides_position_list \<mu> D R f n i =
    hides_position_on (mu_of \<mu>) (set D) (set R) (f,n) i"
proof
  assume list: "hides_position_list \<mu> D R f n i"
  from list obtain l r where lr: "(l,r) \<in> set R"
    and inner: "list_ex (\<lambda>p.
      p \<notin> set (mu_fun_poss_list \<mu> r) \<and>
      (case r |_ p of
        Var x \<Rightarrow> False
      | Fun g ts \<Rightarrow>
          g = f \<and> length ts = n \<and>
          i < length ts \<and> i \<in> mu_of \<mu> (g,length ts) \<and>
          list_ex (\<lambda>q.
            is_Var ((ts ! i) |_ q) \<or>
            root ((ts ! i) |_ q) \<in> Some ` set D)
            (mu_poss_list \<mu> (ts ! i))))
      (fun_poss_list r)"
    unfolding hides_position_list_def
    by (auto simp: list_ex_iff split: prod.splits)
  from inner obtain p where p: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss (mu_of \<mu>) r"
    and shape: "(case r |_ p of
        Var x \<Rightarrow> False
      | Fun g ts \<Rightarrow>
          g = f \<and> length ts = n \<and>
          i < length ts \<and> i \<in> mu_of \<mu> (g,length ts) \<and>
          list_ex (\<lambda>q.
            is_Var ((ts ! i) |_ q) \<or>
            root ((ts ! i) |_ q) \<in> Some ` set D)
            (mu_poss_list \<mu> (ts ! i)))"
    by (auto simp: list_ex_iff)
  from shape obtain ts q where sub: "r |_ p = Fun f ts"
    and n: "length ts = n"
    and i: "i < length ts" "i \<in> mu_of \<mu> (f,length ts)"
    and q: "q \<in> mu_poss (mu_of \<mu>) (ts ! i)"
    and target: "is_Var ((ts ! i) |_ q) \<or>
      root ((ts ! i) |_ q) \<in> Some ` set D"
    by (cases "r |_ p") (auto simp: list_ex_iff)
  show "hides_position_on (mu_of \<mu>) (set D) (set R) (f,n) i"
    unfolding hides_position_on_def
    using lr p inactive sub n i q target by blast
next
  assume hide: "hides_position_on (mu_of \<mu>) (set D) (set R) (f,n) i"
  then obtain l r p ts q where
    lr: "(l,r) \<in> set R"
    and p: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss (mu_of \<mu>) r"
    and sub: "r |_ p = Fun f ts"
    and n: "length ts = n"
    and i: "i < length ts" "i \<in> mu_of \<mu> (f,length ts)"
    and q: "q \<in> mu_poss (mu_of \<mu>) (ts ! i)"
    and target: "is_Var ((ts ! i) |_ q) \<or>
      root ((ts ! i) |_ q) \<in> Some ` set D"
    unfolding hides_position_on_def by blast
  show "hides_position_list \<mu> D R f n i"
    unfolding hides_position_list_def
    apply (simp only: list_ex_iff)
    apply (rule bexI[of _ "(l,r)"])
     apply simp
     apply (rule bexI[of _ p])
      using lr p inactive sub n i q target by auto
qed

lemma inactive_rhs_active_defined_hidden:
  assumes lr: "(l,r) \<in> R"
    and p_fun: "p \<in> fun_poss r"
    and inactive: "p \<notin> mu_fun_poss \<mu> r"
    and sub: "r |_ p = h"
    and q: "q \<in> mu_fun_poss \<mu> h"
    and root: "root (h |_ q) \<in> Some ` D"
  shows "hidden_term_on \<mu> D R (h |_ q)"
proof -
  have p_poss: "p \<in> poss r"
    using p_fun fun_poss_imp_poss by blast
  have q_poss: "q \<in> poss h"
    using q mu_fun_poss_imp_mu_poss mu_poss_imp_poss by blast
  have pq_fun: "p @ q \<in> fun_poss r"
  proof -
    have pq_poss: "p @ q \<in> poss r"
      using p_poss q_poss sub unfolding poss_append_poss by auto
    have sub_fun: "is_Fun (h |_ q)"
      using root by (cases "h |_ q") auto
    have "r |_ (p @ q) = h |_ q"
      using p_poss sub by (simp add: subt_at_append)
    then have at_fun: "is_Fun (r |_ (p @ q))"
      using sub_fun by simp
    show ?thesis
      by (rule poss_is_Fun_fun_poss[OF pq_poss at_fun])
  qed
  have pq_inactive: "p @ q \<notin> mu_fun_poss \<mu> r"
  proof
    assume active: "p @ q \<in> mu_fun_poss \<mu> r"
    have p_mu: "p \<in> mu_poss \<mu> r"
      by (rule mu_fun_poss_append_prefix[OF active])
    have "p \<in> mu_fun_poss \<mu> r"
      by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF p_mu p_fun])
    with inactive show False by contradiction
  qed
  have pq_sub: "r |_ (p @ q) = h |_ q"
    using p_poss sub by (simp add: subt_at_append)
  show ?thesis
    unfolding hidden_term_on_def inactive_fun_subterm_on_def
    using root lr pq_fun pq_inactive pq_sub by blast
qed

lemma improved_projection_pairs_list_step:
  assumes fn: "(f,n) \<in> set (remdups (funas_trs_list R))"
    and hide: "hides_position_list \<mu> D R f n i"
    and len: "length ts = n"
    and i: "i < n"
  shows "(Fun U [Fun f ts], Fun U [ts ! i])
    \<in> rrstep (set (improved_projection_pairs_list U \<mu> D R))"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs"
    by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len
    by simp
  have ilen: "i < length ?xs"
    using i fresh by simp
  have nth_inst: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] ilen
    by simp
  let ?ps = "map (\<lambda>i. (Fun U [Fun f ?xs], Fun U [?xs ! i]))
    [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i]"
  have ps_mem: "?ps \<in> set (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])
      (remdups (funas_trs_list R)))"
    unfolding set_map
  proof (rule image_eqI[of _ _ "(f,n)"])
    show "?ps = (case (f,n) of (f,n) \<Rightarrow>
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])"
      by (simp only: Let_def case_prod_conv)
    show "(f,n) \<in> set (remdups (funas_trs_list R))"
      by (rule fn)
  qed
  have pair_mem: "(Fun U [Fun f ?xs], Fun U [?xs ! i]) \<in> set ?ps"
    using i hide by simp
  have pair:
    "(Fun U [Fun f ?xs], Fun U [?xs ! i])
      \<in> set (improved_projection_pairs_list U \<mu> D R)"
    unfolding improved_projection_pairs_list_def
    using ps_mem pair_mem by (simp only: set_concat, blast)
  show ?thesis
  proof (rule rrstepI[OF pair, where \<sigma> = ?\<sigma>])
    show "Fun U [Fun f ts] = Fun U [Fun f ?xs] \<cdot> ?\<sigma>"
      using inst by simp
    show "Fun U [ts ! i] = Fun U [?xs ! i] \<cdot> ?\<sigma>"
      using nth_inst by simp
  qed
qed

lemma hides_position_on_funas:
  assumes hide: "hides_position_on \<mu> D R fn i"
  shows "fn \<in> funas_trs R"
proof -
  from hide obtain l r p f ts where
    lr: "(l,r) \<in> R"
    and p: "p \<in> fun_poss r"
    and sub: "r |_ p = Fun f ts"
    and fn: "fn = (f,length ts)"
    unfolding hides_position_on_def by blast
  have p_poss: "p \<in> poss r"
    using p fun_poss_imp_poss by blast
  have root_mem: "(f,length ts) \<in> funas_term (r |_ p)"
    unfolding sub by simp
  have sub_funas: "funas_term (r |_ p) \<subseteq> funas_term r"
    by (rule supteq_imp_funas_term_subset,
        rule subt_at_imp_supteq[OF p_poss])
  have "(f,length ts) \<in> funas_rule (l,r)"
    using root_mem sub_funas unfolding funas_rule_def by auto
  then show ?thesis
    using lr fn unfolding funas_trs_def by blast
qed

lemma improved_projection_pairs_list_coverage:
  assumes hide: "hides_position_on (mu_of \<mu>) (set D) (set R)
      (f,length ts) i"
    and i: "i < length ts"
  shows "(Fun U [Fun f ts], Fun U [ts ! i])
    \<in> rrstep (set (improved_projection_pairs_list U \<mu> D R))"
proof -
  have fn: "(f,length ts) \<in> set (remdups (funas_trs_list R))"
    using hides_position_on_funas[OF hide] by simp
  have hide_list: "hides_position_list \<mu> D R f (length ts) i"
    by (subst hides_position_list, rule hide)
  show ?thesis
    by (rule improved_projection_pairs_list_step[
        OF fn hide_list refl i])
qed

lemma improved_csr_dependency_pairs_list_coverage:
  assumes mu_pairs:
      "set (mu_CSDP_list Sharp R \<mu> D) \<subseteq> set P"
    and collapsing:
      "set (collapsing_mu_CSDP_list Sharp U \<mu> R) \<subseteq> set P"
    and hidden:
      "set (hidden_mu_CSDP_list Sharp U \<mu> D R) \<subseteq> set P"
    and projections:
      "set (improved_projection_pairs_list U \<mu> D R) \<subseteq> set P"
  shows "improved_csdp_coverage Sharp U (mu_of \<mu>)
    (set D) (set R) (set P)"
proof -
  have mu_cover:
    "mu_CSDP_on Sharp (mu_of \<mu>) (set D) (set R) \<subseteq> set P"
    using mu_pairs unfolding mu_CSDP_list_split_semantics by simp
  have collapsing_cover:
    "collapsing_mu_CSDP_on Sharp U (mu_of \<mu>) (set R) \<subseteq> set P"
    using collapsing unfolding collapsing_mu_CSDP_list by simp
  have hidden_cover:
    "hidden_mu_CSDP_on Sharp U (mu_of \<mu>) (set D) (set R) \<subseteq> set P"
    using hidden unfolding hidden_mu_CSDP_list by simp
  have projection_cover:
    "\<And>f ts i. hides_position_on (mu_of \<mu>) (set D) (set R)
        (f,length ts) i \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rrstep (set P)"
    using improved_projection_pairs_list_coverage[
        where U=U and \<mu>=\<mu> and D=D and R=R]
      rrstep_mono[OF projections] by blast
  show ?thesis
    unfolding improved_csdp_coverage_def
    using mu_cover collapsing_cover hidden_cover projection_cover by blast
qed

lemma conservative_projection_rules_list_step:
  assumes fn: "(f,n) \<in> set F"
    and len: "length ts = n"
    and i: "i < n" "i \<in> mu_of \<mu> (f,n)"
  shows "(Fun U [Fun f ts], Fun U [ts ! i])
    \<in> rstep (set (conservative_projection_rules_list U \<mu> F))"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs"
    by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len
    by simp
  have ilen: "i < length ?xs"
    using i fresh by simp
  have nth_inst: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] ilen
    by simp
  let ?rs = "map (\<lambda>i. (Fun U [Fun f ?xs], Fun U [?xs ! i]))
    [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]"
  have rs_mem: "?rs \<in> set (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]) F)"
    unfolding set_map
  proof (rule image_eqI[of _ _ "(f,n)"])
    show "?rs = (case (f,n) of (f,n) \<Rightarrow>
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun U [Fun f xs], Fun U [xs ! i]))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)])"
      by (simp only: Let_def case_prod_conv)
    show "(f,n) \<in> set F"
      by (rule fn)
  qed
  have pair_mem: "(Fun U [Fun f ?xs], Fun U [?xs ! i]) \<in> set ?rs"
    using i by simp
  have rule:
    "(Fun U [Fun f ?xs], Fun U [?xs ! i])
      \<in> set (conservative_projection_rules_list U \<mu> F)"
    unfolding conservative_projection_rules_list_def
    using rs_mem pair_mem by (simp only: set_concat, blast)
  show ?thesis
  proof (rule rstepI[OF rule, where C = \<box> and \<sigma> = ?\<sigma>])
    show "Fun U [Fun f ts] = \<box>\<langle>Fun U [Fun f ?xs] \<cdot> ?\<sigma>\<rangle>"
      using inst by simp
    show "Fun U [ts ! i] = \<box>\<langle>Fun U [?xs ! i] \<cdot> ?\<sigma>\<rangle>"
      using nth_inst by simp
  qed
qed

lemma conservative_marking_rules_list_step:
  assumes fn: "(f,n) \<in> set D"
    and len: "length ts = n"
  shows "(Fun U [Fun f ts], sharp_term shp (Fun f ts))
    \<in> rstep (set (conservative_marking_rules_list shp U D))"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs"
    by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len
    by simp
  have rule:
    "(Fun U [Fun f ?xs], sharp_term shp (Fun f ?xs))
      \<in> set (conservative_marking_rules_list shp U D)"
    unfolding conservative_marking_rules_list_def set_map
  proof (rule image_eqI[of _ _ "(f,n)"])
    show "(Fun U [Fun f ?xs], sharp_term shp (Fun f ?xs)) =
      (case (f,n) of (f,n) \<Rightarrow>
        let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
        in (Fun U [Fun f xs], sharp_term shp (Fun f xs)))"
      by (simp only: Let_def case_prod_conv)
    show "(f,n) \<in> set D"
      by (rule fn)
  qed
  show ?thesis
  proof (rule rstepI[OF rule, where C = \<box> and \<sigma> = ?\<sigma>])
    show "Fun U [Fun f ts] = \<box>\<langle>Fun U [Fun f ?xs] \<cdot> ?\<sigma>\<rangle>"
      using inst by simp
    show "sharp_term shp (Fun f ts) =
      \<box>\<langle>sharp_term shp (Fun f ?xs) \<cdot> ?\<sigma>\<rangle>"
      using inst by simp
  qed
qed

definition restrict_mu_to_sig :: "'f sig \<Rightarrow> 'f mu \<Rightarrow> 'f mu"
where
  "restrict_mu_to_sig F \<mu> fn = (if fn \<in> F then \<mu> fn else {})"

lemma restrict_mu_to_sig_eq:
  assumes "(f, length ts) \<in> F"
  shows "restrict_mu_to_sig F \<mu> (f, length ts) = \<mu> (f, length ts)"
  using assms unfolding restrict_mu_to_sig_def by simp

lemma csstep_cond_restrict_mu_to_sig:
  assumes sig: "funas_term t \<subseteq> F"
  shows "csstep_cond (restrict_mu_to_sig F \<mu>) p t = csstep_cond \<mu> p t"
proof -
  have roots:
    "\<And>p1 i p2 f ts. p = p1 @ i # p2 \<Longrightarrow> p \<in> poss t \<Longrightarrow>
      t |_ p1 = Fun f ts \<Longrightarrow> (f,length ts) \<in> F"
  proof -
    fix p1 i p2 f ts
    assume p: "p = p1 @ i # p2" "p \<in> poss t"
      and sub: "t |_ p1 = Fun f ts"
    have p1: "p1 \<in> poss t"
      using p by auto
    have "(f,length ts) \<in> funas_term (t |_ p1)"
      unfolding sub by simp
    also have "funas_term (t |_ p1) \<subseteq> funas_term t"
      by (rule supteq_imp_funas_term_subset,
          rule subt_at_imp_supteq[OF p1])
    finally show "(f,length ts) \<in> F"
      using sig by blast
  qed
  show ?thesis
    unfolding csstep_cond_def
  proof (intro iffI allI impI)
    fix p1 i p2
    assume restricted:
      "\<forall>p1 i p2. p = p1 @ i # p2 \<and> p \<in> poss t \<longrightarrow>
        (\<exists>f ts. t |_ p1 = Fun f ts \<and>
          i \<in> restrict_mu_to_sig F \<mu> (f,length ts))"
      and at: "p = p1 @ i # p2 \<and> p \<in> poss t"
    from restricted[rule_format, OF at]
    obtain f ts where sub: "t |_ p1 = Fun f ts"
      and active: "i \<in> restrict_mu_to_sig F \<mu> (f,length ts)"
      by blast
    show "\<exists>f ts. t |_ p1 = Fun f ts \<and> i \<in> \<mu> (f,length ts)"
      using sub active unfolding restrict_mu_to_sig_def
      by (auto split: if_splits)
  next
    fix p1 i p2
    assume active:
      "\<forall>p1 i p2. p = p1 @ i # p2 \<and> p \<in> poss t \<longrightarrow>
        (\<exists>f ts. t |_ p1 = Fun f ts \<and> i \<in> \<mu> (f,length ts))"
      and at: "p = p1 @ i # p2 \<and> p \<in> poss t"
    from active[rule_format, OF at]
    obtain f ts where sub: "t |_ p1 = Fun f ts"
      and i: "i \<in> \<mu> (f,length ts)"
      by blast
    have at1: "p = p1 @ i # p2" and at2: "p \<in> poss t"
      using at by auto
    have fn: "(f,length ts) \<in> F"
      by (rule roots[OF at1 at2 sub])
    show "\<exists>f ts. t |_ p1 = Fun f ts \<and>
      i \<in> restrict_mu_to_sig F \<mu> (f,length ts)"
      using sub i fn unfolding restrict_mu_to_sig_def by auto
  qed
qed

lemma sig_csstep_subset_restrict_mu_to_sig:
  "sig_step F (csstep \<mu> R) \<subseteq>
    csstep (restrict_mu_to_sig F \<mu>) R"
proof
  fix st
  assume mem: "st \<in> sig_step F (csstep \<mu> R)"
  obtain s t where st: "st = (s,t)"
    using mem by (cases st)
  from mem obtain p where step: "(s,t) \<in> csstep_p \<mu> R p"
    and sig: "funas_term s \<subseteq> F"
    unfolding st sig_step_def csstep_def by auto
  from step obtain lr \<sigma> where rst: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_p_def by auto
  have cond': "csstep_cond (restrict_mu_to_sig F \<mu>) p s"
    using cond csstep_cond_restrict_mu_to_sig[
      OF sig, where p=p and \<mu>=\<mu>] by simp
  have "(s,t) \<in> csstep_p (restrict_mu_to_sig F \<mu>) R p"
    unfolding csstep_p_def using rst cond' by blast
  then show "st \<in> csstep (restrict_mu_to_sig F \<mu>) R"
    unfolding st csstep_def by blast
qed

lemma SN_restrict_mu_to_sig_imp_SN_sig_csstep:
  assumes "SN (csstep (restrict_mu_to_sig F \<mu>) R)"
  shows "SN (sig_step F (csstep \<mu> R))"
  by (rule SN_subset[OF assms sig_csstep_subset_restrict_mu_to_sig])

definition finite_conservative_csdp_coverage ::
  "('f::{showl, compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f \<Rightarrow>
    'f sig \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "finite_conservative_csdp_coverage shp U F \<mu> D R P S \<longleftrightarrow>
    mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R \<subseteq> P \<and>
    collapsing_mu_CSDP_on shp U (restrict_mu_to_sig F \<mu>) R \<subseteq> P \<and>
    R \<subseteq> S \<and>
    (\<forall>f ts i. (f,length ts) \<in> F \<longrightarrow>
      i < length ts \<longrightarrow> i \<in> \<mu> (f,length ts) \<longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S) \<and>
    (\<forall>f ts. (f,length ts) \<in> D \<longrightarrow>
      (Fun U [Fun f ts], sharp_term shp (Fun f ts)) \<in> rstep S)"

lemma restrict_mu_to_sig_projection:
  assumes projections:
    "\<And>f (ts :: ('f,'v) term list) i.
      (f,length ts) \<in> F \<Longrightarrow>
      i < length ts \<Longrightarrow> i \<in> \<mu> (f,length ts) \<Longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
  shows "\<And>f (ts :: ('f,'v) term list) i.
    i < length ts \<Longrightarrow>
    i \<in> restrict_mu_to_sig F \<mu> (f,length ts) \<Longrightarrow>
    (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
proof -
  fix f and ts :: "('f,'v) term list" and i
  assume ilen: "i < length ts"
    and active: "i \<in> restrict_mu_to_sig F \<mu> (f,length ts)"
  from active have fn: "(f,length ts) \<in> F"
    unfolding restrict_mu_to_sig_def by (auto split: if_splits)
  from active fn have active': "i \<in> \<mu> (f,length ts)"
    unfolding restrict_mu_to_sig_def by simp
  show "(Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
    by (rule projections[OF fn ilen active'])
qed

lemma finite_conservative_csdp_coverage_imp:
  assumes cover: "finite_conservative_csdp_coverage shp U F \<mu> D R P S"
  shows "conservative_csdp_coverage shp U (restrict_mu_to_sig F \<mu>) D R P S"
proof -
  from cover have mu:
      "mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R \<subseteq> P"
    and collapsing:
      "collapsing_mu_CSDP_on shp U (restrict_mu_to_sig F \<mu>) R \<subseteq> P"
    and rules: "R \<subseteq> S"
    and projections:
      "\<And>f ts i. (f,length ts) \<in> F \<Longrightarrow>
        i < length ts \<Longrightarrow> i \<in> \<mu> (f,length ts) \<Longrightarrow>
        (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
    and marks:
      "\<And>f ts. (f,length ts) \<in> D \<Longrightarrow>
        (Fun U [Fun f ts], sharp_term shp (Fun f ts)) \<in> rstep S"
    unfolding finite_conservative_csdp_coverage_def by auto
  have projections':
    "\<And>f ts i.
      i < length ts \<Longrightarrow>
      i \<in> restrict_mu_to_sig F \<mu> (f,length ts) \<Longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep S"
    by (rule restrict_mu_to_sig_projection[OF projections])
  show ?thesis
    unfolding conservative_csdp_coverage_def
    using mu collapsing rules projections' marks by blast
qed

lemma finite_conservative_CSDP_imp_SN_sig_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "finite_conservative_csdp_coverage shp U F \<mu> D R P S"
    and fin: "finite_dpp (False, False, P, {}, {}, {}, S)"
  shows "SN (sig_step F (csstep \<mu> R))"
proof (rule SN_restrict_mu_to_sig_imp_SN_sig_csstep)
  show "SN (csstep (restrict_mu_to_sig F \<mu>) R)"
    by (rule finite_conservative_CSDP_imp_SN_csstep[
      OF wf defs finite_conservative_csdp_coverage_imp[OF cover] fin])
qed

lemma mu_fun_poss_restrict_mu_to_sig:
  assumes sig: "funas_term t \<subseteq> F"
  shows "mu_fun_poss (restrict_mu_to_sig F \<mu>) t = mu_fun_poss \<mu> t"
  using sig
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems have fn: "(f,length ts) \<in> F"
    and args: "\<And>t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"
    by auto
  have ih: "\<And>i. i < length ts \<Longrightarrow>
    mu_fun_poss (restrict_mu_to_sig F \<mu>) (ts ! i) =
      mu_fun_poss \<mu> (ts ! i)"
    by (rule Fun.hyps, rule nth_mem, assumption, rule args, rule nth_mem, assumption)
  show ?case
    using fn ih unfolding restrict_mu_to_sig_def by auto
qed

lemma csdp_mu_poss_restrict_mu_to_sig:
  assumes sig: "funas_term t \<subseteq> F"
  shows "CSR_Checker_Base.mu_poss (restrict_mu_to_sig F \<mu>) t =
    CSR_Checker_Base.mu_poss \<mu> t"
  using sig
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems have fn: "(f,length ts) \<in> F"
    and args: "\<And>t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"
    by auto
  have ih: "\<And>i. i < length ts \<Longrightarrow>
    CSR_Checker_Base.mu_poss (restrict_mu_to_sig F \<mu>) (ts ! i) =
      CSR_Checker_Base.mu_poss \<mu> (ts ! i)"
    by (rule Fun.hyps, rule nth_mem, assumption, rule args, rule nth_mem, assumption)
  show ?case
    using fn ih unfolding restrict_mu_to_sig_def by auto
qed

lemma csdp_mu_vars_term_restrict_mu_to_sig:
  assumes "funas_term t \<subseteq> F"
  shows "CSR_Checker_Base.mu_vars_term (restrict_mu_to_sig F \<mu>) t =
    CSR_Checker_Base.mu_vars_term \<mu> t"
  unfolding CSR_Checker_Base.mu_vars_term_def
  using csdp_mu_poss_restrict_mu_to_sig[OF assms] by simp

lemma csdp_mu_supt_restrict_mu_to_sig:
  assumes "funas_term s \<subseteq> F"
  shows "CSR_Checker_Base.mu_supt (restrict_mu_to_sig F \<mu>) s t =
    CSR_Checker_Base.mu_supt \<mu> s t"
  unfolding CSR_Checker_Base.mu_supt_def
  using csdp_mu_poss_restrict_mu_to_sig[OF assms] by simp

lemma mu_CSDP_on_restrict_mu_to_sig:
  assumes RF: "funas_trs R \<subseteq> F"
  shows "mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R =
    mu_CSDP_on shp \<mu> D R"
proof -
  have terms: "\<And>l r. (l,r) \<in> R \<Longrightarrow>
    funas_term l \<subseteq> F \<and> funas_term r \<subseteq> F"
  proof -
    fix l r
    assume lr: "(l,r) \<in> R"
    have "funas_rule (l,r) \<subseteq> funas_trs R"
      unfolding funas_trs_def
    proof
      fix fn
      assume fn: "fn \<in> funas_rule (l,r)"
      have A: "funas_rule (l,r) \<in> funas_rule ` R"
        by (rule imageI, rule lr)
      show "fn \<in> \<Union>(funas_rule ` R)"
      proof (rule UnionI)
        show "funas_rule (l,r) \<in> funas_rule ` R"
          by (rule A)
        show "fn \<in> funas_rule (l,r)"
          by (rule fn)
      qed
    qed
    then show "funas_term l \<subseteq> F \<and> funas_term r \<subseteq> F"
      using RF unfolding funas_rule_def by auto
  qed
  show ?thesis
  proof (intro equalityI subsetI)
    fix dp
    assume "dp \<in> mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R"
    then obtain l r p f ts where lr: "(l,r) \<in> R"
      and pos: "p \<in> mu_fun_poss (restrict_mu_to_sig F \<mu>) r"
      and sub: "r |_ p = Fun f ts" and def: "(f,length ts) \<in> D"
      and ns: "\<not> CSR_Checker_Base.mu_supt
        (restrict_mu_to_sig F \<mu>) l (r |_ p)"
      and dp: "dp = (sharp_term shp l, sharp_term shp (r |_ p))"
      unfolding CSR_Checker_Base.mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have pos': "p \<in> mu_fun_poss \<mu> r"
      using pos mu_fun_poss_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have ns': "\<not> CSR_Checker_Base.mu_supt \<mu> l (r |_ p)"
      using ns csdp_mu_supt_restrict_mu_to_sig[OF lF, of \<mu> "r |_ p"]
      by simp
    show "dp \<in> mu_CSDP_on shp \<mu> D R"
      unfolding CSR_Checker_Base.mu_CSDP_on_def
      using lr pos' sub def ns' dp by blast
  next
    fix dp
    assume "dp \<in> mu_CSDP_on shp \<mu> D R"
    then obtain l r p f ts where lr: "(l,r) \<in> R"
      and pos: "p \<in> mu_fun_poss \<mu> r"
      and sub: "r |_ p = Fun f ts" and def: "(f,length ts) \<in> D"
      and ns: "\<not> CSR_Checker_Base.mu_supt \<mu> l (r |_ p)"
      and dp: "dp = (sharp_term shp l, sharp_term shp (r |_ p))"
      unfolding CSR_Checker_Base.mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have pos': "p \<in> mu_fun_poss (restrict_mu_to_sig F \<mu>) r"
      using pos mu_fun_poss_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have ns': "\<not> CSR_Checker_Base.mu_supt
      (restrict_mu_to_sig F \<mu>) l (r |_ p)"
      using ns csdp_mu_supt_restrict_mu_to_sig[OF lF, of \<mu> "r |_ p"]
      by simp
    show "dp \<in> mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R"
      unfolding CSR_Checker_Base.mu_CSDP_on_def
      using lr pos' sub def ns' dp by blast
  qed
qed

lemma collapsing_mu_CSDP_on_restrict_mu_to_sig:
  assumes RF: "funas_trs R \<subseteq> F"
  shows "collapsing_mu_CSDP_on shp U (restrict_mu_to_sig F \<mu>) R =
    collapsing_mu_CSDP_on shp U \<mu> R"
proof -
  have terms: "\<And>l r. (l,r) \<in> R \<Longrightarrow>
    funas_term l \<subseteq> F \<and> funas_term r \<subseteq> F"
  proof -
    fix l r
    assume lr: "(l,r) \<in> R"
    have "funas_rule (l,r) \<subseteq> funas_trs R"
      unfolding funas_trs_def
    proof
      fix fn
      assume fn: "fn \<in> funas_rule (l,r)"
      have A: "funas_rule (l,r) \<in> funas_rule ` R"
        by (rule imageI, rule lr)
      show "fn \<in> \<Union>(funas_rule ` R)"
      proof (rule UnionI)
        show "funas_rule (l,r) \<in> funas_rule ` R"
          by (rule A)
        show "fn \<in> funas_rule (l,r)"
          by (rule fn)
      qed
    qed
    then show "funas_term l \<subseteq> F \<and> funas_term r \<subseteq> F"
      using RF unfolding funas_rule_def by auto
  qed
  show ?thesis
  proof (intro equalityI subsetI)
    fix dp
    assume "dp \<in> collapsing_mu_CSDP_on shp U
      (restrict_mu_to_sig F \<mu>) R"
    then obtain l r x where lr: "(l,r) \<in> R"
      and xr: "x \<in> CSR_Checker_Base.mu_vars_term
        (restrict_mu_to_sig F \<mu>) r"
      and xl: "x \<notin> CSR_Checker_Base.mu_vars_term
        (restrict_mu_to_sig F \<mu>) l"
      and dp: "dp = (sharp_term shp l, Fun U [Var x])"
      unfolding collapsing_mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have xr': "x \<in> CSR_Checker_Base.mu_vars_term \<mu> r"
      using xr csdp_mu_vars_term_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have xl': "x \<notin> CSR_Checker_Base.mu_vars_term \<mu> l"
      using xl csdp_mu_vars_term_restrict_mu_to_sig[OF lF, of \<mu>] by simp
    show "dp \<in> collapsing_mu_CSDP_on shp U \<mu> R"
      unfolding collapsing_mu_CSDP_on_def using lr xr' xl' dp by blast
  next
    fix dp
    assume "dp \<in> collapsing_mu_CSDP_on shp U \<mu> R"
    then obtain l r x where lr: "(l,r) \<in> R"
      and xr: "x \<in> CSR_Checker_Base.mu_vars_term \<mu> r"
      and xl: "x \<notin> CSR_Checker_Base.mu_vars_term \<mu> l"
      and dp: "dp = (sharp_term shp l, Fun U [Var x])"
      unfolding collapsing_mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have xr': "x \<in> CSR_Checker_Base.mu_vars_term
      (restrict_mu_to_sig F \<mu>) r"
      using xr csdp_mu_vars_term_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have xl': "x \<notin> CSR_Checker_Base.mu_vars_term
      (restrict_mu_to_sig F \<mu>) l"
      using xl csdp_mu_vars_term_restrict_mu_to_sig[OF lF, of \<mu>] by simp
    show "dp \<in> collapsing_mu_CSDP_on shp U
      (restrict_mu_to_sig F \<mu>) R"
      unfolding collapsing_mu_CSDP_on_def using lr xr' xl' dp by blast
  qed
qed

definition improved_csr_dependency_pairs_tt ::
  "('dpp, ('f::{showl, compare_order}, label_type) lab, string) dpp_ops \<Rightarrow>
    ('f,label_type) lab \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
    (('f,label_type) lab, string) rules \<Rightarrow>
    (('f,label_type) lab, string) rules \<Rightarrow> 'dpp result"
where
  "improved_csr_dependency_pairs_tt J U \<mu> R P \<equiv>
    let D = defined_list R;
        F = funas_trs_list R
    in check_return (do {
      check_wf_trs R;
      check_allm (\<lambda>(f,n). check ((Sharp f,n) \<notin> set D)
        (showsl_lit (STR ''sharping yields a defined symbol''))) D;
      check_allm (\<lambda>(f,n). check (\<not> is_sharp_lab f)
        (showsl_lit (STR ''source CSR defines a sharp symbol''))) D;
      check_allm (\<lambda>(f,n). check (f \<noteq> U)
        (showsl_lit (STR ''unhiding symbol is not fresh''))) F;
      check (\<not> is_sharp_lab U)
        (showsl_lit (STR ''unhiding symbol must not be sharp''));
      check_all (\<lambda>dp. dp \<in> set P) (mu_CSDP_list Sharp R \<mu> D)
        <+? (\<lambda>_. showsl_lit (STR ''missing replacement-map dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (collapsing_mu_CSDP_list Sharp U \<mu> R)
        <+? (\<lambda>_. showsl_lit (STR ''missing collapsing dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (hidden_mu_CSDP_list Sharp U \<mu> D R)
        <+? (\<lambda>_. showsl_lit (STR ''missing hidden-term dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (improved_projection_pairs_list U \<mu> D R)
        <+? (\<lambda>_. showsl_lit (STR ''missing unhiding projection pair''))
    }) (dpp_ops.mk J False False P [] [] [] R)"

lemma improved_csr_dependency_pairs_tt_sound:
  assumes J: "dpp_spec J"
    and tt: "improved_csr_dependency_pairs_tt J U \<mu> R P = return d"
  shows "d = dpp_ops.mk J False False P [] [] [] R"
    and "wf_trs (set R)"
    and "\<And>n. (U,n) \<notin> set (funas_trs_list R)"
    and "\<not> is_sharp_lab U"
    and "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and "improved_csdp_coverage Sharp U (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)"
proof -
  note tt' = tt[unfolded improved_csr_dependency_pairs_tt_def Let_def,
    simplified]
  from tt' show "d = dpp_ops.mk J False False P [] [] [] R"
    by auto
  from tt' show "wf_trs (set R)"
    by auto
  fix n
  from tt' show "(U,n) \<notin> set (funas_trs_list R)"
    by auto
  from tt' show "\<not> is_sharp_lab U"
    by auto
  fix f n
  show "\<not> defined (set R) (Sharp f,n)"
  proof
    assume def: "defined (set R) (Sharp f,n)"
    have mem: "(Sharp f,n) \<in> set (defined_list R)"
      using def by auto
    from tt' mem show False by auto
  qed
  have mu_pairs:
    "set (mu_CSDP_list Sharp R \<mu> (defined_list R)) \<subseteq> set P"
    using tt' by auto
  have collapsing:
    "set (collapsing_mu_CSDP_list Sharp U \<mu> R) \<subseteq> set P"
    using tt' by auto
  have hidden:
    "set (hidden_mu_CSDP_list Sharp U \<mu> (defined_list R) R) \<subseteq> set P"
    using tt' by auto
  have projections:
    "set (improved_projection_pairs_list U \<mu> (defined_list R) R)
      \<subseteq> set P"
    using tt' by auto
  show "improved_csdp_coverage Sharp U (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)"
    by (rule improved_csr_dependency_pairs_list_coverage[
        OF mu_pairs collapsing hidden projections])
qed

lemma improved_csr_dependency_pairs_tt_finite_imp_SN_sig:
  assumes J: "dpp_spec J"
    and tt: "improved_csr_dependency_pairs_tt J U \<mu> R P = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
proof -
  from improved_csr_dependency_pairs_tt_sound[OF J tt]
  have d: "d = dpp_ops.mk J False False P [] [] [] R"
    and wf: "wf_trs (set R)"
    and cover: "improved_csdp_coverage Sharp U (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)"
    by auto
  have fin': "finite_dpp
      (False, False, set P, {}, {}, {}, set R)"
    using fin d dpp_spec.mk_sound[OF J] by simp
  have defs:
    "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    by auto
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule finite_improved_CSDP_imp_SN_csstep[
        OF wf defs cover fin'])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
qed

definition conservative_csr_dependency_pairs_tt ::
  "('dpp, ('f::{showl, compare_order}, label_type) lab, string) dpp_ops \<Rightarrow>
    ('f,label_type) lab \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
    (('f,label_type) lab, string) rules \<Rightarrow>
    (('f,label_type) lab, string) rules \<Rightarrow>
    (('f,label_type) lab, string) rules \<Rightarrow> 'dpp result"
where
  "conservative_csr_dependency_pairs_tt J U \<mu> R P S \<equiv>
    let D = defined_list R;
        F = funas_trs_list R
    in check_return (do {
      check_wf_trs R;
      check_allm (\<lambda>(f,n). check ((Sharp f,n) \<notin> set D)
        (showsl_lit (STR ''sharping yields a defined symbol''))) D;
      check_all (\<lambda>dp. dp \<in> set P) (mu_CSDP_list Sharp R \<mu> D)
        <+? (\<lambda>_. showsl_lit (STR ''missing replacement-map dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (collapsing_mu_CSDP_list Sharp U \<mu> R)
        <+? (\<lambda>_. showsl_lit (STR ''missing collapsing dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (hidden_mu_CSDP_list Sharp U \<mu> D R)
        <+? (\<lambda>_. showsl_lit (STR ''missing hidden-term dependency pair''));
      check_all (\<lambda>lr. lr \<in> set S) R
        <+? (\<lambda>_. showsl_lit (STR ''missing original weak rule''));
      check_all (\<lambda>lr. lr \<in> set S)
        (conservative_projection_rules_list U \<mu> F)
        <+? (\<lambda>_. showsl_lit (STR ''missing unhiding projection rule''));
      check_all (\<lambda>lr. lr \<in> set S)
        (conservative_marking_rules_list Sharp U D)
        <+? (\<lambda>_. showsl_lit (STR ''missing unhiding marking rule''))
    }) (dpp_ops.mk J False False P [] [] [] S)"

lemma conservative_csr_dependency_pairs_tt_sound:
  assumes J: "dpp_spec J"
    and tt: "conservative_csr_dependency_pairs_tt J U \<mu> R P S = return d"
  shows "d = dpp_ops.mk J False False P [] [] [] S"
    and "wf_trs (set R)"
    and "finite_conservative_csdp_coverage Sharp U
      (set (funas_trs_list R)) (mu_of \<mu>) (set (defined_list R))
      (set R) (set P) (set S)"
proof -
  note tt' = tt[unfolded conservative_csr_dependency_pairs_tt_def Let_def,
    simplified]
  from tt' show d:
    "d = dpp_ops.mk J False False P [] [] [] S"
    by auto
  from tt' show wf: "wf_trs (set R)"
    by auto
  have mu_pairs:
    "set (mu_CSDP_list Sharp R \<mu> (defined_list R)) \<subseteq> set P"
    using tt' by auto
  have collapsing:
    "set (collapsing_mu_CSDP_list Sharp U \<mu> R) \<subseteq> set P"
    using tt' by auto
  have rules: "set R \<subseteq> set S"
    using tt' by auto
  have projections:
    "set (conservative_projection_rules_list U \<mu> (funas_trs_list R))
      \<subseteq> set S"
    using tt' by auto
  have marks:
    "set (conservative_marking_rules_list Sharp U (defined_list R))
      \<subseteq> set S"
    using tt' by auto
  let ?F = "set (funas_trs_list R)"
  let ?D = "set (defined_list R)"
  have RF: "funas_trs (set R) \<subseteq> ?F"
    by simp
  have mu_cover:
    "mu_CSDP_on Sharp (restrict_mu_to_sig ?F (mu_of \<mu>)) ?D (set R)
      \<subseteq> set P"
    using mu_pairs
    unfolding mu_CSDP_list_split_semantics
      mu_CSDP_on_restrict_mu_to_sig[OF RF]
    by simp
  have collapsing_cover:
    "collapsing_mu_CSDP_on Sharp U
      (restrict_mu_to_sig ?F (mu_of \<mu>)) (set R) \<subseteq> set P"
    using collapsing
    unfolding collapsing_mu_CSDP_list
      collapsing_mu_CSDP_on_restrict_mu_to_sig[OF RF]
    by simp
  have projection_steps:
    "\<And>f ts i. (f,length ts) \<in> ?F \<Longrightarrow>
      i < length ts \<Longrightarrow> i \<in> mu_of \<mu> (f,length ts) \<Longrightarrow>
      (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rstep (set S)"
    using conservative_projection_rules_list_step[
      where U=U and \<mu>=\<mu> and F="funas_trs_list R"]
      rstep_mono[OF projections] by blast
  have marking_steps:
    "\<And>f ts. (f,length ts) \<in> ?D \<Longrightarrow>
      (Fun U [Fun f ts], sharp_term Sharp (Fun f ts)) \<in> rstep (set S)"
    using conservative_marking_rules_list_step[
      where shp=Sharp and U=U and D="defined_list R"]
      rstep_mono[OF marks] by blast
  show "finite_conservative_csdp_coverage Sharp U ?F (mu_of \<mu>) ?D
    (set R) (set P) (set S)"
    unfolding finite_conservative_csdp_coverage_def
    using mu_cover collapsing_cover rules projection_steps marking_steps
    by blast
qed

lemma conservative_csr_dependency_pairs_tt_finite_imp_SN_sig:
  assumes J: "dpp_spec J"
    and tt: "conservative_csr_dependency_pairs_tt J U \<mu> R P S = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
proof -
  from conservative_csr_dependency_pairs_tt_sound[OF J tt]
  have d: "d = dpp_ops.mk J False False P [] [] [] S"
    and wf: "wf_trs (set R)"
    and cover: "finite_conservative_csdp_coverage Sharp U
      (set (funas_trs_list R)) (mu_of \<mu>) (set (defined_list R))
      (set R) (set P) (set S)"
    by auto
  have fin': "finite_dpp
    (False, False, set P, {}, {}, {}, set S)"
    using fin d dpp_spec.mk_sound[OF J] by simp
  have defs:
    "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    by auto
  show ?thesis
    by (rule finite_conservative_CSDP_imp_SN_sig_csstep[
      OF wf defs cover fin'])
qed

end
