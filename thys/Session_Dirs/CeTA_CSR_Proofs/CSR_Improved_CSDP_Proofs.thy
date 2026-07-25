(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Improved_CSDP_Proofs
  imports
    CSR_CSDP_Proofs
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
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> bool"
where
  "hides_position_on \<mu> D R f i \<longleftrightarrow>
    (\<exists>l r p ts. (l,r) \<in> R \<and> p \<in> fun_poss r \<and>
      p \<notin> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      i < length ts \<and> i \<in> \<mu> (f, length ts) \<and>
      (\<exists>q. q \<in> mu_poss \<mu> (ts ! i) \<and>
        (is_Var ((ts ! i) |_ q) \<or> root ((ts ! i) |_ q) \<in> Some ` D)))"

inductive hiding_context_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> bool"
for \<mu> D R
where
  hole[intro]: "hiding_context_on \<mu> D R \<box>"
| more[intro]: "hides_position_on \<mu> D R f (length bef) \<Longrightarrow>
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
  case (more f bef C aft)
  then show ?case by auto
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
    (\<forall>f ts i. hides_position_on \<mu> D R f i \<longrightarrow> i < length ts \<longrightarrow>
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
  case (more f bef C aft)
  let ?whole = "Fun f (bef @ C\<langle>t\<rangle> # aft)"
  have i: "length bef < length (bef @ C\<langle>t\<rangle> # aft)"
    by simp
  have nth: "(bef @ C\<langle>t\<rangle> # aft) ! length bef = C\<langle>t\<rangle>"
    by simp
  from cover[unfolded improved_csdp_coverage_def]
  have projections: "\<And>f ts i. hides_position_on \<mu> D R f i \<Longrightarrow>
    i < length ts \<Longrightarrow> (Fun U [Fun f ts], Fun U [ts ! i]) \<in> rrstep P"
    by blast
  from projections[OF more.hyps(1) i] nth have step:
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
    with T_p show ?thesis by (blast intro: r_into_trancl)
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
      with T_p show ?thesis
        unfolding s uh by blast
    qed
  qed
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

lemma duplicated_mu_poss_eq [simp]:
  "CSR_Checker.mu_poss \<mu> t = CSR_CSDP_Proofs.mu_poss \<mu> t"
  by (induct t) auto

lemma duplicated_mu_vars_term_eq [simp]:
  "CSR_Checker.mu_vars_term \<mu> t = CSR_CSDP_Proofs.mu_vars_term \<mu> t"
  unfolding CSR_Checker.mu_vars_term_def CSR_CSDP_Proofs.mu_vars_term_def
  using duplicated_mu_poss_eq by auto

lemma duplicated_mu_supt_eq [simp]:
  "CSR_Checker.mu_supt \<mu> s t = CSR_CSDP_Proofs.mu_supt \<mu> s t"
  unfolding CSR_Checker.mu_supt_def CSR_CSDP_Proofs.mu_supt_def
  using duplicated_mu_poss_eq by simp

lemma duplicated_mu_CSDP_on_eq:
  "CSR_Checker.mu_CSDP_on shp \<mu> D R =
    CSR_CSDP_Proofs.mu_CSDP_on shp \<mu> D R"
  unfolding CSR_Checker.mu_CSDP_on_def CSR_CSDP_Proofs.mu_CSDP_on_def
  by simp

lemma mu_CSDP_list_split_semantics:
  "set (mu_CSDP_list Sharp R \<mu> D) =
    CSR_CSDP_Proofs.mu_CSDP_on Sharp (mu_of \<mu>) (set D) (set R)"
  using CSR_Checker.mu_CSDP_list[of Sharp R \<mu> D]
  unfolding duplicated_mu_CSDP_on_eq .

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
  shows "CSR_CSDP_Proofs.mu_poss (restrict_mu_to_sig F \<mu>) t =
    CSR_CSDP_Proofs.mu_poss \<mu> t"
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
    CSR_CSDP_Proofs.mu_poss (restrict_mu_to_sig F \<mu>) (ts ! i) =
      CSR_CSDP_Proofs.mu_poss \<mu> (ts ! i)"
    by (rule Fun.hyps, rule nth_mem, assumption, rule args, rule nth_mem, assumption)
  show ?case
    using fn ih unfolding restrict_mu_to_sig_def by auto
qed

lemma csdp_mu_vars_term_restrict_mu_to_sig:
  assumes "funas_term t \<subseteq> F"
  shows "CSR_CSDP_Proofs.mu_vars_term (restrict_mu_to_sig F \<mu>) t =
    CSR_CSDP_Proofs.mu_vars_term \<mu> t"
  unfolding CSR_CSDP_Proofs.mu_vars_term_def
  using csdp_mu_poss_restrict_mu_to_sig[OF assms] by simp

lemma csdp_mu_supt_restrict_mu_to_sig:
  assumes "funas_term s \<subseteq> F"
  shows "CSR_CSDP_Proofs.mu_supt (restrict_mu_to_sig F \<mu>) s t =
    CSR_CSDP_Proofs.mu_supt \<mu> s t"
  unfolding CSR_CSDP_Proofs.mu_supt_def
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
      and ns: "\<not> CSR_CSDP_Proofs.mu_supt
        (restrict_mu_to_sig F \<mu>) l (r |_ p)"
      and dp: "dp = (sharp_term shp l, sharp_term shp (r |_ p))"
      unfolding CSR_CSDP_Proofs.mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have pos': "p \<in> mu_fun_poss \<mu> r"
      using pos mu_fun_poss_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have ns': "\<not> CSR_CSDP_Proofs.mu_supt \<mu> l (r |_ p)"
      using ns csdp_mu_supt_restrict_mu_to_sig[OF lF, of \<mu> "r |_ p"]
      by simp
    show "dp \<in> mu_CSDP_on shp \<mu> D R"
      unfolding CSR_CSDP_Proofs.mu_CSDP_on_def
      using lr pos' sub def ns' dp by blast
  next
    fix dp
    assume "dp \<in> mu_CSDP_on shp \<mu> D R"
    then obtain l r p f ts where lr: "(l,r) \<in> R"
      and pos: "p \<in> mu_fun_poss \<mu> r"
      and sub: "r |_ p = Fun f ts" and def: "(f,length ts) \<in> D"
      and ns: "\<not> CSR_CSDP_Proofs.mu_supt \<mu> l (r |_ p)"
      and dp: "dp = (sharp_term shp l, sharp_term shp (r |_ p))"
      unfolding CSR_CSDP_Proofs.mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have pos': "p \<in> mu_fun_poss (restrict_mu_to_sig F \<mu>) r"
      using pos mu_fun_poss_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have ns': "\<not> CSR_CSDP_Proofs.mu_supt
      (restrict_mu_to_sig F \<mu>) l (r |_ p)"
      using ns csdp_mu_supt_restrict_mu_to_sig[OF lF, of \<mu> "r |_ p"]
      by simp
    show "dp \<in> mu_CSDP_on shp (restrict_mu_to_sig F \<mu>) D R"
      unfolding CSR_CSDP_Proofs.mu_CSDP_on_def
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
      and xr: "x \<in> CSR_CSDP_Proofs.mu_vars_term
        (restrict_mu_to_sig F \<mu>) r"
      and xl: "x \<notin> CSR_CSDP_Proofs.mu_vars_term
        (restrict_mu_to_sig F \<mu>) l"
      and dp: "dp = (sharp_term shp l, Fun U [Var x])"
      unfolding collapsing_mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have xr': "x \<in> CSR_CSDP_Proofs.mu_vars_term \<mu> r"
      using xr csdp_mu_vars_term_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have xl': "x \<notin> CSR_CSDP_Proofs.mu_vars_term \<mu> l"
      using xl csdp_mu_vars_term_restrict_mu_to_sig[OF lF, of \<mu>] by simp
    show "dp \<in> collapsing_mu_CSDP_on shp U \<mu> R"
      unfolding collapsing_mu_CSDP_on_def using lr xr' xl' dp by blast
  next
    fix dp
    assume "dp \<in> collapsing_mu_CSDP_on shp U \<mu> R"
    then obtain l r x where lr: "(l,r) \<in> R"
      and xr: "x \<in> CSR_CSDP_Proofs.mu_vars_term \<mu> r"
      and xl: "x \<notin> CSR_CSDP_Proofs.mu_vars_term \<mu> l"
      and dp: "dp = (sharp_term shp l, Fun U [Var x])"
      unfolding collapsing_mu_CSDP_on_def by blast
    from terms[OF lr] have lF: "funas_term l \<subseteq> F"
      and rF: "funas_term r \<subseteq> F" by auto
    have xr': "x \<in> CSR_CSDP_Proofs.mu_vars_term
      (restrict_mu_to_sig F \<mu>) r"
      using xr csdp_mu_vars_term_restrict_mu_to_sig[OF rF, of \<mu>] by simp
    have xl': "x \<notin> CSR_CSDP_Proofs.mu_vars_term
      (restrict_mu_to_sig F \<mu>) l"
      using xl csdp_mu_vars_term_restrict_mu_to_sig[OF lF, of \<mu>] by simp
    show "dp \<in> collapsing_mu_CSDP_on shp U
      (restrict_mu_to_sig F \<mu>) R"
      unfolding collapsing_mu_CSDP_on_def using lr xr' xl' dp by blast
  qed
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
