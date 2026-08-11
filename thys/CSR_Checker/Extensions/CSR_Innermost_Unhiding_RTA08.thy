(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_Unhiding_RTA08
  imports
    CSR_Checker_Extensions.CSR_Innermost_DP_Checker
    CSR_Checker_Extensions.CSR_Minimal_CSDP_Proofs
begin

definition innermost_csr_rta08_pair_step where
  "innermost_csr_rta08_pair_step shp \<mu> R A P =
    csr_rta08_pair_step shp \<mu> A P \<inter>
      {(s,t). innermost_pair_source shp \<mu> R s}"

lemma innermost_csrstep_mu_Tinf_rhs_imp_rta08_pair_step:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> innermost_csrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and notSN: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
    (sharp_term shp s, sharp_term shp u) \<in>
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
proof -
  from step obtain lr \<sigma> where rewrite:
      "(s,t) \<in> rstep_r_p_s R lr [] \<sigma>"
    and inner0: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csrstep_def innermost_csstep_p_def by blast
  obtain l r where lr_def: "lr = (l,r)" by (cases lr)
  from rewrite have lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding lr_def rstep_r_p_s_def' by auto
  have inner: "\<And>u. mu_supt \<mu> (l \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    using inner0 unfolding lr_def by simp
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  have source: "innermost_pair_source shp \<mu> R
      (sharp_term shp (l \<cdot> \<sigma>))"
    unfolding innermost_pair_source_def
    using lr lhs inner by blast
  from innermost_notSN_imp_mu_Tinf_defined_subterm[
    OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f,length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in>
      mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by blast
  from T_p have notSN_p:
    "\<not> SN_on (innermost_csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r]
    obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from D def len have fD: "(f,length ts) \<in> D" by auto
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
      with sT have "SN_on (innermost_csstep \<mu> R)
          {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    have pair0: "(sharp_term shp l, sharp_term shp (r |_ p))
      \<in> mu_CSDP_on shp \<mu> D R"
      unfolding CSR_Checker_Base.mu_CSDP_on_def
      using lr p_r rp fD ns by blast
    have pair: "(sharp_term shp l, sharp_term shp (r |_ p))
      \<in> csr_rta08_CSDP_on shp \<mu> D R"
      using pair0 unfolding csr_rta08_CSDP_on_def by blast
    have rhs_fun: "is_Fun (sharp_term shp (r |_ p))" using rp by simp
    have raw: "(sharp_term shp (l \<cdot> \<sigma>),
        sharp_term shp ((r |_ p) \<cdot> \<sigma>)) \<in>
      csr_rta08_pair_step shp \<mu> (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
      using csr_rta08_pair_step_noncollapsingI[OF pair rhs_fun, of \<sigma>]
        lhs rp by (cases l, auto)
    have step': "(sharp_term shp (l \<cdot> \<sigma>),
        sharp_term shp ((r |_ p) \<cdot> \<sigma>)) \<in>
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
      using raw source unfolding innermost_csr_rta08_pair_step_def by blast
    show ?thesis using T_p step' sub_subst unfolding s by auto
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
      (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    have xr: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    have xl: "x \<notin> mu_vars_term \<mu> l"
    proof
      assume xl: "x \<in> mu_vars_term \<mu> l"
      have lT: "l \<cdot> \<sigma> \<in>
        mu_Tinf \<mu> (innermost_csstep \<mu> R)"
        using sT unfolding s .
      have "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule innermost_mu_Tinf_SN_on_active_subst_mu_subterm[
          OF lhs lT xl q2])
      with notSN_p sub_q2 show False by simp
    qed
    have pair0: "(sharp_term shp l, Var x)
      \<in> csr_rta08_collapsing_CSDP_on shp \<mu> R"
      by (rule csr_rta08_collapsing_CSDP_onI[OF lr xr xl])
    have pair: "(sharp_term shp l, Var x)
      \<in> csr_rta08_CSDP_on shp \<mu> D R"
      using pair0 unfolding csr_rta08_CSDP_on_def by blast
    have target: "is_Fun (\<sigma> x |_ q2)" using sub_inst sub_q2 by simp
    have admitted: "csr_rta08_defined_target D (\<sigma> x |_ q2)"
      using D def sub_inst sub_q2 by auto
    have raw0: "(sharp_term shp l \<cdot> \<sigma>,
        sharp_term shp (\<sigma> x |_ q2)) \<in>
      csr_rta08_pair_step shp \<mu> (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
      by (rule csr_rta08_pair_step_collapsingI[
        where l="sharp_term shp l" and x=x and \<sigma>=\<sigma> and q=q2],
        rule pair, rule q2, rule target, rule admitted)
    have raw: "(sharp_term shp (l \<cdot> \<sigma>),
        sharp_term shp (\<sigma> x |_ q2)) \<in>
      csr_rta08_pair_step shp \<mu> (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
      using raw0 lhs by (cases l, auto)
    have step': "(sharp_term shp (l \<cdot> \<sigma>),
        sharp_term shp (\<sigma> x |_ q2)) \<in>
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
      using raw source unfolding innermost_csr_rta08_pair_step_def by blast
    show ?thesis using T_p step' sub_q2 unfolding s by auto
  qed
qed

definition finite_innermost_csr_rta08_dpp where
  "finite_innermost_csr_rta08_dpp shp \<mu> R A P \<longleftrightarrow>
    SN_rel (innermost_csr_rta08_pair_step shp \<mu> R A P)
      (innermost_csdp_step shp \<mu> R)"

lemma innermost_csr_progress_relation_imp_SN:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes progress:
    "\<And>t. t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
        (sharp_term shp t, sharp_term shp u) \<in>
          (innermost_csdp_step shp \<mu> R)\<^sup>* O Q O
          (innermost_csdp_step shp \<mu> R)\<^sup>*"
    and fin: "SN_rel Q (innermost_csdp_step shp \<mu> R)"
  shows "SN (innermost_csstep \<mu> R)"
proof (rule ccontr)
  assume not_sn: "\<not> SN (innermost_csstep \<mu> R)"
  from not_SN_imp_Tinf[OF not_sn]
  obtain t0 where t0_T: "t0 \<in> Tinf (innermost_csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" .
  let ?S = "innermost_csdp_step shp \<mu> R"
  let ?rel = "?S\<^sup>* O Q O ?S\<^sup>*"
  have all_ex: "\<forall>t. \<exists>u.
      t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<longrightarrow>
      u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
        (sharp_term shp t, sharp_term shp u) \<in> ?rel"
    using progress by blast
  from choice[OF all_ex]
  obtain nxt where nxt:
    "\<And>t. t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<Longrightarrow>
      nxt t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
        (sharp_term shp t, sharp_term shp (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps]
    have "nxt (ts n) \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      by simp
    then show ?case unfolding ts_def by simp
  qed
  have ts_step:
    "(sharp_term shp (ts n), sharp_term shp (ts (Suc n))) \<in> ?rel"
    for n
    using nxt[OF ts_T[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel Q ?S"
    unfolding SN_rel_on_def SN_defs using chain by blast
  with fin show False by contradiction
qed

lemma mu_Tinf_imp_innermost_rta08_relstep:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
    (sharp_term shp t, sharp_term shp u) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>* O
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R) O
      (innermost_csdp_step shp \<mu> R)\<^sup>*"
proof -
  from mu_Tinf_innermost_imp_first_root_step[OF Tinf]
  obtain s v where pref: "(t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> innermost_csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (innermost_csstep \<mu> R) {v}"
    by blast
  have sv: "(s,v) \<in> innermost_csstep \<mu> R"
    using root unfolding innermost_csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (innermost_csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by (rule innermost_csnrsteps_mu_Tinf_preserve[
      OF wf pref Tinf notSN_s])
  from innermost_csrstep_mu_Tinf_rhs_imp_rta08_pair_step[
    OF wf root sT notSN_v D, where shp=shp]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and pair: "(sharp_term shp s,sharp_term shp u) \<in>
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R)"
    by blast
  have left: "(sharp_term shp t,sharp_term shp s) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>*"
    by (rule innermost_csnrsteps_imp_sharp_innermost_csdp_steps[
      OF pref, where shp=shp])
  have right: "(sharp_term shp u,sharp_term shp u) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>*" by simp
  show ?thesis using uT left pair right by blast
qed

theorem finite_innermost_csr_rta08_CSDP_on_imp_SN:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_innermost_csr_rta08_dpp shp \<mu> R
      (csr_rta08_defined_target D)
      (csr_rta08_CSDP_on shp \<mu> D R)"
  shows "SN (innermost_csstep \<mu> R)"
proof (rule innermost_csr_progress_relation_imp_SN)
  fix t
  assume "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  then show "\<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
    (sharp_term shp t, sharp_term shp u) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>* O
      innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R) O
      (innermost_csdp_step shp \<mu> R)\<^sup>*"
    by (rule mu_Tinf_imp_innermost_rta08_relstep[OF wf _ D])
next
  show "SN_rel
      (innermost_csr_rta08_pair_step shp \<mu> R
        (csr_rta08_defined_target D)
        (csr_rta08_CSDP_on shp \<mu> D R))
      (innermost_csdp_step shp \<mu> R)"
    using fin unfolding finite_innermost_csr_rta08_dpp_def .
qed

theorem csr_switch_via_innermost_rta08_CSDP_on:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,string) trs"
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_innermost_csr_rta08_dpp shp \<mu> R
      (csr_rta08_defined_target D)
      (csr_rta08_CSDP_on shp \<mu> D R)"
  shows "SN (csstep \<mu> R)"
  by (rule csr_switch_overlay_innermost_termination[OF overlay wf],
      rule finite_innermost_csr_rta08_CSDP_on_imp_SN[OF wf D fin])

end
