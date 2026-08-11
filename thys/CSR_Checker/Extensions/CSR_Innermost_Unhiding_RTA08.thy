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

lemma finite_innermost_csr_rta08_dpp_redpair_terminal:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and P S NS R :: "('f,'v) trs"
  assumes redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and noncoll_S: "csr_rta08_noncollapsing_pairs P \<subseteq> S"
    and rewrite_NS: "innermost_csdp_step shp \<mu> R \<subseteq> NS"
    and active_NS: "{(s,t). mu_supt \<mu> s t} \<subseteq> NS"
    and mark_S: "{(t,sharp_term shp t) |t. is_Fun t \<and> A t} \<subseteq> S"
  shows "finite_innermost_csr_rta08_dpp shp \<mu> R A P"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  have raw_S: "csr_rta08_pair_step shp \<mu> A P \<subseteq> S"
  proof
    fix st
    assume step: "st \<in> csr_rta08_pair_step shp \<mu> A P"
    obtain a b where st: "st = (a,b)" by (cases st)
    from step[unfolded csr_rta08_pair_step_def st]
    show "st \<in> S"
    proof
      assume "(a,b) \<in> {(l \<cdot> \<sigma>,r \<cdot> \<sigma>) |l r \<sigma>.
        (l,r) \<in> P \<and> is_Fun r}"
      then obtain l r \<sigma> where a: "a = l \<cdot> \<sigma>"
        and b: "b = r \<cdot> \<sigma>" and pair: "(l,r) \<in> P"
        and rhs: "is_Fun r" by blast
      have "(l,r) \<in> csr_rta08_noncollapsing_pairs P"
        using pair rhs unfolding csr_rta08_noncollapsing_pairs_def by simp
      with noncoll_S have "(l,r) \<in> S" by blast
      then show ?thesis using subst_S unfolding st a b
        by (auto simp: subst.closed_def)
    next
      assume collapse: "(a,b) \<in>
        {(l \<cdot> \<sigma>,sharp_term shp (\<sigma> x |_ q)) |l x \<sigma> q.
          (l,Var x) \<in> P \<and> q \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
          is_Fun (\<sigma> x |_ q) \<and> A (\<sigma> x |_ q)}"
      then obtain l x \<sigma> q where a: "a = l \<cdot> \<sigma>"
        and b: "b = sharp_term shp (\<sigma> x |_ q)"
        and pair: "(l,Var x) \<in> P"
        and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and target: "is_Fun (\<sigma> x |_ q)"
        and admitted: "A (\<sigma> x |_ q)" by blast
      from orient pair have pair_ord: "(l,Var x) \<in> S \<union> NS" by blast
      have inst_ord: "(l \<cdot> \<sigma>,\<sigma> x) \<in> S \<union> NS"
        using pair_ord subst_S subst_NS by (auto simp: subst.closed_def)
      from csr_rta08_active_subterm_bridge[OF q]
      have active: "(\<sigma> x,\<sigma> x |_ q) \<in> NS"
        using active_NS refl_NS unfolding refl_on_def by auto
      from mark_S target admitted have mark:
        "(\<sigma> x |_ q,sharp_term shp (\<sigma> x |_ q)) \<in> S" by blast
      show ?thesis
      proof (cases "(l \<cdot> \<sigma>,\<sigma> x) \<in> S")
        case True
        from compat_S_NS True active have prefix:
          "(l \<cdot> \<sigma>,\<sigma> x |_ q) \<in> S" by blast
        from trans_S_point[OF prefix mark] show ?thesis unfolding st a b .
      next
        case False
        with inst_ord have weak: "(l \<cdot> \<sigma>,\<sigma> x) \<in> NS"
          by blast
        from trans_NS_point[OF weak active] have prefix:
          "(l \<cdot> \<sigma>,\<sigma> x |_ q) \<in> NS" .
        from compat_NS_S prefix mark show ?thesis unfolding st a b by blast
      qed
    qed
  qed
  have pair_S: "innermost_csr_rta08_pair_step shp \<mu> R A P \<subseteq> S"
    using raw_S unfolding innermost_csr_rta08_pair_step_def by blast
  have pair_ord: "innermost_csr_rta08_pair_step shp \<mu> R A P
      \<subseteq> S \<union> NS" using pair_S by blast
  have residual: "innermost_csr_rta08_pair_step shp \<mu> R A P - S
      \<subseteq> {}" using pair_S by blast
  have empty: "SN_rel {} (innermost_csdp_step shp \<mu> R)"
    by (rule SN_rel_empty1)
  have "SN_rel
      (innermost_csr_rta08_pair_step shp \<mu> R A P)
      (innermost_csdp_step shp \<mu> R)"
    by (rule SN_rel_compat_redpair_residual[
      OF redpair rewrite_NS pair_ord residual empty])
  then show ?thesis unfolding finite_innermost_csr_rta08_dpp_def .
qed

lemma csr_rta08_redpair_proc_innermost_terminal_sound:
  fixes J :: "('dpp, ('f::{showl, compare_order},
      'l::{showl, compare_order}) lab, string) dpp_ops"
    and \<mu> :: "(('f, 'l) lab) muL"
    and rp :: "(('f, 'l) lab, string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "csr_rta08_redpair_proc J \<mu> rp Premove dpp = return dpp'"
    and empty: "dpp_ops.pairs J dpp' = []"
  shows "finite_innermost_csr_rta08_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp))
    (csr_rta08_defined_target
      (set (defined_list (dpp_ops.rules J dpp))))
    (set (dpp_ops.pairs J dpp))"
proof -
  interpret dpp_spec J by (rule J)
  obtain F where ws: "rel_impl.not_wst rp = Some F"
    using proc unfolding csr_rta08_redpair_proc_def
    by (cases "rel_impl.not_wst rp", auto)
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)"
    by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove"
    by auto
  let ?D = "defined_list (rules dpp)"
  let ?proj = "csr_rta08_projection_rules_list \<mu> F"
  let ?marks = "csr_rta08_marking_rules_list Sharp ?D"
  let ?cps = "filter (is_Var \<circ> snd) ps"
  let ?nps = "filter (is_Fun \<circ> snd) ps"
  define weak_list where "weak_list = rules dpp @ ?proj @ ?cps @ pns"
  define strict_list where "strict_list = ?nps @ ?marks"
  from proc[unfolded csr_rta08_redpair_proc_def ws split Let_def,
      simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and weak: "isOK (rel_impl_ns rp weak_list)"
    and strict: "isOK (rel_impl_s rp strict_list)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: weak_list_def strict_list_def)
  from valid[unfolded rel_impl_redpair_def, simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)"
    by auto
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST"
    by blast
  have all_rel': "\<exists>S NS NST.
      rel_impl_prop rp (strict_list @ weak_list) S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop:
      "rel_impl_prop rp (strict_list @ weak_list) S NS NST"
    using all_rel' by presburger
  have strict_checks: "\<forall>lr\<in>set strict_list. isOK (rel_impl.s rp lr)"
    using strict unfolding rel_impl_s_def
    by (auto simp: isOK_check_allm)
  have weak_checks: "\<forall>lr\<in>set weak_list. isOK (rel_impl.ns rp lr)"
    using weak unfolding rel_impl_ns_def
    by (auto simp: isOK_check_allm)
  have orientation: "\<forall>st. st \<in> set (strict_list @ weak_list) \<longrightarrow>
      ((isOK (rel_impl.s rp st) \<longrightarrow> st \<in> S) \<and>
       (isOK (rel_impl.ns rp st) \<longrightarrow> st \<in> NS) \<and>
       (isOK (rel_impl.nst rp st) \<longrightarrow> st \<in> NST))"
    by (rule conjunct1[OF rel_prop])
  have strict_S: "set strict_list \<subseteq> S"
    using orientation strict_checks by auto
  have weak_NS: "set weak_list \<subseteq> NS"
    using orientation weak_checks by auto
  from rel_prop have ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and subst_NS: "subst.closed NS"
    and info0: "not_subterm_rel_info NS (rel_impl.not_wst rp)"
    by auto
  from rel_prop standard have trans_S: "trans S"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    by auto
  from rel_prop subst have subst_S: "subst.closed S" by auto
  from rel_prop sn have SN_S: "SN S" by auto
  from info0 have info: "not_subterm_rel_info NS (Some F)"
    unfolding ws .
  have redpair: "compat_redpair_order S NS"
    by (unfold_locales; fact)
  have rules_NS: "set (rules dpp) \<subseteq> NS"
    using weak_NS unfolding weak_list_def by auto
  have rewrite_NS:
      "innermost_csdp_step Sharp (mu_of \<mu>) (set (rules dpp)) \<subseteq> NS"
  proof -
    have inner_rstep:
      "innermost_csdp_step Sharp (mu_of \<mu>) (set (rules dpp))
        \<subseteq> rstep (set (rules dpp))"
      unfolding innermost_csdp_step_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    have "rstep (set (rules dpp)) \<subseteq> rstep NS"
      by (rule rstep_mono[OF rules_NS])
    also have "rstep NS \<subseteq> NS"
      by (rule rstep_subset[OF ctxt_NS subst_NS subset_refl])
    finally show ?thesis using inner_rstep by blast
  qed
  have proj_NS: "set ?proj \<subseteq> NS"
    using weak_NS unfolding weak_list_def by auto
  have active_NS: "{(s,t). mu_supt (mu_of \<mu>) s t} \<subseteq> NS"
    by (rule csr_rta08_projection_rules_cover_active[OF redpair info proj_NS])
  have marks_S: "set ?marks \<subseteq> S"
    using strict_S unfolding strict_list_def by auto
  have mark_S: "{(t, sharp_term Sharp t) |t. is_Fun t \<and>
      csr_rta08_defined_target (set ?D) t} \<subseteq> S"
    by (rule csr_rta08_marking_rules_cover[OF redpair marks_S])
  have nps_S: "set ?nps \<subseteq> S"
    using strict_S unfolding strict_list_def by auto
  have cps_NS: "set ?cps \<subseteq> NS"
    using weak_NS unfolding weak_list_def by auto
  have pns_NS: "set pns \<subseteq> NS"
    using weak_NS unfolding weak_list_def by auto
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
  proof
    fix dp
    assume pair: "dp \<in> set (pairs dpp)"
    show "dp \<in> S \<union> NS"
    proof (cases "dp \<in> set Premove")
      case True
      with pair have in_ps: "dp \<in> set ps" unfolding ps by auto
      obtain l r where dp: "dp = (l,r)" by (cases dp)
      show ?thesis
      proof (cases r)
        case (Var x)
        with in_ps cps_NS show ?thesis unfolding dp by auto
      next
        case (Fun f ts)
        with in_ps nps_S show ?thesis unfolding dp by auto
      qed
    next
      case False
      with pair pns_NS show ?thesis unfolding pns by auto
    qed
  qed
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have empty_set: "set (pairs dpp') = {}" using empty by simp
  have removed: "set (pairs dpp) \<subseteq> set Premove"
  proof
    fix dp
    assume pair: "dp \<in> set (pairs dpp)"
    show "dp \<in> set Premove"
    proof (rule ccontr)
      assume "dp \<notin> set Premove"
      with pair have "dp \<in> set (pairs dpp) - set Premove" by simp
      with pairs' have "dp \<in> set (pairs dpp')" by simp
      with empty_set show False by simp
    qed
  qed
  have noncoll_S:
      "csr_rta08_noncollapsing_pairs (set (pairs dpp)) \<subseteq> S"
  proof
    fix dp
    assume mem: "dp \<in> csr_rta08_noncollapsing_pairs (set (pairs dpp))"
    then have pair: "dp \<in> set (pairs dpp)"
      and rhs_fun: "is_Fun (snd dp)"
      unfolding csr_rta08_noncollapsing_pairs_def by auto
    from pair removed have "dp \<in> set ps" unfolding ps by auto
    with rhs_fun have "dp \<in> set ?nps" by auto
    with nps_S show "dp \<in> S" by blast
  qed
  show ?thesis
    by (rule finite_innermost_csr_rta08_dpp_redpair_terminal[
      OF redpair orient noncoll_S rewrite_NS active_NS mark_S])
qed

fun check_innermost_csr_rta08_terminal ::
  "('dpp, ('f::{showl,compare_order}, 'l::{showl,compare_order}) lab,
      string) dpp_ops \<Rightarrow>
   (('f,'l) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,'l,string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_innermost_csr_rta08_terminal J \<mu> i dpp
      (CSR_DP_Ordinary_Proof (Redpair_UR_Proc redp Pr U P_is_Empty)) =
    debug i (STR ''terminal innermost RTA08 reduction pair'') (do {
      dpp' \<leftarrow> csr_rta08_redpair_proc J \<mu> (get_rel_impl redp) Pr dpp;
      check (dpp_ops.pairs J dpp' = [])
        (i \<circ> showsl_lit
          (STR '': terminal innermost RTA08 reduction pair leaves dependency pairs''))
    })"
| "check_innermost_csr_rta08_terminal J \<mu> i dpp prf =
    error (i \<circ> showsl_lit
      (STR '': innermost RTA08 proof is not a terminal reduction-pair proof''))"

lemma check_innermost_csr_rta08_terminal_sound:
  fixes J :: "('dpp, ('f::{showl,compare_order},
      'l::{showl,compare_order}) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and ok: "isOK (check_innermost_csr_rta08_terminal J \<mu> i dpp prf)"
  shows "finite_innermost_csr_rta08_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp))
    (csr_rta08_defined_target
      (set (defined_list (dpp_ops.rules J dpp))))
    (set (dpp_ops.pairs J dpp))"
using ok
proof (cases "prf")
  case (CSR_DP_Ordinary_Proof child)
  then show ?thesis
  proof (cases child)
    case (Redpair_UR_Proc redp Pr U tail)
    then show ?thesis
    proof (cases tail)
      case P_is_Empty
      from ok CSR_DP_Ordinary_Proof Redpair_UR_Proc P_is_Empty
      obtain dpp' where proc:
          "csr_rta08_redpair_proc J \<mu> (get_rel_impl redp) Pr dpp = return dpp'"
        and empty: "dpp_ops.pairs J dpp' = []" by auto
      show ?thesis
        by (rule csr_rta08_redpair_proc_innermost_terminal_sound[
          OF J get_rel_impl proc empty])
    qed (use ok CSR_DP_Ordinary_Proof Redpair_UR_Proc in simp_all)
  qed (use ok CSR_DP_Ordinary_Proof in simp_all)
qed (use ok in simp_all)

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

definition check_innermost_csr_rta08_termination_proof ::
  "('dpp, ('f::{showl,compare_order}, label_type) lab,string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_innermost_csr_rta08_termination_proof J i \<mu> R P prf =
    debug i (STR ''terminal innermost RTA08 CSR dependency pairs'') (do {
      check_csr_orthogonal R;
      csr_sharp_mu_check \<mu>;
      dpp \<leftarrow> csr_rta08_dependency_pairs_tt J \<mu> R P;
      check_innermost_csr_rta08_terminal J \<mu> (add_index i 1) dpp prf
    })"

lemma check_innermost_csr_rta08_termination_proof_sound:
  fixes J :: "('dpp, ('f::{showl,compare_order}, label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and ok: "isOK (check_innermost_csr_rta08_termination_proof
      J i \<mu> R P prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof -
  from ok obtain dpp where ortho_ok: "isOK (check_csr_orthogonal R)"
    and tt: "csr_rta08_dependency_pairs_tt J \<mu> R P = return dpp"
    and rec: "isOK (check_innermost_csr_rta08_terminal
      J \<mu> (add_index i 1) dpp prf)"
    unfolding check_innermost_csr_rta08_termination_proof_def by auto
  from csr_rta08_dependency_pairs_tt_sound[OF J tt]
  have wf: "wf_trs (set R)"
    and pairs: "set P = csr_rta08_CSDP_on Sharp (mu_of \<mu>)
      (set (defined_list R)) (set R)"
    by auto
  have fin: "finite_innermost_csr_rta08_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.rules J dpp))
      (csr_rta08_defined_target
        (set (defined_list (dpp_ops.rules J dpp))))
      (set (dpp_ops.pairs J dpp))"
    by (rule check_innermost_csr_rta08_terminal_sound[OF J rec])
  interpret dpp_spec J by fact
  from csr_rta08_dependency_pairs_tt_sound[OF J tt]
  have dpp: "dpp = dpp_ops.mk J False False P [] [] [] R" by auto
  have sem: "dpp_ops.dpp J dpp = (False,False,set P,{},{},{},set R)"
    using dpp unfolding dpp_spec.mk_sound[OF J] by simp
  have sem': "dpp_ops.dpp J dpp =
      (NFS dpp,M dpp,set (local.P dpp),set (Pw dpp),set (Q dpp),
        set (local.R dpp),set (Rw dpp))"
    by (rule dpp_sound)
  have rules: "set (dpp_ops.rules J dpp) = set R"
    using sem sem' rules_sound[of dpp] by auto
  have pairs': "set (dpp_ops.pairs J dpp) = set P"
    using sem sem' pairs_sound[of dpp] by auto
  have defined: "set (defined_list (dpp_ops.rules J dpp)) =
      set (defined_list R)"
    using rules by simp
  note fin' = fin[unfolded rules defined pairs']
  have exact: "finite_innermost_csr_rta08_dpp Sharp (mu_of \<mu>)
      (set R) (csr_rta08_defined_target (set (defined_list R)))
      (csr_rta08_CSDP_on Sharp (mu_of \<mu>)
        (set (defined_list R)) (set R))"
    using fin' pairs by simp
  have overlay: "csr_switch_overlay (set R)"
    by (rule check_csr_orthogonal_sound[OF ortho_ok])
  have D: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    using tt[unfolded csr_rta08_dependency_pairs_tt_def Let_def,
      simplified] by auto
  show ?thesis
    by (rule csr_switch_via_innermost_rta08_CSDP_on[
      OF overlay wf D exact])
qed

definition check_innermost_csr_or_rta08_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_innermost_csr_or_rta08_termination_proof I J i \<mu> R P prf =
    (case check_innermost_csr_termination_proof I J i \<mu> R P prf of
       Inr x \<Rightarrow> Inr x
     | Inl _ \<Rightarrow> check_innermost_csr_rta08_termination_proof
         J i \<mu> R P prf)"

lemma check_innermost_csr_or_rta08_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_innermost_csr_or_rta08_termination_proof
      I J i \<mu> R P prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof (cases "check_innermost_csr_termination_proof I J i \<mu> R P prf")
  case (Inl e)
  with ok have "isOK (check_innermost_csr_rta08_termination_proof
      J i \<mu> R P prf)"
    unfolding check_innermost_csr_or_rta08_termination_proof_def by simp
  then show ?thesis
    by (rule check_innermost_csr_rta08_termination_proof_sound[OF J])
next
  case (Inr x)
  then have "isOK (check_innermost_csr_termination_proof
      I J i \<mu> R P prf)" by simp
  then show ?thesis
    by (rule check_innermost_csr_termination_proof_sound[OF I J])
qed

end
