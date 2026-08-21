(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Typed_General_Redpair
  imports CSR_Muterm_Extended_Basic
    CSR_Muterm_Ext.CSR_Muterm_Innermost_Progress
begin

text \<open>
  The global orthogonal CSR switch is not strong enough for a minimal-chain
  processor: at a marked call we only know termination below that particular
  call.  The following local form carries this termination fact through the
  variant simulation.  This is the missing invariant needed by the MU-TERM
  interpretation for variables which are frozen before a collapsing step and
  become active afterwards.
\<close>

lemma csr_switch_selected_steps_variants_simulation_on:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and steps: "(s,t) \<in> (csr_switch_selected_step \<mu> R)\<^sup>*"
    and member: "s' \<in> csr_innermost_variants \<mu> R s"
    and inner_SN: "SN_on (innermost_csstep \<mu> R) {s'}"
  shows "\<exists>t'. t' \<in> csr_innermost_variants \<mu> R t \<and>
    (s',t') \<in> (innermost_csstep \<mu> R)\<^sup>*"
  using steps member inner_SN
proof (induct rule: rtrancl_induct)
  case base
  show ?case by (intro exI[of _ s'], use base in auto)
next
  case (step x y)
  from step.hyps(3)[OF step.prems(1-2)]
  obtain x' where x'_member:
      "x' \<in> csr_innermost_variants \<mu> R x"
    and prefix: "(s',x') \<in> (innermost_csstep \<mu> R)\<^sup>*"
    by blast
  have x'_SN: "SN_on (innermost_csstep \<mu> R) {x'}"
    by (rule steps_preserve_SN_on[OF prefix step.prems(2)])
  from csr_switch_selected_step_variants_simulation[
      OF ortho wf step.hyps(2) x'_member x'_SN]
  obtain y' where y'_member:
      "y' \<in> csr_innermost_variants \<mu> R y"
    and suffix: "(x',y') \<in> (innermost_csstep \<mu> R)\<^sup>*"
    by blast
  have path: "(s',y') \<in> (innermost_csstep \<mu> R)\<^sup>*"
    by (rule rtrancl_trans[OF prefix suffix])
  show ?case using y'_member path by blast
qed

lemma csr_switch_block_variants_simulation_on:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and block: "(s,t) \<in> csr_switch_block \<mu> R"
    and member: "s' \<in> csr_innermost_variants \<mu> R s"
    and inner_SN: "SN_on (innermost_csstep \<mu> R) {s'}"
  shows "\<exists>t'. t' \<in> csr_innermost_variants \<mu> R t \<and>
    (s',t') \<in> (innermost_csstep \<mu> R)\<^sup>+"
proof -
  from block obtain u where selected:
      "(s,u) \<in> (csr_switch_selected_step \<mu> R)\<^sup>*"
    and minimal: "(u,t) \<in> csr_switch_minimal_step \<mu> R"
    unfolding csr_switch_block_def by blast
  from csr_switch_selected_steps_variants_simulation_on[
      OF ortho wf selected member inner_SN]
  obtain u' where u'_member:
      "u' \<in> csr_innermost_variants \<mu> R u"
    and prefix: "(s',u') \<in> (innermost_csstep \<mu> R)\<^sup>*"
    by blast
  have u'_SN: "SN_on (innermost_csstep \<mu> R) {u'}"
    by (rule steps_preserve_SN_on[OF prefix inner_SN])
  have minimal_selected: "(u,t) \<in> csr_switch_selected_step \<mu> R"
    using csr_switch_minimal_step_subset_selected minimal by blast
  from csr_switch_selected_step_variants_simulation[
      OF ortho wf minimal_selected u'_member u'_SN]
  obtain t' where t'_member:
      "t' \<in> csr_innermost_variants \<mu> R t"
    and suffix: "(u',t') \<in> (innermost_csstep \<mu> R)\<^sup>+"
    using minimal by blast
  have path: "(s',t') \<in> (innermost_csstep \<mu> R)\<^sup>+"
    using prefix suffix by (rule rtrancl_trancl_trancl)
  show ?thesis using t'_member path by blast
qed

theorem csr_switch_overlay_innermost_termination_on:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and inner_SN: "SN_on (innermost_csstep \<mu> R) {s}"
  shows "SN_on (csstep \<mu> R) {s}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (csstep \<mu> R) {s}"
  let ?P = "\<lambda>(n :: nat) t. \<not> SN_on (csstep \<mu> R) {t} \<and>
    (n = 0 \<longrightarrow> t = s)"
  let ?Q = "\<lambda>(_ :: nat) x y. (x,y) \<in> csr_switch_block \<mu> R"
  have initial: "\<exists>t. ?P 0 t" using notSN by auto
  have successor: "\<And>t (n :: nat). ?P n t \<Longrightarrow>
      \<exists>u. ?P (Suc n) u \<and> ?Q n t u"
  proof -
    fix t n
    assume p: "?P n t"
    from notSN_has_csr_switch_block_successor[OF wf] p
    obtain u where u: "\<not> SN_on (csstep \<mu> R) {u}"
      and block: "(t,u) \<in> csr_switch_block \<mu> R" by blast
    show "\<exists>u. ?P (Suc n) u \<and> ?Q n t u"
      using u block by auto
  qed
  from dependent_nat_choice[OF initial successor]
  obtain ts where ts_choice:
      "\<forall>n. ?P n (ts n) \<and> ?Q n (ts n) (ts (Suc n))" ..
  have ts0: "ts 0 = s" using ts_choice by auto
  have blocks: "\<And>n. (ts n,ts (Suc n)) \<in> csr_switch_block \<mu> R"
    using ts_choice by auto
  let ?PV = "\<lambda>n u. u \<in> csr_innermost_variants \<mu> R (ts n) \<and>
    (s,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
  let ?QV = "\<lambda>(_ :: nat) u v.
    (u,v) \<in> (innermost_csstep \<mu> R)\<^sup>+"
  have variants_initial: "\<exists>u. ?PV 0 u"
    using csr_innermost_variants_self[of s \<mu> R] ts0 by auto
  have variants_successor: "\<And>u n. ?PV n u \<Longrightarrow>
      \<exists>v. ?PV (Suc n) v \<and> ?QV n u v"
  proof -
    fix u n
    assume member: "?PV n u"
    from member have su: "(s,u) \<in> (innermost_csstep \<mu> R)\<^sup>*"
      by blast
    have u_SN: "SN_on (innermost_csstep \<mu> R) {u}"
      by (rule steps_preserve_SN_on[OF su inner_SN])
    from csr_switch_block_variants_simulation_on[
        OF ortho wf blocks[of n] member[THEN conjunct1] u_SN]
    obtain v where v_member:
        "v \<in> csr_innermost_variants \<mu> R (ts (Suc n))"
      and uv: "(u,v) \<in> (innermost_csstep \<mu> R)\<^sup>+" by blast
    have sv: "(s,v) \<in> (innermost_csstep \<mu> R)\<^sup>*"
      using member[THEN conjunct2] uv
      by (rule rtrancl_trancl_trancl[THEN trancl_into_rtrancl])
    show "\<exists>v. ?PV (Suc n) v \<and> ?QV n u v"
      using v_member sv uv by blast
  qed
  from dependent_nat_choice[OF variants_initial variants_successor]
  obtain us where us_choice:
      "\<forall>n. ?PV n (us n) \<and> ?QV n (us n) (us (Suc n))" ..
  have us0_SN: "SN_on (innermost_csstep \<mu> R) {us 0}"
    by (rule steps_preserve_SN_on[OF _ inner_SN], use us_choice in blast)
  have plus_SN: "SN_on ((innermost_csstep \<mu> R)\<^sup>+) {us 0}"
    by (rule SN_on_trancl[OF us0_SN])
  have us_steps: "\<And>n. (us n,us (Suc n)) \<in>
      (innermost_csstep \<mu> R)\<^sup>+" using us_choice by blast
  from plus_SN[unfolded SN_on_def]
  show False using us_steps by blast
qed

lemma mu_Tinf_innermost_imp_mu_Tinf:
  fixes R :: "('f,string) trs"
  assumes ortho: "csr_switch_overlay R" and wf: "wf_trs R"
    and minimal: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  shows "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
proof (unfold mu_Tinf_def, intro CollectI conjI)
  from minimal have not_inner:
      "\<not> SN_on (innermost_csstep \<mu> R) {t}"
    unfolding mu_Tinf_def by blast
  show "\<not> SN_on (csstep \<mu> R) {t}"
  proof
    assume full: "SN_on (csstep \<mu> R) {t}"
    have "SN_on (innermost_csstep \<mu> R) {t}"
      by (rule SN_on_subset1[OF full innermost_csstep_subset_csstep])
    with not_inner show False by contradiction
  qed
  show "\<forall>s. mu_supt \<mu> t s \<longrightarrow> SN_on (csstep \<mu> R) {s}"
  proof (intro allI impI)
    fix s
    assume sub: "mu_supt \<mu> t s"
    from minimal sub have inner:
        "SN_on (innermost_csstep \<mu> R) {s}"
      unfolding mu_Tinf_def by blast
    show "SN_on (csstep \<mu> R) {s}"
      by (rule csr_switch_overlay_innermost_termination_on[OF ortho wf inner])
  qed
qed

text \<open>
  Exact typed MU-TERM steps embed into the RTA'08 chain semantics.  We use
  that semantics for the general recursive reduction-pair processor: in the
  collapsing case the marked target must be related to the selected active
  subterm by the checked projection and marking obligations.  It must not be
  treated as a pointwise fixed term.
\<close>

lemma muterm_typed_pair_step_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and step: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "(s,t) \<in> Rgt \<union> Rge \<and>
    ((s,t) \<notin> Rgt \<longrightarrow>
      (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and rfun: "\<not> is_Var r" and s: "s = l \<cdot> \<sigma>"
      and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from pairs_order pair have order: "(l,r) \<in> Rgt \<union> Rge" by auto
    show ?thesis
    proof (cases "(l,r) \<in> Rgt")
      case True
      have "(s,t) \<in> Rgt"
        unfolding s t by (rule subst.closedD[OF rp.subst_S True])
      then show ?thesis by auto
    next
      case False
      with order have weak: "(l,r) \<in> Rge" by auto
      have ordered: "(s,t) \<in> Rge"
        unfolding s t by (rule subst.closedD[OF rp.subst_NS weak])
      have residual: "muterm_noncollapsing_rrstep (P - Rgt) s t"
        unfolding muterm_noncollapsing_rrstep_def rrstep_def'
        using pair rfun s t False by blast
      show ?thesis unfolding muterm_typed_pair_step_def
        using ordered residual by auto
    qed
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> a b \<theta> where pair: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and x: "\<sigma> y = a \<cdot> \<theta>"
      and bridge: "(a,b) \<in> B" and t: "t = b \<cdot> \<theta>"
      unfolding muterm_collapsing_rrstep_def rrstep_def' by auto
    have bridge_weak: "(\<sigma> y,b \<cdot> \<theta>) \<in> Rge"
    proof -
      from bridges_order bridge have "(a,b) \<in> Rge" by auto
      then have "(a \<cdot> \<theta>,b \<cdot> \<theta>) \<in> Rge"
        by (rule subst.closedD[OF rp.subst_NS])
      then show ?thesis unfolding x .
    qed
    from pairs_order pair have order: "(l,Var y) \<in> Rgt \<union> Rge" by auto
    show ?thesis
    proof (cases "(l,Var y) \<in> Rgt")
      case True
      have first: "(l \<cdot> \<sigma>,\<sigma> y) \<in> Rgt"
        using subst.closedD[OF rp.subst_S True, of \<sigma>] by simp
      have ordered: "(s,t) \<in> Rgt"
        using rp.compat_S_NS first bridge_weak unfolding s t by auto
      then show ?thesis by auto
    next
      case False
      with order have weak: "(l,Var y) \<in> Rge" by auto
      have first: "(l \<cdot> \<sigma>,\<sigma> y) \<in> Rge"
        using subst.closedD[OF rp.subst_NS weak, of \<sigma>] by simp
      have ordered: "(s,t) \<in> Rge"
        using rp.trans_NS_point first bridge_weak unfolding s t by auto
      have residual: "muterm_collapsing_rrstep (P - Rgt) s (a \<cdot> \<theta>)"
        unfolding muterm_collapsing_rrstep_def
        using pair s x[symmetric] False by blast
      show ?thesis unfolding muterm_typed_pair_step_def rrstep_def'
        using ordered residual bridge t by auto
    qed
  qed
qed

lemma sharp_innermost_csdp_step_imp_innermost_csnrstep:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (shp f,n)"
    and marked_inj: "inj shp"
    and step: "(sharp_term shp s,v) \<in> innermost_csdp_step shp \<mu> R"
  shows "\<exists>t. v = sharp_term shp t \<and>
    (s,t) \<in> innermost_csnrstep \<mu> R"
proof (cases s)
  case (Var x)
  from step obtain p lr \<sigma> where
    rewrite: "(sharp_term shp s,v) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding innermost_csdp_step_def by auto
  have rewrite': "(Var x,v) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite unfolding Var by simp
  from rewrite' have "p = []"
    unfolding rstep_r_p_s_def' by (cases p, auto)
  with rewrite' have lr: "lr \<in> R" and lhs: "fst lr \<cdot> \<sigma> = Var x"
    unfolding rstep_r_p_s_def' by auto
  from wf lr have "\<exists>g ts. fst lr = Fun g ts"
    unfolding wf_trs_def by (cases lr, auto)
  then obtain g ts where "fst lr = Fun g ts" by blast
  with lhs show ?thesis by simp
next
  case (Fun f ss)
  from step obtain p lr \<sigma> where
    rewrite0: "(sharp_term shp s,v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond0: "csdp_step_cond shp \<mu> p (sharp_term shp s)"
    and inner: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csdp_step_def by blast
  have rewrite: "(Fun (shp f) ss,v) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite0 unfolding Fun by simp
  have cond: "csdp_step_cond shp \<mu> p (Fun (shp f) ss)"
    using cond0 unfolding Fun by simp
  have p_ne: "p \<noteq> []"
  proof
    assume "p = []"
    with rewrite have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun (shp f) ss"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have "\<exists>g ts. fst lr = Fun g ts"
      unfolding wf_trs_def by (cases lr, auto)
    then obtain g ts where l: "fst lr = Fun g ts" by blast
    from lhs l have g: "g = shp f" and len: "length ts = length ss"
      by auto
    from lr l g len have "defined R (shp f,length ss)"
      unfolding defined_def by (cases lr, auto)
    with fresh show False by contradiction
  qed
  then obtain i q where p: "p = i # q" by (cases p, auto)
  let ?t = "replace_at (Fun f ss) p (snd lr \<cdot> \<sigma>)"
  have rewrite': "(Fun f ss,?t) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite p unfolding rstep_r_p_s_def' by auto
  have v: "v = sharp_term shp ?t"
    using rewrite p unfolding rstep_r_p_s_def' by auto
  have cond': "csstep_cond \<mu> p (Fun f ss)"
  proof (unfold csstep_cond_def, intro allI impI)
    fix p1 j p2
    assume A: "p = p1 @ j # p2 \<and> p \<in> poss (Fun f ss)"
    show "\<exists>g us. Fun f ss |_ p1 = Fun g us \<and>
      j \<in> \<mu> (g,length us)"
    proof (cases p1)
      case Nil
      from cond[unfolded csdp_step_cond_def, rule_format,
          of "[]" j p2] A Nil
      show ?thesis using injD[OF marked_inj] by auto
    next
      case (Cons k qs)
      from cond[unfolded csdp_step_cond_def, rule_format,
          of p1 j p2] A Cons
      show ?thesis by auto
    qed
  qed
  have step': "(Fun f ss,?t) \<in> innermost_csnrstep \<mu> R"
    unfolding innermost_csnrstep_def innermost_csstep_p_def
    using p rewrite' cond' inner by blast
  show ?thesis using v step' Fun by auto
qed

lemma innermost_mu_Tinf_imp_SN_sharp_innermost_csdp:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (shp f,n)"
    and marked_inj: "inj shp"
    and Tinf: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  shows "SN_on (innermost_csdp_step shp \<mu> R) {sharp_term shp t}"
proof -
  from mu_Tinf_innermost_imp_first_root_step[OF Tinf]
  have SN: "SN_on (innermost_csnrstep \<mu> R) {t}" by blast
  show ?thesis
  proof (unfold SN_on_def, intro notI)
    assume "\<exists>ts. ts 0 \<in> {sharp_term shp t} \<and>
      (\<forall>i. (ts i,ts (Suc i)) \<in> innermost_csdp_step shp \<mu> R)"
    then obtain ts where init: "ts 0 = sharp_term shp t"
      and steps: "\<And>i. (ts i,ts (Suc i)) \<in>
        innermost_csdp_step shp \<mu> R" by auto
    have shaped: "\<And>i. \<exists>s. ts i = sharp_term shp s"
    proof -
      fix i
      show "\<exists>s. ts i = sharp_term shp s"
      proof (induct i)
        case 0
        show ?case using init by blast
      next
        case (Suc i)
        then obtain s where tsi: "ts i = sharp_term shp s" by blast
        from sharp_innermost_csdp_step_imp_innermost_csnrstep[
          OF wf fresh marked_inj, of s "ts (Suc i)"] steps[of i] tsi
        show ?case by auto
      qed
    qed
    have all_shaped: "\<forall>i. \<exists>s. ts i = sharp_term shp s"
      using shaped by blast
    from choice[OF all_shaped] obtain ss where
      shape: "\<And>i. ts i = sharp_term shp (ss i)" by blast
    have inject: "\<And>s u. sharp_term shp s = sharp_term shp u \<Longrightarrow> s = u"
    proof -
      fix s u
      assume eq: "sharp_term shp s = sharp_term shp u"
      show "s = u" using eq marked_inj
        by (cases s; cases u; auto dest: injD)
    qed
    have ss0: "ss 0 = t" by (rule inject, use init shape[of 0] in simp)
    have ss_steps: "\<And>i. (ss i,ss (Suc i)) \<in>
        innermost_csnrstep \<mu> R"
    proof -
      fix i
      from sharp_innermost_csdp_step_imp_innermost_csnrstep[
        OF wf fresh marked_inj, of "ss i" "ts (Suc i)"]
        steps[of i] shape[of i]
      obtain u where u: "ts (Suc i) = sharp_term shp u"
        and local: "(ss i,u) \<in> innermost_csnrstep \<mu> R" by auto
      have "u = ss (Suc i)" by (rule inject, use u shape[of "Suc i"] in simp)
      with local show "(ss i,ss (Suc i)) \<in> innermost_csnrstep \<mu> R"
        by simp
    qed
    from SN ss0 ss_steps show False unfolding SN_on_def by blast
  qed
qed

lemma SN_rel_min_interpreted_redpair_targeted:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and target_SN: "\<And>s t. (s,t) \<in> B \<Longrightarrow> SN_on A {t}"
    and target_good: "\<And>s t. (s,t) \<in> B \<Longrightarrow> G t"
    and pair_order: "\<And>s t. SN_on A {s} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (I s,I t) \<in> Rgt \<union> Rge"
    and pair_residual: "\<And>s t. SN_on A {s} \<Longrightarrow>
      (s,t) \<in> B \<Longrightarrow> (I s,I t) \<notin> Rgt \<Longrightarrow> (s,t) \<in> C"
    and steps_order: "\<And>s t. G s \<Longrightarrow> SN_on A {s} \<Longrightarrow>
      (s,t) \<in> A\<^sup>* \<Longrightarrow> (I s,I t) \<in> Rge"
    and fin: "SN_rel C A"
  shows "SN_rel B A"
proof (rule ccontr)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?PB = "A\<^sup>* O B O A\<^sup>*"
  let ?PC = "A\<^sup>* O C O A\<^sup>*"
  assume not_fin: "\<not> SN_rel B A"
  then obtain f where chain: "chain ?PB f"
    unfolding SN_rel_on_def SN_defs by auto
  have ex_mid: "\<forall>i. \<exists>a b. (f i,a) \<in> A\<^sup>* \<and>
      (a,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*"
  proof
    fix i
    from chain[rule_format, of i] obtain a b where
      pre: "(f i,a) \<in> A\<^sup>*" and pair: "(a,b) \<in> B"
      and post: "(b,f (Suc i)) \<in> A\<^sup>*" by auto
    show "\<exists>a b. (f i,a) \<in> A\<^sup>* \<and> (a,b) \<in> B \<and>
      (b,f (Suc i)) \<in> A\<^sup>*" using pre pair post by auto
  qed
  from choice[OF ex_mid] obtain a where choose_a:
      "\<forall>i. \<exists>b. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*" by auto
  from choice[OF choose_a] obtain b where chosen:
      "\<forall>i. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b i) \<in> B \<and> (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  from chosen have pre: "\<And>i. (f i,a i) \<in> A\<^sup>*"
    and pair: "\<And>i. (a i,b i) \<in> B"
    and post: "\<And>i. (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  have between: "(b i,a (Suc i)) \<in> A\<^sup>*" for i
    by (rule rtrancl_trans[OF post[of i] pre[of "Suc i"]])
  have b_sn: "SN_on A {b i}" for i by (rule target_SN[OF pair])
  have b_good: "G (b i)" for i by (rule target_good[OF pair])
  have a_sn: "SN_on A {a (Suc i)}" for i
  proof (rule ccontr)
    assume not_sn: "\<not> SN_on A {a (Suc i)}"
    from steps_notSN_on_source[OF between[of i] not_sn]
      b_sn[of i] show False by contradiction
  qed
  have weak: "(I (b i),I (a (Suc i))) \<in> Rge" for i
    by (rule steps_order[OF b_good b_sn between])
  have pord: "(I (a (Suc i)),I (b (Suc i))) \<in> Rgt \<union> Rge" for i
    by (rule pair_order[OF a_sn pair])
  let ?x = "\<lambda>i. I (a (Suc i))"
  have xstep: "(?x i,?x (Suc i)) \<in> Rge \<union> Rgt" for i
  proof (cases "(I (a (Suc i)),I (b (Suc i))) \<in> Rgt")
    case True
    from rp.compat_S_NS True weak[of "Suc i"] show ?thesis by auto
  next
    case False
    from False pord[of i] have first:
      "(I (a (Suc i)),I (b (Suc i))) \<in> Rge" by auto
    from rp.trans_NS_point[OF first weak[of "Suc i"]] show ?thesis by simp
  qed
  have xchain: "chain (Rge \<union> Rgt) ?x" using xstep by simp
  have sn0: "SN_on Rgt {?x 0}" using rp.SN unfolding SN_on_def by auto
  from non_strict_ending[OF xchain rp.compat_NS_S sn0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?x k,?x (Suc k)) \<in> Rge - Rgt" by auto
  have tail_pair: "(a (Suc (k+j)),b (Suc (k+j))) \<in> C" for k
  proof -
    have not_strict: "(I (a (Suc (k+j))),I (b (Suc (k+j)))) \<notin> Rgt"
    proof
      assume strict: "(I (a (Suc (k+j))),I (b (Suc (k+j)))) \<in> Rgt"
      have comp: "(I (a (Suc (k+j))),I (a (Suc (Suc (k+j))))) \<in> Rgt O Rge"
        by (rule relcompI[OF strict weak[of "Suc (k+j)"]])
      have "(?x (k+j),?x (Suc (k+j))) \<in> Rgt"
        by (rule rp.compat_S_NS[THEN subsetD, OF comp])
      moreover from tail[of "k+j"] have
        "(?x (k+j),?x (Suc (k+j))) \<notin> Rgt" by auto
      ultimately show False by contradiction
    qed
    show ?thesis by (rule pair_residual[OF a_sn pair not_strict])
  qed
  let ?h = "shift f (Suc j)"
  have residual_chain: "chain ?PC ?h"
  proof
    fix k
    have member: "(f (Suc (k+j)),f (Suc (Suc (k+j)))) \<in> ?PC"
      using pre[of "Suc (k+j)"] tail_pair[of k]
        post[of "Suc (k+j)"] by auto
    show "(?h k,?h (Suc k)) \<in> ?PC" using member by simp
  qed
  from fin have "SN_on ?PC UNIV" unfolding SN_rel_on_def .
  moreover have "\<not> SN_on ?PC UNIV"
    by (rule not_SN_onI[OF _ residual_chain], simp)
  ultimately show False by contradiction
qed

theorem finite_muterm_innermost_min_typed_dpp_redpair:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (shp f,n)"
    and marked_inj: "inj shp"
    and redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and rewrite_weak: "innermost_csdp_step shp \<mu> R \<subseteq> Rge"
    and fin: "finite_muterm_innermost_min_typed_dpp shp \<mu> R
      (P - Rgt) B"
  shows "finite_muterm_innermost_min_typed_dpp shp \<mu> R P B"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have weak_steps: "(innermost_csdp_step shp \<mu> R)\<^sup>* \<subseteq> Rge"
  proof -
    have "(innermost_csdp_step shp \<mu> R)\<^sup>* \<subseteq> Rge\<^sup>*"
      by (rule rtrancl_mono[OF rewrite_weak])
    also have "... = Rge" by (rule rp.rtrancl_NS)
    finally show ?thesis .
  qed
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair_targeted[
      OF redpair, where I="\<lambda>t. t" and G="\<lambda>_. True"])
    fix s t
    assume event: "(s,t) \<in>
      muterm_innermost_min_typed_pair_step shp \<mu> R P B"
    then obtain u where t: "t = sharp_term shp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    show "SN_on (innermost_csdp_step shp \<mu> R) {t}"
      unfolding t by (rule innermost_mu_Tinf_imp_SN_sharp_innermost_csdp[
        OF wf fresh marked_inj uT])
  next
    fix s t
    assume "(s,t) \<in>
      muterm_innermost_min_typed_pair_step shp \<mu> R P B"
    show "True" by simp
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step shp \<mu> R) {s}"
      and event: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step shp \<mu> R P B"
    from event have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from muterm_typed_pair_step_redpair_order[
      OF redpair pairs_order bridges_order typed]
    show "(s,t) \<in> Rgt \<union> Rge" by blast
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step shp \<mu> R) {s}"
      and event: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step shp \<mu> R P B"
      and not_strict: "(s,t) \<notin> Rgt"
    from event have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      and source: "innermost_pair_source shp \<mu> R s"
      and target: "\<exists>u. t = sharp_term shp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from muterm_typed_pair_step_redpair_order[
      OF redpair pairs_order bridges_order typed] not_strict
    have residual: "(s,t) \<in> muterm_typed_pair_step (P - Rgt) B" by blast
    show "(s,t) \<in>
      muterm_innermost_min_typed_pair_step shp \<mu> R (P - Rgt) B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def
      using residual source target by auto
  next
    fix s t
    assume good: "True"
      and source_SN: "SN_on (innermost_csdp_step shp \<mu> R) {s}"
      and steps: "(s,t) \<in> (innermost_csdp_step shp \<mu> R)\<^sup>*"
    show "(s,t) \<in> Rge" by (rule weak_steps[THEN subsetD, OF steps])
  next
    show "SN_rel
      (muterm_innermost_min_typed_pair_step shp \<mu> R (P - Rgt) B)
      (innermost_csdp_step shp \<mu> R)"
      using fin unfolding finite_muterm_innermost_min_typed_dpp_def .
  qed
qed

theorem finite_muterm_innermost_min_typed_dpp_usable_redpair:
  fixes R U P B Rgt Rge ::
    "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_innermost_ur_closed R U \<mu> (P \<union> B)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and target: "muterm_innermost_typed_target_safe R U \<mu> P B"
    and redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and usable_weak: "U \<subseteq> Rge"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp \<mu> R
      (P - Rgt) B"
  shows "finite_muterm_innermost_min_typed_dpp Sharp \<mu> R P B"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from closed have U_R: "U \<subseteq> R"
    and U_closed: "\<And>l r. (l,r) \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
    unfolding muterm_innermost_ur_closed_def by auto
  have weak_step: "csdp_step Sharp \<mu> U \<subseteq> Rge"
  proof -
    have "csdp_step Sharp \<mu> U \<subseteq> rstep U"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    also have "... \<subseteq> rstep Rge" by (rule rstep_mono[OF usable_weak])
    also have "... \<subseteq> Rge" by (rule rp.rstep_NS)
    finally show ?thesis .
  qed
  have weak_steps: "(csdp_step Sharp \<mu> U)\<^sup>* \<subseteq> Rge"
  proof -
    have "(csdp_step Sharp \<mu> U)\<^sup>* \<subseteq> Rge\<^sup>*"
      by (rule rtrancl_mono[OF weak_step])
    also have "... = Rge" by (rule rp.rtrancl_NS)
    finally show ?thesis .
  qed
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair_targeted[
      OF redpair, where I="\<lambda>t. t" and
        G="\<lambda>t. \<exists>f ts. t = Fun (Sharp f) ts \<and>
          \<mu> (Sharp f,length ts) = \<mu> (f,length ts) \<and>
          muterm_innermost_ur_safe R U \<mu> t"])
    fix s t
    assume event: "(s,t) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    then obtain u where t: "t = sharp_term Sharp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    show "SN_on (innermost_csdp_step Sharp \<mu> R) {t}"
      unfolding t by (rule innermost_mu_Tinf_imp_SN_sharp_innermost_csdp[
        OF wf fresh inj_Sharp uT])
  next
    fix s t
    assume event: "(s,t) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    then have typed: "(s,t) \<in>
      muterm_innermost_typed_pair_step Sharp \<mu> R P B"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    from muterm_innermost_typed_target_safeD[OF target typed]
    obtain f ts where t: "t = Fun (Sharp f) ts"
      and marked: "\<mu> (Sharp f,length ts) = \<mu> (f,length ts)"
      and safe: "muterm_innermost_ur_safe R U \<mu> t" by blast
    show "\<exists>f ts. t = Fun (Sharp f) ts \<and>
      \<mu> (Sharp f,length ts) = \<mu> (f,length ts) \<and>
      muterm_innermost_ur_safe R U \<mu> t"
      using t marked safe by blast
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step Sharp \<mu> R) {s}"
      and event: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    from event have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from muterm_typed_pair_step_redpair_order[
      OF redpair pairs_order bridges_order typed]
    show "(s,t) \<in> Rgt \<union> Rge" by blast
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step Sharp \<mu> R) {s}"
      and event: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
      and not_strict: "(s,t) \<notin> Rgt"
    from event have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      and source: "innermost_pair_source Sharp \<mu> R s"
      and target_inv: "\<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from muterm_typed_pair_step_redpair_order[
      OF redpair pairs_order bridges_order typed] not_strict
    have residual: "(s,t) \<in> muterm_typed_pair_step (P - Rgt) B" by blast
    show "(s,t) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R (P - Rgt) B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def
      using residual source target_inv by auto
  next
    fix s t
    assume good: "\<exists>f ts. s = Fun (Sharp f) ts \<and>
        \<mu> (Sharp f,length ts) = \<mu> (f,length ts) \<and>
        muterm_innermost_ur_safe R U \<mu> s"
      and source_SN: "SN_on (innermost_csdp_step Sharp \<mu> R) {s}"
      and steps: "(s,t) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    from good obtain f ss where s: "s = Fun (Sharp f) ss"
      and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
      and safe: "muterm_innermost_ur_safe R U \<mu> s" by blast
    have full_steps: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      using steps rtrancl_mono[OF innermost_csdp_step_subset_csdp_step]
      by blast
    have safe': "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)"
      using safe unfolding s .
    have full_steps': "(Fun (Sharp f) ss,t) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*" using full_steps unfolding s .
    have result: "(Fun (Sharp f) ss,t) \<in>
        (csdp_step Sharp \<mu> U)\<^sup>* \<and>
        muterm_innermost_ur_safe R U \<mu> t \<and>
        (\<exists>ts. t = Fun (Sharp f) ts \<and> length ts = length ss)"
    proof (rule muterm_innermost_ur_safe_sharp_csdp_steps[
        where R=R and U=U and \<mu>=\<mu> and f=f and ss=ss and v=t])
      show "wf_trs R" by (rule wf)
      show "\<And>g n. \<not> defined R (Sharp g,n)" by (rule fresh)
      show "U \<subseteq> R" by (rule U_R)
      show "\<And>l r. (l,r) \<in> U \<Longrightarrow>
        csr_u3_root_rules_closed R U r (mu_fun_poss \<mu> r)"
        by (rule U_closed)
      show "rhs_mu_vars_condition \<mu> U" by (rule conservative)
      show "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)" by (rule marked)
      show "muterm_innermost_ur_safe R U \<mu> (Fun (Sharp f) ss)"
        by (rule safe')
      show "(Fun (Sharp f) ss,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
        by (rule full_steps')
    qed
    have "(s,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
      using result unfolding s by blast
    then show "(s,t) \<in> Rge" by (rule weak_steps[THEN subsetD])
  next
    show "SN_rel
      (muterm_innermost_min_typed_pair_step Sharp \<mu> R (P - Rgt) B)
      (innermost_csdp_step Sharp \<mu> R)"
      using fin unfolding finite_muterm_innermost_min_typed_dpp_def .
  qed
qed

definition muterm_innermost_typed_ur_redpair_proc where
  "muterm_innermost_typed_ur_redpair_proc J \<mu> rp Premove U B dpp =
    check_return (do {
      rel_impl_redpair rp;
      let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
      check (muterm_expanded_innermost_usable_check
          (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''typed innermost MU-TERM usable-rule or shape check failed''));
      rel_impl_ns rp (U @ B @ pns)
        <+? (\<lambda>s. showsl_lit
          (STR ''problem weakly orienting typed innermost MU-TERM rules, unhiding rules, or pairs\<newline>'' ) \<circ> s);
      rel_impl_s rp ps
        <+? (\<lambda>s. showsl_lit
          (STR ''problem strictly orienting typed innermost MU-TERM pairs\<newline>'' ) \<circ> s)
    }) (dpp_spec.delete_pairs J dpp Premove)"

theorem muterm_innermost_typed_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_innermost_typed_ur_redpair_proc J \<mu> rp
      Premove U B dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.rules J dpp')) (set (dpp_ops.pairs J dpp')) (set B)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp)) (set (dpp_ops.pairs J dpp)) (set B)"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_innermost_typed_ur_redpair_proc_def
      Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and usable: "muterm_expanded_innermost_usable_check
      (rules dpp) U \<mu> (pairs dpp) B"
    and weak: "isOK (rel_impl_ns rp (U @ B @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ B @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have ex_rel: "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule all_rel[THEN spec])
  from ex_rel obtain S NS NST where
    rel_prop: "rel_impl_prop rp ?all S NS NST" by auto
  from rel_prop strict weak subst sn standard
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and B_NS: "set B \<subseteq> NS"
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
  from muterm_expanded_innermost_usable_check_sound[OF usable]
  have closed_sem: "muterm_innermost_ur_closed
      (set (rules dpp)) (set U) (mu_of \<mu>)
      (set (pairs dpp) \<union> set B)"
    and conservative_sem: "rhs_mu_vars_condition (mu_of \<mu>) (set U)"
    and target_sem: "muterm_innermost_typed_target_safe
      (set (rules dpp)) (set U) (mu_of \<mu>) (set (pairs dpp)) (set B)"
    by blast+
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq>
      set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have step_sub: "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B) \<subseteq>
    muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - set Premove) (set B)"
  proof
    fix st
    assume member: "st \<in> muterm_innermost_min_typed_pair_step
      Sharp (mu_of \<mu>) (set (rules dpp)) (set (pairs dpp) - S) (set B)"
    from member have typed: "st \<in> muterm_innermost_typed_pair_step
      Sharp (mu_of \<mu>) (set (rules dpp)) (set (pairs dpp) - S) (set B)"
      and target_inv: "st \<in> {(s,t). \<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf (mu_of \<mu>)
          (innermost_csstep (mu_of \<mu>) (set (rules dpp)))}"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    from muterm_innermost_typed_pair_step_mono_pairs[OF sub] typed
    have typed': "st \<in> muterm_innermost_typed_pair_step
      Sharp (mu_of \<mu>) (set (rules dpp))
        (set (pairs dpp) - set Premove) (set B)" by blast
    show "st \<in> muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - set Premove) (set B)"
      unfolding muterm_innermost_min_typed_pair_step_def
      using typed' target_inv by auto
  qed
  have fin_S: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B)"
    unfolding finite_muterm_innermost_min_typed_dpp_def
    by (rule SN_rel_mono[OF step_sub subset_refl
      fin[unfolded pairs' rules' finite_muterm_innermost_min_typed_dpp_def]])
  show ?thesis
    by (rule finite_muterm_innermost_min_typed_dpp_usable_redpair[
      OF wf fresh closed_sem conservative_sem target_sem redpair orient B_NS
        U_NS fin_S])
qed

lemma muterm_innermost_min_typed_relto_witness:
  assumes step: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B O
      (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> B))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> B))\<^sup>* \<and>
    (s,t) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_innermost_min_typed_pair_step Sharp \<mu> R {(l,r)} B O
      (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from step obtain a b where
    pre: "(s,a) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    and post: "(b,t) \<in> (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  from event have typed: "(a,b) \<in> muterm_typed_pair_step P B"
    and source: "innermost_pair_source Sharp \<mu> R a"
    and target_inv: "\<exists>u. b = sharp_term Sharp u \<and>
      u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def by auto
  have cs_sub: "csdp_step Sharp \<mu> R \<subseteq>
      csdp_step Sharp \<mu> (R \<union> B)"
  proof
    fix st
    assume member: "st \<in> csdp_step Sharp \<mu> R"
    then obtain x y p lr \<tau> where st: "st = (x,y)"
      and cond: "csdp_step_cond Sharp \<mu> p x"
      and raw: "(x,y) \<in> rstep_r_p_s R lr p \<tau>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lr: "lr \<in> R"
      unfolding rstep_r_p_s_def Let_def by auto
    have raw': "(x,y) \<in> rstep_r_p_s (R \<union> B) lr p \<tau>"
      using raw lr unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (R \<union> B)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have base_sub: "innermost_csdp_step Sharp \<mu> R \<subseteq>
      csdp_step Sharp \<mu> (R \<union> B)"
    by (rule subset_trans[OF innermost_csdp_step_subset_csdp_step cs_sub])
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (R \<union> B))\<^sup>*"
    using pre rtrancl_mono[OF base_sub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (R \<union> B))\<^sup>*"
    using post rtrancl_mono[OF base_sub] by blast
  from typed have cases:
      "muterm_noncollapsing_rrstep P a b \<or>
       (\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by blast
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P a b"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and rfun: "\<not> is_Var r" and a: "a = l \<cdot> \<sigma>"
      and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,r)} B"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
      using rfun a b by auto
    have one_inner: "(a,b) \<in>
      muterm_innermost_typed_pair_step Sharp \<mu> R {(l,r)} B"
      unfolding muterm_innermost_typed_pair_step_def using one source by auto
    have one_min: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R {(l,r)} B"
      unfolding muterm_innermost_min_typed_pair_step_def
      using one_inner target_inv by auto
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x=r in exI)
      apply (rule_tac x=\<sigma> in exI)
      using pair pre' post' pre one_min post unfolding a b by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P a x \<and>
      (x,b) \<in> rrstep B"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep B" by blast
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one_coll: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} B"
      unfolding muterm_typed_pair_step_def using one_coll bridge by auto
    have one_inner: "(a,b) \<in>
      muterm_innermost_typed_pair_step Sharp \<mu> R {(l,Var y)} B"
      unfolding muterm_innermost_typed_pair_step_def using one source by auto
    have one_min: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R {(l,Var y)} B"
      unfolding muterm_innermost_min_typed_pair_step_def
      using one_inner target_inv by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (R \<union> B)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (R \<union> B))\<^sup>*"
      using bridge' post' by auto
    have post_var: "(Var y \<cdot> \<sigma>,t) \<in>
        (csdp_step Sharp \<mu> (R \<union> B))\<^sup>*"
      using post'' x by simp
    have whole: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_innermost_min_typed_pair_step Sharp \<mu> R
        {(l,Var y)} B O
      (innermost_csdp_step Sharp \<mu> R)\<^sup>*"
      using pre one_min post by blast
    show ?thesis using pair pre'[unfolded a] post_var whole by blast
  qed
qed

lemma muterm_innermost_min_typed_pair_step_mono_pairs:
  assumes sub: "P \<subseteq> Q"
  shows "muterm_innermost_min_typed_pair_step shp \<mu> R P B \<subseteq>
    muterm_innermost_min_typed_pair_step shp \<mu> R Q B"
proof
  fix st
  assume member: "st \<in> muterm_innermost_min_typed_pair_step shp \<mu> R P B"
  then have typed: "st \<in> muterm_innermost_typed_pair_step shp \<mu> R P B"
    and target: "st \<in> {(s,t). \<exists>u. t = sharp_term shp u \<and>
      u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)}"
    unfolding muterm_innermost_min_typed_pair_step_def by auto
  from muterm_innermost_typed_pair_step_mono_pairs[OF sub] typed
  have typed': "st \<in> muterm_innermost_typed_pair_step shp \<mu> R Q B"
    by blast
  show "st \<in> muterm_innermost_min_typed_pair_step shp \<mu> R Q B"
    unfolding muterm_innermost_min_typed_pair_step_def
    using typed' target by auto
qed

lemma check_muterm_innermost_min_typed_dep_graph_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R B P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>) (set R)
        (set P \<inter> set C) (set B)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set B)"
proof -
  let ?PS = "set P"
  let ?RB = "set (R @ B)"
  let ?S = "innermost_csdp_step Sharp (mu_of \<mu>) (set R)"
  let ?Q = "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
    (set R) ?PS (set B)"
  show ?thesis
    unfolding finite_muterm_innermost_min_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?S\<^sup>* O ?Q O ?S\<^sup>*)"
    then obtain ch where chain: "\<And>i.
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O ?Q O ?S\<^sup>*" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?PS \<and>
      (ch i,l \<cdot> \<sigma>) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(l,r)} (set B) O ?S\<^sup>*"
    proof
      fix i
      from muterm_innermost_min_typed_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?PS \<and>
        (ch i,l \<cdot> \<sigma>) \<in>
          (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in>
          (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
          muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
            (set R) {(l,r)} (set B) O ?S\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma>) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(s i,r)} (set B) O ?S\<^sup>*" by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma>) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(s i,t i)} (set B) O ?S\<^sup>*" by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(s i,t i)} (set B) O ?S\<^sup>*" by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?PS"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(s i,t i)} (set B) O ?S\<^sup>*" by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,
        s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?RB)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    have selected: "\<exists>prf Cs n. (Some prf,Cs) \<in> set edps \<and>
      (\<forall>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs)"
      using check pair steps
      apply (rule check_muterm_typed_dep_graph_select_component)
      done
    from selected obtain p0 Cs n where mem: "(Some p0,Cs) \<in> set edps"
      and CP_all: "\<forall>m. (s (m+n),t (m+n)) \<in> ?PS \<inter> set Cs"
      by auto
    from CP_all have CP: "\<And>m.
      (s (m+n),t (m+n)) \<in> ?PS \<inter> set Cs" by auto
    let ?tail = "\<lambda>m. ch (m+n)"
    let ?QC = "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set R) (?PS \<inter> set Cs) (set B)"
    have tail_step: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      ?S\<^sup>* O ?QC O ?S\<^sup>*"
    proof -
      fix m
      have singleton: "{(s (m+n),t (m+n))} \<subseteq> ?PS \<inter> set Cs"
        using CP[of m] by auto
      have mono: "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
          (set R) {(s (m+n),t (m+n))} (set B) \<subseteq> ?QC"
        by (rule muterm_innermost_min_typed_pair_step_mono_pairs[OF singleton])
      have inc: "?S\<^sup>* O
          muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
            (set R) {(s (m+n),t (m+n))} (set B) O ?S\<^sup>*
        \<subseteq> ?S\<^sup>* O ?QC O ?S\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      have member: "(ch (m+n),ch (Suc (m+n))) \<in>
          ?S\<^sup>* O ?QC O ?S\<^sup>*"
        by (rule inc[THEN subsetD, OF typed[of "m+n"]])
      show "(?tail m,?tail (Suc m)) \<in> ?S\<^sup>* O ?QC O ?S\<^sup>*"
        using member by simp
    qed
    have tail_sn: "SN (?S\<^sup>* O ?QC O ?S\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_innermost_min_typed_dpp_def SN_rel_on_def .
    have tail_chain: "chain (?S\<^sup>* O ?QC O ?S\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN (?S\<^sup>* O ?QC O ?S\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed

lemma finite_csr_dpp_imp_finite_muterm_innermost_min_typed_noncollapsing:
  assumes noncoll: "\<forall>dp\<in>P. is_Fun (snd dp)"
    and fin: "finite_csr_dpp shp \<mu> P R"
  shows "finite_muterm_innermost_min_typed_dpp shp \<mu> R P B"
proof -
  have pair_sub: "muterm_innermost_min_typed_pair_step shp \<mu> R P B
      \<subseteq> rrstep P"
  proof
    fix st
    assume member: "st \<in>
      muterm_innermost_min_typed_pair_step shp \<mu> R P B"
    then have typed: "st \<in> muterm_typed_pair_step P B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    obtain s t where st: "st = (s,t)" by (cases st)
    from typed[unfolded st muterm_typed_pair_step_def]
    have cases: "muterm_noncollapsing_rrstep P s t \<or>
      (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
      by auto
    from cases show "st \<in> rrstep P"
    proof
      assume "muterm_noncollapsing_rrstep P s t"
      then show ?thesis unfolding st muterm_noncollapsing_rrstep_def by blast
    next
      assume "\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B"
      then obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
        unfolding muterm_collapsing_rrstep_def by blast
      from noncoll[rule_format, OF pair] have False by simp
      then show ?thesis ..
    qed
  qed
  from fin have full: "SN_rel (rrstep P) (csdp_step shp \<mu> R)"
    unfolding finite_csr_dpp_def .
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def
    by (rule SN_rel_mono[OF pair_sub innermost_csdp_step_subset_csdp_step full])
qed

text \<open>
  The arbitrary-term MU-TERM interpretation differs at one crucial point from
  the older extended-basic interpretation: a nonterminating term does not get
  a rewrite-list wrapper, but its active arguments are still interpreted.
  Keeping this definition separate avoids changing the already certified
  extended-basic processors while the general typed processor is proved.
\<close>

locale muterm_i3 =
  fixes Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "('f \<times> nat) set"
    and cn :: "'f \<times> nat"
  assumes wf: "wf_trs (set Rs)"
begin

interpretation old: muterm_i2 Rs \<mu> \<Delta> cn
  by (unfold_locales, rule wf)

fun i3 :: "('f,'v) term \<Rightarrow> ('f,'v) term"
where
  "i3 (Var x) = Var x"
| "i3 (Fun f ts) =
    (if SN_on (csstep \<mu> (set Rs)) {Fun f ts}
     then old.i2 (Fun f ts)
     else Fun f (map (\<lambda>(i,t).
       if i \<in> \<mu> (f,length ts) then i3 t else t)
       (zip [0..<length ts] ts)))"

definition i3_args where
  "i3_args f ts = map (\<lambda>(i,t).
    if i \<in> \<mu> (f,length ts) then i3 t else t)
      (zip [0..<length ts] ts)"

lemma i3_args_length[simp]: "length (i3_args f ts) = length ts"
  unfolding i3_args_def by simp

lemma i3_args_nth:
  assumes i: "i < length ts"
  shows "i3_args f ts ! i =
    (if i \<in> \<mu> (f,length ts) then i3 (ts ! i) else ts ! i)"
  using i unfolding i3_args_def
  by (simp add: nth_zip)

lemma i3_Fun:
  "i3 (Fun f ts) =
    (if SN_on (csstep \<mu> (set Rs)) {Fun f ts}
     then old.i2 (Fun f ts)
     else Fun f (i3_args f ts))"
  unfolding i3_args_def by simp

definition i3_subst where
  "i3_subst t \<sigma> x =
    (if x \<in> mu_vars_term \<mu> t then i3 (\<sigma> x) else \<sigma> x)"

fun i3_bracket :: "('f,'v) term \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) term"
where
  "i3_bracket (Var x) \<sigma> = i3 (\<sigma> x)"
| "i3_bracket (Fun f ts) \<sigma> = Fun f
    (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"

lemma i3_bracket_Fun_nth:
  assumes i: "i < length ts"
  shows "args (i3_bracket (Fun f ts) \<sigma>) ! i =
    (if i \<in> \<mu> (f,length ts) then i3_bracket (ts ! i) \<sigma>
     else (ts ! i) \<cdot> \<sigma>)"
  using i by (simp add: nth_zip)

lemma i3_bracket_as_subst:
  assumes disj: "mu_vars_term \<mu> t \<inter> non_mu_vars_term \<mu> t = {}"
  shows "i3_bracket t \<sigma> = t \<cdot> i3_subst t \<sigma>"
  using disj
proof (induct t)
  case (Var x)
  then show ?case unfolding i3_subst_def mu_vars_term_def by simp
next
  case (Fun f ts)
  have lists: "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) =
      map (\<lambda>t. t \<cdot> i3_subst (Fun f ts) \<sigma>) ts"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts)) =
        length (map (\<lambda>t. t \<cdot> i3_subst (Fun f ts) \<sigma>) ts)"
      by simp
    fix i
    assume imap: "i < length (map (\<lambda>(i,t).
      if i \<in> \<mu> (f,length ts) then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"
    then have i: "i < length ts" by simp
    show "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
        then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) ! i =
      map (\<lambda>t. t \<cdot> i3_subst (Fun f ts) \<sigma>) ts ! i"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have child_disj: "mu_vars_term \<mu> (ts ! i) \<inter>
          non_mu_vars_term \<mu> (ts ! i) = {}"
      proof (rule ccontr)
        assume "mu_vars_term \<mu> (ts ! i) \<inter>
            non_mu_vars_term \<mu> (ts ! i) \<noteq> {}"
        then obtain x where xa: "x \<in> mu_vars_term \<mu> (ts ! i)"
          and xn: "x \<in> non_mu_vars_term \<mu> (ts ! i)" by blast
        have "x \<in> mu_vars_term \<mu> (Fun f ts)"
          by (rule mu_vars_term_active_argI[OF i True xa])
        moreover have "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
          by (rule non_mu_vars_term_active_argI[OF i True xn])
        ultimately show False using Fun.prems by blast
      qed
      have IH: "i3_bracket (ts ! i) \<sigma> =
          (ts ! i) \<cdot> i3_subst (ts ! i) \<sigma>"
        by (rule Fun.hyps[OF nth_mem[OF i] child_disj])
      have subst_eq: "(ts ! i) \<cdot> i3_subst (ts ! i) \<sigma> =
          (ts ! i) \<cdot> i3_subst (Fun f ts) \<sigma>"
      proof (rule term_subst_eq)
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        show "i3_subst (ts ! i) \<sigma> x = i3_subst (Fun f ts) \<sigma> x"
        proof (cases "x \<in> mu_vars_term \<mu> (ts ! i)")
          case True
          have parent: "x \<in> mu_vars_term \<mu> (Fun f ts)"
            by (rule mu_vars_term_active_argI[OF i `i \<in> \<mu> (f,length ts)` True])
          show ?thesis unfolding i3_subst_def using True parent by simp
        next
          case False
          from vars_term_active_or_inactive[OF x] False
          have child_inactive: "x \<in> non_mu_vars_term \<mu> (ts ! i)" by blast
          have parent_inactive: "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
            by (rule non_mu_vars_term_active_argI[OF i `i \<in> \<mu> (f,length ts)` child_inactive])
          have parent_not_active: "x \<notin> mu_vars_term \<mu> (Fun f ts)"
            using Fun.prems parent_inactive by blast
          show ?thesis unfolding i3_subst_def
            using False parent_not_active by simp
        qed
      qed
      show ?thesis using i True IH subst_eq by (simp add: nth_zip)
    next
      case False
      have inactive: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
          x \<notin> mu_vars_term \<mu> (Fun f ts)"
      proof -
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        have parent_inactive: "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
          apply (rule non_mu_vars_term_inactive_argI)
            apply (rule i)
           apply (rule False)
          apply (rule x)
          done
        show "x \<notin> mu_vars_term \<mu> (Fun f ts)"
          using Fun.prems parent_inactive by blast
      qed
      have subst_eq: "(ts ! i) \<cdot> \<sigma> =
          (ts ! i) \<cdot> i3_subst (Fun f ts) \<sigma>"
        by (rule term_subst_eq, simp add: i3_subst_def inactive)
      show ?thesis using i False subst_eq by (simp add: nth_zip)
    qed
  qed
  show ?case using lists by simp
qed

lemma i3_equals_bracket:
  assumes roots: "\<And>p. p \<in> mu_fun_poss \<mu> t \<Longrightarrow>
    root (t |_ p) \<in> Some ` \<Delta>"
  shows "i3 (t \<cdot> \<sigma>) = i3_bracket t \<sigma>"
  using roots
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have root_delta: "(f,length ts) \<in> \<Delta>"
    using Fun.prems[of "[]"] by auto
  let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
  have args: "i3_args f ?ss = args (i3_bracket (Fun f ts) \<sigma>)"
  proof (rule nth_equalityI)
    show "length (i3_args f ?ss) =
      length (args (i3_bracket (Fun f ts) \<sigma>))" by simp
    fix i
    assume ia: "i < length (i3_args f ?ss)"
    then have i: "i < length ts" by simp
    show "i3_args f ?ss ! i = args (i3_bracket (Fun f ts) \<sigma>) ! i"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have sub_roots: "\<And>p. p \<in> mu_fun_poss \<mu> (ts ! i) \<Longrightarrow>
          root (ts ! i |_ p) \<in> Some ` \<Delta>"
      proof -
        fix p
        assume p: "p \<in> mu_fun_poss \<mu> (ts ! i)"
        have "i # p \<in> mu_fun_poss \<mu> (Fun f ts)"
          using i True p by auto
        from Fun.prems[OF this]
        show "root (ts ! i |_ p) \<in> Some ` \<Delta>" using i p by simp
      qed
      have IH: "i3 ((ts ! i) \<cdot> \<sigma>) = i3_bracket (ts ! i) \<sigma>"
        by (rule Fun.hyps[OF nth_mem[OF i] sub_roots])
      show ?thesis using i True IH
        by (simp add: i3_args_nth i3_bracket_Fun_nth)
    next
      case False
      then show ?thesis using i
        by (simp add: i3_args_nth i3_bracket_Fun_nth)
    qed
  qed
  show ?case
  proof (cases "SN_on (csstep \<mu> (set Rs)) {Fun f ?ss}")
    case False
    have source: "Fun f ts \<cdot> \<sigma> = Fun f ?ss" by simp
    have i3_value: "i3 (Fun f ?ss) = Fun f (i3_args f ?ss)"
      using False by (simp add: i3_Fun i3_args_def)
    show ?thesis unfolding source i3_value using args by simp
  next
    case True
    have old_args: "old.i2_args f ?ss = i3_args f ?ss"
    proof (rule nth_equalityI)
      show "length (old.i2_args f ?ss) = length (i3_args f ?ss)" by simp
      fix i
      assume ia: "i < length (old.i2_args f ?ss)"
      then have i: "i < length ts" by simp
      show "old.i2_args f ?ss ! i = i3_args f ?ss ! i"
      proof (cases "i \<in> \<mu> (f,length ts)")
        case False
        then show ?thesis using i
          by (simp add: old.i2_args_nth i3_args_nth)
      next
        case True
        have empty: "[] \<in> mu_poss \<mu> ((ts ! i) \<cdot> \<sigma>)"
          by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
        have pos: "i # [] \<in> mu_poss \<mu> (Fun f ?ss)"
          using i True empty by auto
        from SN_on_mu_pos[OF wf pos `SN_on (csstep \<mu> (set Rs)) {Fun f ?ss}`]
        have sub_SN: "SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
          using i by simp
        have eq: "i3 ((ts ! i) \<cdot> \<sigma>) = old.i2 ((ts ! i) \<cdot> \<sigma>)"
          using sub_SN by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
        show ?thesis using i True eq
          by (simp add: old.i2_args_nth i3_args_nth)
      qed
    qed
    have old_root: "old.i2 (Fun f ?ss) = Fun f (old.i2_args f ?ss)"
      using True root_delta by (simp add: old.i2_Fun old.i2_args_def)
    show ?thesis using True old_root old_args args by simp
  qed
qed

lemma i3_projects_self_total:
  "(i3 t,t) \<in> (rstep (ce_trs cn))\<^sup>*"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  show ?case
  proof (cases "SN_on (csstep \<mu> (set Rs)) {Fun f ts}")
    case True
    from old.i2_projects_self_total[of "Fun f ts"]
    show ?thesis using True by simp
  next
    case False
    let ?us = "map (\<lambda>(i,t).
      if i \<in> \<mu> (f,length ts) then i3 t else t)
      (zip [0..<length ts] ts)"
    have len: "length ?us = length ts" by simp
    have args: "\<forall>i<length ?us.
      (?us ! i,ts ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
    proof (intro allI impI)
      fix i
      assume iu: "i < length ?us"
      then have i: "i < length ts" by simp
      show "(?us ! i,ts ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
      proof (cases "i \<in> \<mu> (f,length ts)")
        case True
        from Fun.hyps[OF nth_mem[OF i]] show ?thesis
          using i True by (simp add: nth_zip)
      next
        case False
        then show ?thesis using i by (simp add: nth_zip)
      qed
    qed
    have "(Fun f ?us,Fun f ts) \<in> (rstep (ce_trs cn))\<^sup>*"
      by (rule args_rsteps_imp_rsteps[OF len args])
    then show ?thesis using False by simp
  qed
qed

lemma i3_lhs_subst_projects_value:
  assumes x: "x \<in> vars_term l"
  shows "(i3_subst l \<sigma> x, \<sigma> x) \<in> (rstep (ce_trs cn))\<^sup>*"
proof (cases "x \<in> mu_vars_term \<mu> l")
  case False
  then show ?thesis unfolding i3_subst_def by simp
next
  case True
  from i3_projects_self_total[of "\<sigma> x"]
  show ?thesis unfolding i3_subst_def using True by simp
qed

lemma i3_lhs_subst_to_bracket_rsteps:
  assumes active_sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
  shows "(r \<cdot> i3_subst l \<sigma>, i3_bracket r \<sigma>)
    \<in> (rstep (ce_trs cn))\<^sup>*"
  using active_sub
proof (induct r)
  case (Var x)
  have active: "x \<in> mu_vars_term \<mu> (Var x)"
    unfolding mu_vars_term_def by simp
  from Var.prems active have "x \<in> mu_vars_term \<mu> l" by blast
  then show ?case unfolding i3_subst_def by simp
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. t \<cdot> i3_subst l \<sigma>) ts"
  let ?us = "args (i3_bracket (Fun f ts) \<sigma>)"
  have len: "length ?ss = length ?us" by simp
  have args: "\<And>i. i < length ?ss \<Longrightarrow>
    (?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
  proof -
    fix i
    assume iss: "i < length ?ss"
    then have i: "i < length ts" by simp
    show "(?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have child_sub: "mu_vars_term \<mu> (ts ! i) \<subseteq>
          mu_vars_term \<mu> l"
      proof
        fix x
        assume x: "x \<in> mu_vars_term \<mu> (ts ! i)"
        have "x \<in> mu_vars_term \<mu> (Fun f ts)"
          by (rule mu_vars_term_active_argI[OF i True x])
        with Fun.prems show "x \<in> mu_vars_term \<mu> l" by blast
      qed
      from Fun.hyps[OF nth_mem[OF i] child_sub]
      show ?thesis using i True
        by (simp add: i3_bracket_Fun_nth)
    next
      case False
      have point: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
        (i3_subst l \<sigma> x,\<sigma> x) \<in> (rstep (ce_trs cn))\<^sup>*"
      proof -
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        show "(i3_subst l \<sigma> x,\<sigma> x) \<in>
          (rstep (ce_trs cn))\<^sup>*"
        proof (cases "x \<in> vars_term l")
          case True
          show ?thesis by (rule i3_lhs_subst_projects_value[OF True])
        next
          case False
          then have "x \<notin> mu_vars_term \<mu> l"
            by (meson mu_vars_term_imp_vars_term)
          then show ?thesis unfolding i3_subst_def by simp
        qed
      qed
      have step: "((ts ! i) \<cdot> i3_subst l \<sigma>,
          (ts ! i) \<cdot> \<sigma>) \<in> (rstep (ce_trs cn))\<^sup>*"
        by (rule term_subst_rsteps[OF point])
      show ?thesis using i False step
        by (simp add: i3_bracket_Fun_nth)
    qed
  qed
  have "(Fun f ?ss,Fun f ?us) \<in> (rstep (ce_trs cn))\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length ?ss = length ?us" by (rule len)
    show "\<forall>i<length ?ss.
        (?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
      using args by simp
  qed
  then show ?case by simp
qed

lemma i3_SN_eq_i2:
  assumes "SN_on (csstep \<mu> (set Rs)) {t}"
  shows "i3 t = old.i2 t"
  using assms by (cases t) simp_all

lemma i3_bracket_SN_eq_i2_bracket:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {t \<cdot> \<sigma>}"
  shows "i3_bracket t \<sigma> = old.i2_bracket t \<sigma>"
  using SN
proof (induct t)
  case (Var x)
  then show ?case by (simp add: i3_SN_eq_i2)
next
  case (Fun f ts)
  have lists: "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) =
      map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then old.i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts)"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts)) =
      length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then old.i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts))" by simp
    fix i
    assume ia: "i < length (map (\<lambda>(i,t).
      if i \<in> \<mu> (f,length ts) then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"
    then have i: "i < length ts" by simp
    show "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
        then i3_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) ! i =
      map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
        then old.i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) ! i"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case False
      then show ?thesis using i
        by (simp add: nth_zip)
    next
      case True
      have empty: "[] \<in> mu_poss \<mu> ((ts ! i) \<cdot> \<sigma>)"
        by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
      have pos: "i # [] \<in> mu_poss \<mu> (Fun f ts \<cdot> \<sigma>)"
        using i True empty by auto
      from SN_on_mu_pos[OF wf pos Fun.prems]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
        using i by simp
      have IH: "i3_bracket (ts ! i) \<sigma> =
        old.i2_bracket (ts ! i) \<sigma>"
        by (rule Fun.hyps[OF nth_mem[OF i] sub_SN])
      show ?thesis using i True IH
        by (simp add: nth_zip)
    qed
  qed
  show ?case using lists by simp
qed

lemma i3_projects_to_bracket:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {t \<cdot> \<sigma>}"
  shows "(i3 (t \<cdot> \<sigma>),i3_bracket t \<sigma>)
    \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
  using old.i2_projects_to_bracket[OF SN]
    i3_SN_eq_i2[OF SN] i3_bracket_SN_eq_i2_bracket[OF SN]
  by simp

lemma i3_noncollapsing_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pair_order: "(l,r) \<in> Rgt \<union> Rge"
    and lhs_partition: "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and active_sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
    and rhs_roots: "\<And>p. p \<in> mu_fun_poss \<mu> r \<Longrightarrow>
      root (r |_ p) \<in> Some ` \<Delta>"
    and source_SN: "SN_on (csstep \<mu> (set Rs)) {l \<cdot> \<sigma>}"
  shows "(i3 (l \<cdot> \<sigma>),i3 (r \<cdot> \<sigma>)) \<in> Rgt \<union> Rge \<and>
    ((i3 (l \<cdot> \<sigma>),i3 (r \<cdot> \<sigma>)) \<notin> Rgt \<longrightarrow>
      (l,r) \<notin> Rgt)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?\<tau> = "i3_subst l \<sigma>"
  have source0: "(i3 (l \<cdot> \<sigma>),i3_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule i3_projects_to_bracket[OF source_SN])
  have source_bracket: "i3_bracket l \<sigma> = l \<cdot> ?\<tau>"
    by (rule i3_bracket_as_subst[OF lhs_partition])
  have target0: "(r \<cdot> ?\<tau>,i3_bracket r \<sigma>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    by (rule i3_lhs_subst_to_bracket_rsteps[OF active_sub])
  have target_I: "i3 (r \<cdot> \<sigma>) = i3_bracket r \<sigma>"
    by (rule i3_equals_bracket[OF rhs_roots])
  have source_steps: "(i3 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have sub: "csstep \<mu> (ce_trs cn) \<subseteq>
        rstep (U \<union> ce_trs cn)"
      by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
    show ?thesis using source0 unfolding source_bracket
      by (rule rtrancl_mono[OF sub, THEN subsetD])
  qed
  have target_steps: "(r \<cdot> ?\<tau>,i3 (r \<cdot> \<sigma>))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have sub: "rstep (ce_trs cn) \<subseteq> rstep (U \<union> ce_trs cn)"
      by (rule rstep_mono, simp)
    show ?thesis unfolding target_I
      by (rule rtrancl_mono[OF sub, THEN subsetD, OF target0])
  qed
  have source_weak: "(i3 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge"
    using rtrancl_mono[OF rewrite_weak, THEN subsetD, OF source_steps]
      rp.refl_NS rp.trans_NS by (simp add: trans_refl_imp_rtrancl_id)
  have target_weak: "(r \<cdot> ?\<tau>,i3 (r \<cdot> \<sigma>)) \<in> Rge"
    using rtrancl_mono[OF rewrite_weak, THEN subsetD, OF target_steps]
      rp.refl_NS rp.trans_NS by (simp add: trans_refl_imp_rtrancl_id)
  show ?thesis
  proof (cases "(l,r) \<in> Rgt")
    case True
    have middle: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    from rp.compat_NS_S[THEN subsetD, OF relcompI[OF source_weak middle]]
    have first: "(i3 (l \<cdot> \<sigma>),r \<cdot> ?\<tau>) \<in> Rgt" .
    from rp.compat_S_NS[THEN subsetD, OF relcompI[OF first target_weak]]
    show ?thesis using first target_weak
      rp.compat_S_NS by auto
  next
    case False
    with pair_order have weak: "(l,r) \<in> Rge" by auto
    have middle: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak])
    from rp.trans_NS_point[OF source_weak middle]
    have first: "(i3 (l \<cdot> \<sigma>),r \<cdot> ?\<tau>) \<in> Rge" .
    from rp.trans_NS_point[OF first target_weak]
    show ?thesis using pair_order False by auto
  qed
qed

lemma i3_collapsing_bridge_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pair_order: "(l,Var y) \<in> Rgt \<union> Rge"
    and bridge_order: "(a,b) \<in> Rge"
    and lhs_partition: "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and rhs_active: "y \<in> mu_vars_term \<mu> l"
    and bridge_partition: "mu_vars_term \<mu> a \<inter> non_mu_vars_term \<mu> a = {}"
    and bridge_active: "mu_vars_term \<mu> b \<subseteq> mu_vars_term \<mu> a"
    and source_SN: "SN_on (csstep \<mu> (set Rs)) {l \<cdot> \<sigma>}"
    and x: "\<sigma> y = a \<cdot> \<theta>"
    and b_roots: "\<And>p. p \<in> mu_fun_poss \<mu> b \<Longrightarrow>
      root (b |_ p) \<in> Some ` \<Delta>"
  shows "(i3 (l \<cdot> \<sigma>),i3 (b \<cdot> \<theta>)) \<in> Rgt \<union> Rge \<and>
    ((i3 (l \<cdot> \<sigma>),i3 (b \<cdot> \<theta>)) \<notin> Rgt \<longrightarrow>
      (l,Var y) \<notin> Rgt)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?\<sigma>' = "i3_subst l \<sigma>"
  let ?\<theta>' = "i3_subst a \<theta>"
  have source0: "(i3 (l \<cdot> \<sigma>),i3_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule i3_projects_to_bracket[OF source_SN])
  have source_bracket: "i3_bracket l \<sigma> = l \<cdot> ?\<sigma>'"
    by (rule i3_bracket_as_subst[OF lhs_partition])
  have source_steps: "(i3 (l \<cdot> \<sigma>),l \<cdot> ?\<sigma>')
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have sub: "csstep \<mu> (ce_trs cn) \<subseteq>
        rstep (U \<union> ce_trs cn)"
      by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
    show ?thesis using source0 unfolding source_bracket
      by (rule rtrancl_mono[OF sub, THEN subsetD])
  qed
  have source_weak: "(i3 (l \<cdot> \<sigma>),l \<cdot> ?\<sigma>') \<in> Rge"
    using rtrancl_mono[OF rewrite_weak, THEN subsetD, OF source_steps]
      rp.refl_NS rp.trans_NS by (simp add: trans_refl_imp_rtrancl_id)
  have sigma_y: "?\<sigma>' y = i3 (\<sigma> y)"
    unfolding i3_subst_def using rhs_active by simp
  from rhs_active obtain q where q_mu: "q \<in> mu_poss \<mu> l"
    and lq: "l |_ q = Var y"
    unfolding mu_vars_term_def by blast
  have q_sub: "q \<in> mu_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_poss_subst_lift[OF q_mu])
  have q_pos: "q \<in> poss l" using q_mu mu_poss_imp_poss by blast
  have at_sub: "(l \<cdot> \<sigma>) |_ q = \<sigma> y"
    using subt_at_subst[OF q_pos, of \<sigma>] lq by simp
  have sigma_y_SN: "SN_on (csstep \<mu> (set Rs)) {\<sigma> y}"
    using SN_on_mu_pos[OF wf q_sub source_SN] unfolding at_sub .
  have bridge_source0': "(i3 (a \<cdot> \<theta>),i3_bracket a \<theta>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule i3_projects_to_bracket[where t=a and \<sigma>=\<theta>],
      use sigma_y_SN x in simp)
  have bridge_source0: "(i3 (\<sigma> y),i3_bracket a \<theta>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    using bridge_source0' x by simp
  have bridge_bracket: "i3_bracket a \<theta> = a \<cdot> ?\<theta>'"
    by (rule i3_bracket_as_subst[OF bridge_partition])
  have bridge_source_steps: "(i3 (\<sigma> y),a \<cdot> ?\<theta>')
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have sub: "csstep \<mu> (ce_trs cn) \<subseteq>
        rstep (U \<union> ce_trs cn)"
      by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
    show ?thesis unfolding bridge_bracket[symmetric]
      by (rule rtrancl_mono[OF sub, THEN subsetD, OF bridge_source0])
  qed
  have bridge_source_weak: "(i3 (\<sigma> y),a \<cdot> ?\<theta>') \<in> Rge"
    using rtrancl_mono[OF rewrite_weak, THEN subsetD, OF bridge_source_steps]
      rp.refl_NS rp.trans_NS by (simp add: trans_refl_imp_rtrancl_id)
  have bridge_middle: "(a \<cdot> ?\<theta>',b \<cdot> ?\<theta>') \<in> Rge"
    by (rule subst.closedD[OF rp.subst_NS bridge_order])
  have bridge_weak: "(i3 (\<sigma> y),b \<cdot> ?\<theta>') \<in> Rge"
    by (rule rp.trans_NS_point[OF bridge_source_weak bridge_middle])
  have bridge_weak': "(?\<sigma>' y,b \<cdot> ?\<theta>') \<in> Rge"
    using bridge_weak sigma_y by simp
  have target0: "(b \<cdot> ?\<theta>',i3_bracket b \<theta>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    by (rule i3_lhs_subst_to_bracket_rsteps[OF bridge_active])
  have target_I: "i3 (b \<cdot> \<theta>) = i3_bracket b \<theta>"
    by (rule i3_equals_bracket[OF b_roots])
  have target_steps: "(b \<cdot> ?\<theta>',i3 (b \<cdot> \<theta>))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have sub: "rstep (ce_trs cn) \<subseteq> rstep (U \<union> ce_trs cn)"
      by (rule rstep_mono, simp)
    show ?thesis unfolding target_I
      by (rule rtrancl_mono[OF sub, THEN subsetD, OF target0])
  qed
  have target_weak: "(b \<cdot> ?\<theta>',i3 (b \<cdot> \<theta>)) \<in> Rge"
    using rtrancl_mono[OF rewrite_weak, THEN subsetD, OF target_steps]
      rp.refl_NS rp.trans_NS by (simp add: trans_refl_imp_rtrancl_id)
  show ?thesis
  proof (cases "(l,Var y) \<in> Rgt")
    case True
    have middle: "(l \<cdot> ?\<sigma>',?\<sigma>' y) \<in> Rgt"
      using subst.closedD[OF rp.subst_S True, of ?\<sigma>'] by simp
    from rp.compat_NS_S[THEN subsetD, OF relcompI[OF source_weak middle]]
    have first: "(i3 (l \<cdot> \<sigma>),?\<sigma>' y) \<in> Rgt" .
    from rp.compat_S_NS[THEN subsetD, OF relcompI[OF first bridge_weak']]
    have second: "(i3 (l \<cdot> \<sigma>),b \<cdot> ?\<theta>') \<in> Rgt" .
    from rp.compat_S_NS[THEN subsetD, OF relcompI[OF second target_weak]]
    show ?thesis using second target_weak rp.compat_S_NS by auto
  next
    case False
    with pair_order have weak: "(l,Var y) \<in> Rge" by auto
    have middle: "(l \<cdot> ?\<sigma>',?\<sigma>' y) \<in> Rge"
      using subst.closedD[OF rp.subst_NS weak, of ?\<sigma>'] by simp
    from rp.trans_NS_point[OF source_weak middle]
    have first: "(i3 (l \<cdot> \<sigma>),?\<sigma>' y) \<in> Rge" .
    from rp.trans_NS_point[OF first bridge_weak']
    have second: "(i3 (l \<cdot> \<sigma>),b \<cdot> ?\<theta>') \<in> Rge" .
    from rp.trans_NS_point[OF second target_weak]
    show ?thesis using pair_order False by auto
  qed
qed

lemma SN_sharp_csdp_imp_SN_csstep_i3:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
  shows "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
  have undef: "\<not> defined (set Rs) (shp f,length ss)" by (rule fresh)
  from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
  obtain j where j: "j < length ss"
    and active: "j \<in> \<mu> (shp f,length ss)"
    and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {ss ! j}" by blast
  have active_orig: "j \<in> \<mu> (f,length ss)" using active marked_mu by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig SN]
    notSN_j show False by contradiction
qed

lemma i3_typed_pair_redpair_order:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and pair_lhs_marked_mu: "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow>
      l = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>P. \<exists>f ls. l = Fun (shp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>P. is_Var r \<or>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs"
    and lhs_partition: "\<And>l r. (l,r) \<in> P \<union> B \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and active_sub: "\<And>l r. (l,r) \<in> P \<union> B \<Longrightarrow> is_Fun r \<Longrightarrow>
      mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
    and collapsing_active: "\<And>l y. (l,Var y) \<in> P \<Longrightarrow>
      y \<in> mu_vars_term \<mu> l"
    and rhs_roots: "\<And>l r p. (l,r) \<in> P \<union> B \<Longrightarrow>
      p \<in> mu_fun_poss \<mu> r \<Longrightarrow> root (r |_ p) \<in> Some ` \<Delta>"
    and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    and pair_step: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "(i3 s,i3 t) \<in> Rgt \<union> Rge \<and>
    ((i3 s,i3 t) \<notin> Rgt \<longrightarrow>
      (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
proof -
  from pair_step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and rfun: "\<not> is_Var r" and s: "s = l \<cdot> \<sigma>"
      and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from pair_lhs_shape pair obtain f ls where l: "l = Fun (shp f) ls" by auto
    have marked_f: "\<mu> (shp f,length ls) = \<mu> (f,length ls)"
      by (rule pair_lhs_marked_mu[OF pair l])
    from pair_rhs_shape pair rfun obtain g rs where r: "r = Fun (shp g) rs"
      by (cases r, auto)
    have r_fun: "is_Fun r" unfolding r by simp
    have source_form: "l \<cdot> \<sigma> =
        Fun (shp f) (map (\<lambda>u. u \<cdot> \<sigma>) ls)"
      unfolding l by simp
    have source_cs: "SN_on (csstep \<mu> (set Rs)) {l \<cdot> \<sigma>}"
      unfolding source_form
      by (rule SN_sharp_csdp_imp_SN_csstep_i3[
        OF fresh _ source_SN[unfolded s source_form]], use marked_f in simp)
    from i3_noncollapsing_redpair_order[
      OF redpair rewrite_weak pairs_order[THEN subsetD, OF pair]
        lhs_partition[OF UnI1[OF pair]] active_sub[OF UnI1[OF pair] r_fun]
        rhs_roots[OF UnI1[OF pair]] source_cs]
    have ordered: "(i3 s,i3 t) \<in> Rgt \<union> Rge"
      and residual: "(i3 s,i3 t) \<notin> Rgt \<Longrightarrow> (l,r) \<notin> Rgt"
      unfolding s t by auto
    have residual_step: "(i3 s,i3 t) \<notin> Rgt \<Longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
        rrstep_def' using pair rfun s t residual by blast
    show ?thesis using ordered residual_step by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> a b \<theta> where pair: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and x: "\<sigma> y = a \<cdot> \<theta>"
      and bridge: "(a,b) \<in> B" and t: "t = b \<cdot> \<theta>"
      unfolding muterm_collapsing_rrstep_def rrstep_def' by auto
    from pair_lhs_shape pair obtain f ls where l: "l = Fun (shp f) ls" by auto
    have marked_f: "\<mu> (shp f,length ls) = \<mu> (f,length ls)"
      by (rule pair_lhs_marked_mu[OF pair l])
    have source_form: "l \<cdot> \<sigma> =
        Fun (shp f) (map (\<lambda>u. u \<cdot> \<sigma>) ls)"
      unfolding l by simp
    have source_cs: "SN_on (csstep \<mu> (set Rs)) {l \<cdot> \<sigma>}"
      unfolding source_form
      by (rule SN_sharp_csdp_imp_SN_csstep_i3[
        OF fresh _ source_SN[unfolded s source_form]], use marked_f in simp)
    from bridge_rhs_shape bridge have b_fun: "is_Fun b" by auto
    from i3_collapsing_bridge_redpair_order[
      OF redpair rewrite_weak pairs_order[THEN subsetD, OF pair]
        bridges_order[THEN subsetD, OF bridge]
        lhs_partition[OF UnI1[OF pair]] collapsing_active[OF pair]
        lhs_partition[OF UnI2[OF bridge]]
        active_sub[OF UnI2[OF bridge] b_fun]
        source_cs x rhs_roots[OF UnI2[OF bridge]]]
    have ordered: "(i3 s,i3 t) \<in> Rgt \<union> Rge"
      and residual: "(i3 s,i3 t) \<notin> Rgt \<Longrightarrow>
        (l,Var y) \<notin> Rgt"
      unfolding s t by auto
    have residual_step: "(i3 s,i3 t) \<notin> Rgt \<Longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      unfolding muterm_typed_pair_step_def muterm_collapsing_rrstep_def
        rrstep_def' using pair s x bridge t residual by blast
    show ?thesis using ordered residual_step by blast
  qed
qed

lemma sharp_csdp_steps_shape_i3:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and source: "s = Fun (shp f) ss"
    and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
  shows "\<exists>us. t = Fun (shp f) us \<and> length us = length ss"
  using steps source
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  from step.hyps(3)[OF step.prems] obtain us where
    y: "y = Fun (shp f) us" and len: "length us = length ss" by blast
  have sharp_step: "(sharp_term shp (Fun f us),z)
      \<in> csdp_step shp \<mu> (set Rs)"
    using step.hyps(2) unfolding y by simp
  from sharp_csdp_step_imp_csnrstep[OF wf fresh marked_inj sharp_step]
  obtain u where z: "z = sharp_term shp u"
    and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
  from nonroot obtain vs where u: "u = Fun f vs"
    and len': "length vs = length us" by (elim csnrstep_FunE, blast)
  show ?case using z u len len' by auto
qed

theorem finite_muterm_min_typed_dpp_i3_redpair:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed_rhs: "\<And>l r. (l,r) \<in>
      {lr \<in> P. is_Fun (snd lr)} \<union> B \<union> U \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu>
      ({lr \<in> P. is_Fun (snd lr)} \<union> B \<union> U)"
    and lhs_partition: "\<And>l r. (l,r) \<in> P \<union> B \<union> U \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and collapsing_active: "\<And>l y. (l,Var y) \<in> P \<Longrightarrow>
      y \<in> mu_vars_term \<mu> l"
    and U_R: "U \<subseteq> set Rs"
    and fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and pair_lhs_marked_mu: "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow>
      l = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and pair_rhs_marked_mu: "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow>
      r = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and bridge_rhs_marked_mu: "\<And>a b f ss. (a,b) \<in> B \<Longrightarrow>
      b = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>P. \<exists>f ls. l = Fun (shp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>P. is_Var r \<or>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and bridge_lhs_shape: "\<forall>(a,b)\<in>B. is_Fun a"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> (set Rs) (P - Rgt) B"
  shows "finite_muterm_min_typed_dpp shp \<mu> (set Rs) P B"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?T = "{lr \<in> P. is_Fun (snd lr)} \<union> B \<union> U"
  have lhs_T: "\<And>l r. (l,r) \<in> ?T \<Longrightarrow> is_Fun l"
  proof -
    fix l r
    assume lr: "(l,r) \<in> ?T"
    show "is_Fun l"
    proof (cases "(l,r) \<in> P")
      case True
      from pair_lhs_shape True show ?thesis by auto
    next
      case False
      have lr_BU: "(l,r) \<in> B \<union> U" using lr False by blast
      show ?thesis
      proof (cases "(l,r) \<in> B")
        case True
        from bridge_lhs_shape True show ?thesis by auto
      next
        case False
        with lr_BU have "(l,r) \<in> U" by blast
        with U_R have "(l,r) \<in> set Rs" by blast
        with wf show ?thesis unfolding wf_trs_def by (cases l, auto)
      qed
    qed
  qed
  interpret L: muterm_i2_extended_basic Rs \<mu> \<Delta> cn U ?T
  proof
    show "\<Delta> = csr_u3_delta (set Rs) U" by (rule delta)
  next
    fix l r
    assume lr: "(l,r) \<in> ?T"
    then show "csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
      using closed_rhs[of l r] lr by blast
  next
    show "rhs_mu_vars_condition \<mu> ?T" by (rule conservative)
  next
    fix l r
    assume lr: "(l,r) \<in> ?T"
    then show "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
      using lhs_partition[of l r] lr by blast
  next
    show "U \<subseteq> ?T" by simp
  next
    fix l r
    assume "(l,r) \<in> ?T"
    then show "is_Fun l" by (rule lhs_T)
  qed
  have roots_all: "\<And>l r p. (l,r) \<in> P \<union> B \<Longrightarrow>
      p \<in> mu_fun_poss \<mu> r \<Longrightarrow> root (r |_ p) \<in> Some ` \<Delta>"
  proof -
    fix l r p
    assume lr: "(l,r) \<in> P \<union> B" and p: "p \<in> mu_fun_poss \<mu> r"
    from mu_fun_poss_imp_fun_poss[OF p] obtain h us where
      at: "r |_ p = Fun h us" using fun_poss_fun_conv by blast
    have root: "root (r |_ p) = Some (h,length us)" unfolding at by simp
    have r_fun: "is_Fun r" using p by (cases r, auto)
    have lrT: "(l,r) \<in> ?T" using lr r_fun by auto
    have "(h,length us) \<in> csr_u3_delta (set Rs) U"
      by (rule csr_u3_root_rules_closed_delta[
        OF closed_rhs[OF lrT] p root])
    then show "root (r |_ p) \<in> Some ` \<Delta>" unfolding delta root by blast
  qed
  have typed_order: "(i3 s,i3 t) \<in> Rgt \<union> Rge \<and>
      ((i3 s,i3 t) \<notin> Rgt \<longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
    if source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      and typed: "(s,t) \<in> muterm_typed_pair_step P B" for s t
  proof (rule i3_typed_pair_redpair_order)
    show "\<And>g n. \<not> defined (set Rs) (shp g,n)" by (rule fresh)
    show "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow> l = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
      by (rule pair_lhs_marked_mu)
    show "compat_redpair_order Rgt Rge" by (rule redpair)
    show "rstep (U \<union> ce_trs cn) \<subseteq> Rge" by (rule rewrite_weak)
    show "P \<subseteq> Rgt \<union> Rge" by (rule pairs_order)
    show "B \<subseteq> Rge" by (rule bridges_order)
    show "\<forall>(l,r)\<in>P. \<exists>f ls. l = Fun (shp f) ls" by (rule pair_lhs_shape)
    show "\<forall>(l,r)\<in>P. is_Var r \<or> (\<exists>g rs. r = Fun (shp g) rs)"
      by (rule pair_rhs_shape)
    show "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs" by (rule bridge_rhs_shape)
    fix l r
    assume lr: "(l,r) \<in> P \<union> B"
    show "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
      by (rule lhs_partition, use lr in auto)
  next
    fix l r
    assume lr: "(l,r) \<in> P \<union> B" and r_fun: "is_Fun r"
    have lrT: "(l,r) \<in> ?T" using lr r_fun by auto
    then show "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
      by (rule L.eb_active_variables)
  next
    show "\<And>l y. (l,Var y) \<in> P \<Longrightarrow> y \<in> mu_vars_term \<mu> l"
      by (rule collapsing_active)
    show "\<And>l r p. (l,r) \<in> P \<union> B \<Longrightarrow>
      p \<in> mu_fun_poss \<mu> r \<Longrightarrow> root (r |_ p) \<in> Some ` \<Delta>"
      by (rule roots_all)
    show "SN_on (csdp_step shp \<mu> (set Rs)) {s}" by (rule source_SN)
    show "SN_on (csdp_step shp \<mu> (set Rs)) {t}" by (rule target_SN)
    show "(s,t) \<in> muterm_typed_pair_step P B" by (rule typed)
  qed
  show ?thesis unfolding finite_muterm_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair_targeted[
      OF redpair, where G="\<lambda>t. \<exists>f ts. t = Fun (shp f) ts \<and>
        \<mu> (shp f,length ts) = \<mu> (f,length ts)"])
    fix s t
    assume pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) P B"
    then show "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      unfolding muterm_min_typed_pair_step_def by auto
  next
    fix s t
    assume pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) P B"
    then have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_min_typed_pair_step_def by auto
    show "\<exists>f ts. t = Fun (shp f) ts \<and>
        \<mu> (shp f,length ts) = \<mu> (f,length ts)"
    proof -
      from typed have cases:
          "muterm_noncollapsing_rrstep P s t \<or>
           (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
        unfolding muterm_typed_pair_step_def by auto
      from cases show ?thesis
      proof
        assume "muterm_noncollapsing_rrstep P s t"
        then obtain l r \<sigma> where lr: "(l,r) \<in> P" and "\<not> is_Var r"
          and "t = r \<cdot> \<sigma>"
          unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
        with pair_rhs_shape obtain g rs where r: "r = Fun (shp g) rs" by (cases r, auto)
        have marked: "\<mu> (shp g,length rs) = \<mu> (g,length rs)"
          by (rule pair_rhs_marked_mu[OF lr r])
        show ?thesis using r marked `t = r \<cdot> \<sigma>` by auto
      next
        assume "\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B"
        then obtain x a b \<sigma> where ab: "(a,b) \<in> B" and t: "t = b \<cdot> \<sigma>"
          unfolding rrstep_def' by auto
        from bridge_rhs_shape ab obtain g rs where b: "b = Fun (shp g) rs"
          by auto
        have marked: "\<mu> (shp g,length rs) = \<mu> (g,length rs)"
          by (rule bridge_rhs_marked_mu[OF ab b])
        show ?thesis unfolding t b using marked by auto
      qed
    qed
  next
    fix s t
    assume source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) P B"
    from pair have target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      and typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_min_typed_pair_step_def by auto
    show "(i3 s,i3 t) \<in> Rgt \<union> Rge"
      using typed_order[OF source_SN target_SN typed] by blast
  next
    fix s t
    assume source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) P B"
      and not_strict: "(i3 s,i3 t) \<notin> Rgt"
    from pair have target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      and typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_min_typed_pair_step_def by auto
    from typed_order[OF source_SN target_SN typed] not_strict
    have residual: "(s,t) \<in> muterm_typed_pair_step (P - Rgt) B" by blast
    show "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) (P - Rgt) B"
      unfolding muterm_min_typed_pair_step_def using residual target_SN by auto
  next
    fix s t
    assume marked: "\<exists>f ts. s = Fun (shp f) ts \<and>
        \<mu> (shp f,length ts) = \<mu> (f,length ts)"
      and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
    from marked obtain f ss where s: "s = Fun (shp f) ss"
      and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)" by blast
    have old_steps: "(old.i2 s,old.i2 t) \<in>
        (rstep (U \<union> ce_trs cn))\<^sup>*"
      by (rule L.i2_sharp_csdp_steps_extended_basic[
        OF fresh marked_inj marked_mu s source_SN steps])
    have source_cs: "SN_on (csstep \<mu> (set Rs)) {s}"
      unfolding s by (rule SN_sharp_csdp_imp_SN_csstep_i3[
        OF fresh marked_mu source_SN[unfolded s]])
    have target_dp: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    proof (rule ccontr)
      assume "\<not> SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      from steps_notSN_on_source[OF steps this] source_SN show False by contradiction
    qed
    from sharp_csdp_steps_shape_i3[OF fresh marked_inj s steps]
    obtain us where t: "t = Fun (shp f) us" and len: "length us = length ss"
      by blast
    have target_cs: "SN_on (csstep \<mu> (set Rs)) {t}"
      unfolding t by (rule SN_sharp_csdp_imp_SN_csstep_i3[
        OF fresh _ target_dp[unfolded t]], use marked_mu len in simp)
    have weak_star: "(old.i2 s,old.i2 t) \<in> Rge\<^sup>*"
      by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF old_steps])
    have weak: "(old.i2 s,old.i2 t) \<in> Rge"
      using weak_star rp.refl_NS rp.trans_NS
      by (simp add: trans_refl_imp_rtrancl_id)
    show "(i3 s,i3 t) \<in> Rge"
      using i3_SN_eq_i2[OF source_cs] i3_SN_eq_i2[OF target_cs] weak by simp
  next
    show "SN_rel
      (muterm_min_typed_pair_step shp \<mu> (set Rs) (P - Rgt) B)
      (csdp_step shp \<mu> (set Rs))"
      using fin unfolding finite_muterm_min_typed_dpp_def .
  qed
qed

end

theorem finite_muterm_min_typed_dpp_general_usable_redpair:
  fixes Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and shp :: "'f \<Rightarrow> 'f"
  assumes wf: "wf_trs (set Rs)"
    and closed_rhs: "\<And>l r. (l,r) \<in>
      {lr \<in> P. is_Fun (snd lr)} \<union> B \<union> U \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu>
      ({lr \<in> P. is_Fun (snd lr)} \<union> B \<union> U)"
    and lhs_partition: "\<And>l r. (l,r) \<in> P \<union> B \<union> U \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and collapsing_active: "\<And>l y. (l,Var y) \<in> P \<Longrightarrow>
      y \<in> mu_vars_term \<mu> l"
    and U_R: "U \<subseteq> set Rs"
    and fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and pair_lhs_marked_mu: "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow>
      l = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and pair_rhs_marked_mu: "\<And>l r f ss. (l,r) \<in> P \<Longrightarrow>
      r = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and bridge_rhs_marked_mu: "\<And>a b f ss. (a,b) \<in> B \<Longrightarrow>
      b = Fun (shp f) ss \<Longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>P. \<exists>f ls. l = Fun (shp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>P. is_Var r \<or>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and bridge_lhs_shape: "\<forall>(a,b)\<in>B. is_Fun a"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs"
    and U_weak: "U \<subseteq> Rge"
    and ce: "ce_compatible Rge"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> (set Rs) (P - Rgt) B"
  shows "finite_muterm_min_typed_dpp shp \<mu> (set Rs) P B"
proof (cases "P = {}")
  case True
  with fin show ?thesis by simp
next
  case False
  then obtain dp where dp: "dp \<in> P" by blast
  obtain l r where pair: "(l,r) \<in> P" by (cases dp, use dp in blast)
  from pair_lhs_shape pair obtain f ss where l: "l = Fun (shp f) ss" by auto
  obtain n where ce_bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(shp f,n)"
  have ce_weak: "ce_trs ?cn \<subseteq> Rge" by (rule ce_bound, simp)
  have rules_weak: "U \<union> ce_trs ?cn \<subseteq> Rge" using U_weak ce_weak by auto
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have rewrite_weak: "rstep (U \<union> ce_trs ?cn) \<subseteq> Rge"
    by (rule subset_trans[OF rstep_mono[OF rules_weak] rp.rstep_NS])
  interpret I: muterm_i3 Rs \<mu> "csr_u3_delta (set Rs) U" ?cn
    by (unfold_locales, rule wf)
  show ?thesis
    by (rule I.finite_muterm_min_typed_dpp_i3_redpair[
      OF refl closed_rhs conservative lhs_partition
        collapsing_active U_R fresh marked_inj pair_lhs_marked_mu
        pair_rhs_marked_mu bridge_rhs_marked_mu redpair rewrite_weak
        pairs_order bridges_order pair_lhs_shape pair_rhs_shape bridge_lhs_shape
        bridge_rhs_shape fin])
qed

context csr_rta08_i1
begin

lemma i1_sharp_csdp_steps:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<And>n. \<mu> (shp f,n) = \<mu> (f,n)"
    and source: "s = Fun (shp f) ss"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
  shows "(weak.i1 s,weak.i1 t) \<in>
    (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  have combined: "(weak.i1 s,weak.i1 t) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<and>
      SN_on (csdp_step shp \<mu> (set Rs)) {t} \<and>
      (\<exists>us. t = Fun (shp f) us \<and> length us = length ss)"
    using steps SN source
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case by auto
  next
    case (step y z)
    from step.hyps(3)[OF step.prems(1) step.prems(2)]
    have prefix: "(weak.i1 s,weak.i1 y) \<in>
        (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      and y_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {y}"
      and y_shape: "\<exists>us. y = Fun (shp f) us \<and> length us = length ss"
      by blast+
    from y_shape obtain us where y: "y = Fun (shp f) us"
      and us_len: "length us = length ss" by blast
    have one: "(weak.i1 y,weak.i1 z) \<in>
        (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      unfolding y
      apply (rule weak.i1_sharp_csdp_step[
        where shp=shp and f=f and ss=us and t=z])
          apply (rule fresh)
         apply (rule marked_inj)
        using marked_mu[of "length us"] apply simp
       using y_SN y apply simp
      using step.hyps(2) y apply simp
      done
    have z_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {z}"
      by (rule step_SN_on_target[OF y_SN step.hyps(2)])
    have z_shape: "\<exists>vs. z = Fun (shp f) vs \<and> length vs = length ss"
    proof -
      have sharp_step: "(sharp_term shp (Fun f us),z)
          \<in> csdp_step shp \<mu> (set Rs)"
        using step.hyps(2) unfolding y by simp
      from sharp_csdp_step_imp_csnrstep[OF wf fresh marked_inj sharp_step]
      obtain u where z: "z = sharp_term shp u"
        and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
      from nonroot obtain vs where u: "u = Fun f vs"
        and len: "length vs = length us" by (elim csnrstep_FunE, blast)
      with z us_len show ?thesis by auto
    qed
    show ?case
      by (intro conjI rtrancl_trans[OF prefix one] z_SN z_shape)
  qed
  then show ?thesis by blast
qed

lemma i1_typed_pair_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "Q \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_inactive: "\<And>l r p. (l,r) \<in> Q \<Longrightarrow>
      p \<in> fun_poss l \<Longrightarrow> p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and pair_rhs_delta: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_lhs_inactive: "\<And>a b p. (a,b) \<in> B \<Longrightarrow>
      p \<in> fun_poss a \<Longrightarrow> p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_rhs_delta: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
    and pair_step: "(s,t) \<in> muterm_typed_pair_step Q B"
  shows "(weak.i1 s,weak.i1 t) \<in> Rgt \<union> Rge \<and>
    ((weak.i1 s,weak.i1 t) \<notin> Rgt \<longrightarrow>
      (s,t) \<in> muterm_typed_pair_step (Q - Rgt) B)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have closure: "(csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<subseteq> Rge"
  proof
    fix st
    assume "st \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    then have "st \<in> Rge\<^sup>*" by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD])
    then show "st \<in> Rge" using rp.refl_NS rp.trans_NS
      by (simp add: trans_refl_imp_rtrancl_id)
  qed
  have ce_closure: "(csstep \<mu> (ce_trs cn))\<^sup>* \<subseteq> Rge"
  proof (rule subset_trans[OF rtrancl_mono closure])
    show "csstep \<mu> (ce_trs cn) \<subseteq> csstep \<mu> (U \<union> ce_trs cn)"
      by (rule csstep_rules_mono, simp)
  qed
  from pair_step have cases:
      "muterm_noncollapsing_rrstep Q s t \<or>
       (\<exists>x. muterm_collapsing_rrstep Q s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep Q s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> Q"
      and rfun: "is_Fun r" and s: "s = l \<cdot> \<sigma>"
      and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from weak.i1_pattern_subst[OF pair_lhs_inactive[OF pair], of \<sigma>]
    have source: "(weak.i1 (l \<cdot> \<sigma>),
        l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x))) \<in> Rge"
      by (rule ce_closure[THEN subsetD])
    have target: "weak.i1 (r \<cdot> \<sigma>) =
        r \<cdot> (\<lambda>x. weak.i1 (\<sigma> x))"
      by (rule weak.i1_delta_subst[OF pair_rhs_delta[OF pair rfun]])
    from pairs_order pair have order: "(l,r) \<in> Rgt \<union> Rge" by auto
    show ?thesis
    proof (cases "(l,r) \<in> Rgt")
      case True
      have middle: "(l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x)),
          r \<cdot> (\<lambda>x. weak.i1 (\<sigma> x))) \<in> Rgt"
        by (rule subst.closedD[OF rp.subst_S True])
      have strict: "(weak.i1 s,weak.i1 t) \<in> Rgt"
        using rp.compat_NS_S source middle unfolding s t target by auto
      show ?thesis using strict by auto
    next
      case False
      with order have weak: "(l,r) \<in> Rge" by auto
      have middle: "(l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x)),
          r \<cdot> (\<lambda>x. weak.i1 (\<sigma> x))) \<in> Rge"
        by (rule subst.closedD[OF rp.subst_NS weak])
      have total: "(weak.i1 s,weak.i1 t) \<in> Rge"
        using rp.trans_NS_point source middle unfolding s t target by auto
      have residual: "muterm_noncollapsing_rrstep (Q - Rgt) s t"
        unfolding muterm_noncollapsing_rrstep_def rrstep_def'
        using pair rfun s t False by blast
      show ?thesis unfolding muterm_typed_pair_step_def using total residual by auto
    qed
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep Q s x \<and> (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> a b \<theta> where pair: "(l,Var y) \<in> Q"
      and s: "s = l \<cdot> \<sigma>" and x: "\<sigma> y = a \<cdot> \<theta>"
      and bridge: "(a,b) \<in> B" and t: "t = b \<cdot> \<theta>"
      unfolding muterm_collapsing_rrstep_def rrstep_def' by auto
    from weak.i1_pattern_subst[OF pair_lhs_inactive[OF pair], of \<sigma>]
    have source: "(weak.i1 (l \<cdot> \<sigma>),
        l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x))) \<in> Rge"
      by (rule ce_closure[THEN subsetD])
    from weak.i1_pattern_subst[OF bridge_lhs_inactive[OF bridge], of \<theta>]
    have hidden: "(weak.i1 (a \<cdot> \<theta>),
        a \<cdot> (\<lambda>x. weak.i1 (\<theta> x))) \<in> Rge"
      by (rule ce_closure[THEN subsetD])
    have bridge_inst: "(a \<cdot> (\<lambda>x. weak.i1 (\<theta> x)),
        b \<cdot> (\<lambda>x. weak.i1 (\<theta> x))) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS bridges_order[THEN subsetD, OF bridge]])
    have target: "weak.i1 (b \<cdot> \<theta>) =
        b \<cdot> (\<lambda>x. weak.i1 (\<theta> x))"
      by (rule weak.i1_delta_subst[OF bridge_rhs_delta[OF bridge]])
    have hidden_to_target: "(weak.i1 (\<sigma> y),weak.i1 (b \<cdot> \<theta>)) \<in> Rge"
      using rp.trans_NS_point hidden bridge_inst unfolding x target by auto
    from pairs_order pair have order: "(l,Var y) \<in> Rgt \<union> Rge" by auto
    show ?thesis
    proof (cases "(l,Var y) \<in> Rgt")
      case True
      have middle: "(l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x)),weak.i1 (\<sigma> y)) \<in> Rgt"
        using subst.closedD[OF rp.subst_S True, of "\<lambda>x. weak.i1 (\<sigma> x)"] by simp
      have first: "(weak.i1 (l \<cdot> \<sigma>),weak.i1 (\<sigma> y)) \<in> Rgt"
        using rp.compat_NS_S source middle by auto
      have strict: "(weak.i1 s,weak.i1 t) \<in> Rgt"
        using rp.compat_S_NS first hidden_to_target unfolding s t by auto
      show ?thesis using strict by auto
    next
      case False
      with order have weak: "(l,Var y) \<in> Rge" by auto
      have middle: "(l \<cdot> (\<lambda>x. weak.i1 (\<sigma> x)),weak.i1 (\<sigma> y)) \<in> Rge"
        using subst.closedD[OF rp.subst_NS weak, of "\<lambda>x. weak.i1 (\<sigma> x)"] by simp
      have first: "(weak.i1 (l \<cdot> \<sigma>),weak.i1 (\<sigma> y)) \<in> Rge"
        by (rule rp.trans_NS_point[OF source middle])
      have total: "(weak.i1 s,weak.i1 t) \<in> Rge"
        using rp.trans_NS_point first hidden_to_target unfolding s t by auto
      have residual: "muterm_collapsing_rrstep (Q - Rgt) s (a \<cdot> \<theta>)"
      proof (unfold muterm_collapsing_rrstep_def, intro exI conjI)
        show "(l,Var y) \<in> Q - Rgt" using pair False by auto
        show "s = l \<cdot> \<sigma>" by (rule s)
        show "a \<cdot> \<theta> = \<sigma> y" using x by simp
      qed
      show ?thesis unfolding muterm_typed_pair_step_def rrstep_def'
        using total residual bridge t by auto
    qed
  qed
qed

theorem finite_muterm_min_typed_dpp_i1_redpair:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and pair_rhs_marked_mu: "\<And>l r g rs n. (l,r) \<in> Q \<Longrightarrow>
      r = Fun (shp g) rs \<Longrightarrow> \<mu> (shp g,n) = \<mu> (g,n)"
    and bridge_rhs_marked_mu: "\<And>a b g rs n. (a,b) \<in> B \<Longrightarrow>
      b = Fun (shp g) rs \<Longrightarrow> \<mu> (shp g,n) = \<mu> (g,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "Q \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>Q. \<exists>f ls. l = Fun (shp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>Q. is_Var r \<or>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs"
    and pair_lhs_inactive: "\<And>l r p. (l,r) \<in> Q \<Longrightarrow>
      p \<in> fun_poss l \<Longrightarrow> p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and pair_rhs_delta: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_lhs_inactive: "\<And>a b p. (a,b) \<in> B \<Longrightarrow>
      p \<in> fun_poss a \<Longrightarrow> p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_rhs_delta: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> (set Rs) (Q - Rgt) B"
  shows "finite_muterm_min_typed_dpp shp \<mu> (set Rs) Q B"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have closure: "(csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<subseteq> Rge"
  proof
    fix st
    assume "st \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    then have "st \<in> Rge\<^sup>*" by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD])
    then show "st \<in> Rge" using rp.refl_NS rp.trans_NS
      by (simp add: trans_refl_imp_rtrancl_id)
  qed
  have typed_order: "(weak.i1 s,weak.i1 t) \<in> Rgt \<union> Rge \<and>
      ((weak.i1 s,weak.i1 t) \<notin> Rgt \<longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (Q - Rgt) B)"
    if typed: "(s,t) \<in> muterm_typed_pair_step Q B" for s t
  proof (rule i1_typed_pair_redpair_order)
    show "compat_redpair_order Rgt Rge" by (rule redpair)
    show "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge" by (rule rewrite_weak)
    show "Q \<subseteq> Rgt \<union> Rge" by (rule pairs_order)
    show "B \<subseteq> Rge" by (rule bridges_order)
    show "\<And>l r p. (l,r) \<in> Q \<Longrightarrow> p \<in> fun_poss l \<Longrightarrow>
      p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule pair_lhs_inactive)
    show "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
      by (rule pair_rhs_delta)
    show "\<And>a b p. (a,b) \<in> B \<Longrightarrow> p \<in> fun_poss a \<Longrightarrow>
      p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule bridge_lhs_inactive)
    show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
      by (rule bridge_rhs_delta)
    show "(s,t) \<in> muterm_typed_pair_step Q B" by (rule typed)
  qed
  show ?thesis unfolding finite_muterm_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair_targeted[
      OF redpair, where G="\<lambda>t. \<exists>f ts. t = Fun (shp f) ts \<and>
        (\<forall>n. \<mu> (shp f,n) = \<mu> (f,n))"])
    fix s t
    assume pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) Q B"
    then show "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      unfolding muterm_min_typed_pair_step_def by auto
  next
    fix s t
    assume pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) Q B"
    then have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      unfolding muterm_min_typed_pair_step_def by auto
    from typed have cases: "muterm_noncollapsing_rrstep Q s t \<or>
      (\<exists>x. muterm_collapsing_rrstep Q s x \<and> (x,t) \<in> rrstep B)"
      unfolding muterm_typed_pair_step_def by auto
    from cases show "\<exists>f ts. t = Fun (shp f) ts \<and>
        (\<forall>n. \<mu> (shp f,n) = \<mu> (f,n))"
    proof
      assume nc: "muterm_noncollapsing_rrstep Q s t"
      then obtain l r \<sigma> where pair: "(l,r) \<in> Q" and rfun: "is_Fun r"
        and t: "t = r \<cdot> \<sigma>"
        unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
      from pair_rhs_shape pair rfun obtain g rs where rshape: "r = Fun (shp g) rs"
        by (cases r, auto)
      have mu: "\<forall>n. \<mu> (shp g,n) = \<mu> (g,n)"
        by (intro allI, rule pair_rhs_marked_mu[OF pair rshape])
      show ?thesis using rshape t mu by auto
    next
      assume coll: "\<exists>x. muterm_collapsing_rrstep Q s x \<and> (x,t) \<in> rrstep B"
      then obtain x a b \<sigma> where bridge: "(a,b) \<in> B" and t: "t = b \<cdot> \<sigma>"
        unfolding rrstep_def' by auto
      from bridge_rhs_shape bridge obtain g rs where bshape: "b = Fun (shp g) rs"
        by auto
      have mu: "\<forall>n. \<mu> (shp g,n) = \<mu> (g,n)"
        by (intro allI, rule bridge_rhs_marked_mu[OF bridge bshape])
      show ?thesis using bshape t mu by auto
    qed
  next
    fix s t
    assume "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) Q B"
    then have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      unfolding muterm_min_typed_pair_step_def by auto
    from typed_order[OF typed]
    show "(weak.i1 s,weak.i1 t) \<in> Rgt \<union> Rge" by blast
  next
    fix s t
    assume "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) Q B"
      and not_strict: "(weak.i1 s,weak.i1 t) \<notin> Rgt"
    from pair have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
      unfolding muterm_min_typed_pair_step_def by auto
    from typed_order[OF typed] not_strict
    have residual: "(s,t) \<in> muterm_typed_pair_step (Q - Rgt) B" by blast
    show "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> (set Rs) (Q - Rgt) B"
      unfolding muterm_min_typed_pair_step_def using residual target_SN by auto
  next
    fix s t
    assume marked: "\<exists>f ts. s = Fun (shp f) ts \<and>
        (\<forall>n. \<mu> (shp f,n) = \<mu> (f,n))"
      and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
      and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
    from marked obtain f ss where s: "s = Fun (shp f) ss"
      and marked_mu: "\<And>n. \<mu> (shp f,n) = \<mu> (f,n)" by blast
    from i1_sharp_csdp_steps[OF fresh marked_inj marked_mu s source_SN steps]
    show "(weak.i1 s,weak.i1 t) \<in> Rge"
      by (rule closure[THEN subsetD])
  next
    show "SN_rel (muterm_min_typed_pair_step shp \<mu> (set Rs) (Q - Rgt) B)
      (csdp_step shp \<mu> (set Rs))"
      using fin unfolding finite_muterm_min_typed_dpp_def .
  qed
qed

end

theorem finite_muterm_innermost_min_typed_dpp_i1_redpair:
  fixes Rs :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab),string) rules"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs (set Rs)"
    and closed: "csr_rta08_usable_rules_closed (set Rs) U \<mu> Q"
    and overlay: "csr_switch_overlay (set Rs)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and pair_rhs_marked_mu: "\<And>l r g rs n. (l,r) \<in> Q \<Longrightarrow>
      r = Fun (Sharp g) rs \<Longrightarrow> \<mu> (Sharp g,n) = \<mu> (g,n)"
    and bridge_rhs_marked_mu: "\<And>a b g rs n. (a,b) \<in> B \<Longrightarrow>
      b = Fun (Sharp g) rs \<Longrightarrow> \<mu> (Sharp g,n) = \<mu> (g,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "Q \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>Q. \<exists>f ls. l = Fun (Sharp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>Q. is_Var r \<or>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (Sharp g) rs"
    and pair_lhs_inactive: "\<And>l r p. (l,r) \<in> Q \<Longrightarrow>
      p \<in> fun_poss l \<Longrightarrow> p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and pair_rhs_delta: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_lhs_inactive: "\<And>a b p. (a,b) \<in> B \<Longrightarrow>
      p \<in> fun_poss a \<Longrightarrow> p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
    and bridge_rhs_delta: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp \<mu> (set Rs)
      (Q - Rgt) B"
  shows "finite_muterm_innermost_min_typed_dpp Sharp \<mu> (set Rs) Q B"
proof -
  interpret I: csr_rta08_i1 Rs U \<mu> Q cn
    by (unfold_locales, rule wf, rule closed)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have closure: "(csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<subseteq> Rge"
  proof
    fix st
    assume "st \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    then have "st \<in> Rge\<^sup>*"
      by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD])
    then show "st \<in> Rge" using rp.refl_NS rp.trans_NS
      by (simp add: trans_refl_imp_rtrancl_id)
  qed
  have typed_order: "(I.weak.i1 s,I.weak.i1 t) \<in> Rgt \<union> Rge \<and>
      ((I.weak.i1 s,I.weak.i1 t) \<notin> Rgt \<longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (Q - Rgt) B)"
    if typed: "(s,t) \<in> muterm_typed_pair_step Q B" for s t
  proof (rule I.i1_typed_pair_redpair_order)
    show "compat_redpair_order Rgt Rge" by (rule redpair)
    show "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge" by (rule rewrite_weak)
    show "Q \<subseteq> Rgt \<union> Rge" by (rule pairs_order)
    show "B \<subseteq> Rge" by (rule bridges_order)
    show "\<And>l r p. (l,r) \<in> Q \<Longrightarrow> p \<in> fun_poss l \<Longrightarrow>
      p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule pair_lhs_inactive)
    show "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
      by (rule pair_rhs_delta)
    show "\<And>a b p. (a,b) \<in> B \<Longrightarrow> p \<in> fun_poss a \<Longrightarrow>
      p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule bridge_lhs_inactive)
    show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
      by (rule bridge_rhs_delta)
    show "(s,t) \<in> muterm_typed_pair_step Q B" by (rule typed)
  qed
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair_targeted[
      OF redpair, where I=I.weak.i1 and
      G="\<lambda>t. \<exists>f ts. t = Fun (Sharp f) ts \<and>
        SN_on (csdp_step Sharp \<mu> (set Rs)) {t} \<and>
        (\<forall>n. \<mu> (Sharp f,n) = \<mu> (f,n))"])
    fix s t
    assume pair: "(s,t) \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) Q B"
    from pair obtain u where t: "t = sharp_term Sharp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    show "SN_on (innermost_csdp_step Sharp \<mu> (set Rs)) {t}"
      unfolding t by (rule innermost_mu_Tinf_imp_SN_sharp_innermost_csdp[
        OF wf fresh inj_Sharp uT])
  next
    fix s t
    assume pair: "(s,t) \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) Q B"
    from pair have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      and source: "innermost_pair_source Sharp \<mu> (set Rs) s"
      and target: "\<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from target obtain u where t_u: "t = sharp_term Sharp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))" by blast
    have full_uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
      by (rule mu_Tinf_innermost_imp_mu_Tinf[OF overlay wf uT])
    have full_SN: "SN_on (csdp_step Sharp \<mu> (set Rs)) {t}"
      unfolding t_u by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh full_uT])
    from typed have cases: "muterm_noncollapsing_rrstep Q s t \<or>
      (\<exists>x. muterm_collapsing_rrstep Q s x \<and> (x,t) \<in> rrstep B)"
      unfolding muterm_typed_pair_step_def by auto
    from cases show "\<exists>f ts. t = Fun (Sharp f) ts \<and>
        SN_on (csdp_step Sharp \<mu> (set Rs)) {t} \<and>
        (\<forall>n. \<mu> (Sharp f,n) = \<mu> (f,n))"
    proof
      assume nc: "muterm_noncollapsing_rrstep Q s t"
      then obtain l r \<sigma> where qr: "(l,r) \<in> Q" and rfun: "is_Fun r"
        and t: "t = r \<cdot> \<sigma>"
        unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
      from pair_rhs_shape qr rfun obtain g rs where r: "r = Fun (Sharp g) rs"
        by (cases r, auto)
      have marked: "\<forall>n. \<mu> (Sharp g,n) = \<mu> (g,n)"
        by (intro allI, rule pair_rhs_marked_mu[OF qr r])
      show ?thesis using r t marked full_SN by auto
    next
      assume coll: "\<exists>x. muterm_collapsing_rrstep Q s x \<and>
        (x,t) \<in> rrstep B"
      then obtain x a b \<sigma> where bridge: "(a,b) \<in> B"
        and t: "t = b \<cdot> \<sigma>" unfolding rrstep_def' by auto
      from bridge_rhs_shape bridge obtain g rs where b: "b = Fun (Sharp g) rs"
        by auto
      have marked: "\<forall>n. \<mu> (Sharp g,n) = \<mu> (g,n)"
        by (intro allI, rule bridge_rhs_marked_mu[OF bridge b])
      show ?thesis using b t marked full_SN by auto
    qed
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step Sharp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) Q B"
    from pair have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from typed_order[OF typed]
    show "(I.weak.i1 s,I.weak.i1 t) \<in> Rgt \<union> Rge" by blast
  next
    fix s t
    assume source_SN: "SN_on (innermost_csdp_step Sharp \<mu> (set Rs)) {s}"
      and pair: "(s,t) \<in> muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) Q B"
      and not_strict: "(I.weak.i1 s,I.weak.i1 t) \<notin> Rgt"
    from pair have typed: "(s,t) \<in> muterm_typed_pair_step Q B"
      and pair_source: "innermost_pair_source Sharp \<mu> (set Rs) s"
      and target_inv: "t \<in> {v. \<exists>u. v = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))}"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    from typed_order[OF typed] not_strict
    have residual: "(s,t) \<in> muterm_typed_pair_step (Q - Rgt) B" by blast
    have residual_inner: "(s,t) \<in> muterm_innermost_typed_pair_step
      Sharp \<mu> (set Rs) (Q - Rgt) B"
      unfolding muterm_innermost_typed_pair_step_def
      using residual pair_source by auto
    show "(s,t) \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) (Q - Rgt) B"
      unfolding muterm_innermost_min_typed_pair_step_def
      using residual_inner target_inv by auto
  next
    fix s t
    assume marked: "\<exists>f ts. s = Fun (Sharp f) ts \<and>
        SN_on (csdp_step Sharp \<mu> (set Rs)) {s} \<and>
        (\<forall>n. \<mu> (Sharp f,n) = \<mu> (f,n))"
      and source_SN:
        "SN_on (innermost_csdp_step Sharp \<mu> (set Rs)) {s}"
      and steps: "(s,t) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    from marked obtain f ss where s: "s = Fun (Sharp f) ss"
      and full_SN: "SN_on (csdp_step Sharp \<mu> (set Rs)) {s}"
      and marked_mu: "\<And>n. \<mu> (Sharp f,n) = \<mu> (f,n)" by blast
    have full_steps: "(s,t) \<in> (csdp_step Sharp \<mu> (set Rs))\<^sup>*"
      by (rule rtrancl_mono[OF innermost_csdp_step_subset_csdp_step,
        THEN subsetD, OF steps])
    from I.i1_sharp_csdp_steps[
      OF fresh inj_Sharp marked_mu s full_SN full_steps]
    show "(I.weak.i1 s,I.weak.i1 t) \<in> Rge"
      by (rule closure[THEN subsetD])
  next
    show "SN_rel (muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs)
      (Q - Rgt) B) (innermost_csdp_step Sharp \<mu> (set Rs))"
      using fin unfolding finite_muterm_innermost_min_typed_dpp_def .
  qed
qed

lemma csr_u3_all_closed_funas_delta:
  assumes closed: "csr_u3_root_rules_closed R U t (fun_poss t)"
  shows "funas_term t \<subseteq> csr_u3_delta R U"
proof
  fix f
  assume member: "f \<in> funas_term t"
  from member[unfolded funas_term_poss_conv]
  obtain p g ts where f: "f = (g,length ts)"
    and p: "p \<in> poss t" and at: "t |_ p = Fun g ts"
    by auto
  have p: "p \<in> fun_poss t"
    using p at unfolding fun_poss_poss by simp
  have root: "root (t |_ p) = Some f"
    using f at by simp
  show "f \<in> csr_u3_delta R U"
    by (rule csr_u3_root_rules_closed_delta[OF closed p root])
qed

text \<open>
  The RTA'08 interpretation uses closure at all inactive roots of pair
  left-hand sides and at all roots of non-variable pair right-hand sides.
  Unlike the older basic usable-rule processor above, it does not require
  collapsing dependency pairs to satisfy the conservativity condition.
\<close>

definition muterm_general_rta08_ur_redpair_proc where
  "muterm_general_rta08_ur_redpair_proc J \<mu> rp Premove U B dpp =
    check_return (case rel_impl.not_wst rp of
      None \<Rightarrow> error (showsl_lit
        (STR ''general RTA'08 MU-TERM reduction pair does not expose weak-subterm exceptions''))
    | Some F \<Rightarrow> do {
        rel_impl_redpair rp;
        let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
        check (csr_rta08_usable_rules_check
            (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
          (showsl_lit (STR ''general RTA'08 MU-TERM usable-rule closure failed''));
        check (list_all (\<lambda>dp. is_Var (snd dp) \<or>
            csr_u3_all_root_rules_check
              (dpp_ops.rules J dpp) U (snd dp)) (dpp_ops.pairs J dpp))
          (showsl_lit (STR ''general RTA'08 MU-TERM pair RHS closure failed''));
        check (list_all (\<lambda>lr. csr_u3_inactive_root_rules_check
            (dpp_ops.rules J dpp) U \<mu> (fst lr)) B)
          (showsl_lit (STR ''general RTA'08 MU-TERM unhiding LHS closure failed''));
        check (list_all (\<lambda>lr. csr_u3_all_root_rules_check
            (dpp_ops.rules J dpp) U (snd lr)) B)
          (showsl_lit (STR ''general RTA'08 MU-TERM unhiding RHS closure failed''));
        check (muterm_general_typed_shape_check (dpp_ops.pairs J dpp) B)
          (showsl_lit (STR ''general RTA'08 MU-TERM typed pair or unhiding shape failed''));
        check (muterm_marked_mu_equal_check \<mu>)
          (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
        rel_impl.ce_compat rp;
        rel_impl_ns rp
          (U @ B @ csr_rta08_projection_rules_list \<mu> F @ pns)
          <+? (\<lambda>s. showsl_lit
            (STR ''problem weakly orienting general RTA'08 MU-TERM rules, unhiding rules, projections, or pairs\<newline>'' ) \<circ> s);
        rel_impl_s rp ps
          <+? (\<lambda>s. showsl_lit
            (STR ''problem strictly orienting general RTA'08 MU-TERM pairs\<newline>'' ) \<circ> s)
      }) (dpp_spec.delete_pairs J dpp Premove)"

theorem finite_muterm_min_typed_dpp_general_rta08_redpair:
  fixes Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and shp :: "'f \<Rightarrow> 'f"
  assumes wf: "wf_trs (set Rs)"
    and closed: "csr_rta08_usable_rules_closed (set Rs) U \<mu> Q"
    and pair_rhs_closed: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (fun_poss r)"
    and bridge_lhs_closed: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U a
        {p\<in>fun_poss a. p \<notin> mu_fun_poss \<mu> a}"
    and bridge_rhs_closed: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U b (fun_poss b)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and pair_rhs_marked_mu: "\<And>l r g rs n. (l,r) \<in> Q \<Longrightarrow>
      r = Fun (shp g) rs \<Longrightarrow> \<mu> (shp g,n) = \<mu> (g,n)"
    and bridge_rhs_marked_mu: "\<And>a b g rs n. (a,b) \<in> B \<Longrightarrow>
      b = Fun (shp g) rs \<Longrightarrow> \<mu> (shp g,n) = \<mu> (g,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "Q \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>Q. \<exists>f ls. l = Fun (shp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>Q. is_Var r \<or>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (shp g) rs"
    and U_weak: "U \<subseteq> Rge"
    and ce: "ce_compatible Rge"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> (set Rs) (Q - Rgt) B"
  shows "finite_muterm_min_typed_dpp shp \<mu> (set Rs) Q B"
proof (cases "Q = {}")
  case True
  with fin show ?thesis by simp
next
  case False
  then obtain dp where dp: "dp \<in> Q" by blast
  from pair_lhs_shape dp obtain f ss where lhs: "fst dp = Fun (shp f) ss"
    by (cases dp, auto)
  obtain n where ce_bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(shp f,n)"
  have ce_weak: "ce_trs ?cn \<subseteq> Rge" by (rule ce_bound, simp)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have rules_weak: "U \<union> ce_trs ?cn \<subseteq> Rge" using U_weak ce_weak by auto
  have rewrite_weak: "csstep \<mu> (U \<union> ce_trs ?cn) \<subseteq> Rge"
    by (rule subset_trans[OF csstep_subset_rstep
      subset_trans[OF rstep_mono[OF rules_weak] rp.rstep_NS]])
  interpret I: csr_rta08_i1 Rs U \<mu> Q ?cn
    by (unfold_locales, rule wf, rule closed)
  have pair_lhs_inactive: "\<And>l r p. (l,r) \<in> Q \<Longrightarrow>
      p \<in> fun_poss l \<Longrightarrow> p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix l r p
    assume lr: "(l,r) \<in> Q" and p: "p \<in> fun_poss l"
      and inactive: "p \<notin> mu_fun_poss \<mu> l"
    from closed have pairs_closed:
      "\<forall>dp\<in>Q. csr_u3_root_rules_closed (set Rs) U (fst dp)
        {q\<in>fun_poss (fst dp). q \<notin> mu_fun_poss \<mu> (fst dp)}"
      unfolding csr_rta08_usable_rules_closed_def by blast
    have roots0:
      "csr_u3_root_rules_closed (set Rs) U (fst (l,r))
        {q\<in>fun_poss (fst (l,r)). q \<notin> mu_fun_poss \<mu> (fst (l,r))}"
      by (rule pairs_closed[rule_format, OF lr])
    from roots0 have roots:
      "csr_u3_root_rules_closed (set Rs) U l
        {q\<in>fun_poss l. q \<notin> mu_fun_poss \<mu> l}"
      by simp
    show "funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_inactive_subterm_delta[OF roots p inactive])
  qed
  have bridge_lhs_inactive: "\<And>a b p. (a,b) \<in> B \<Longrightarrow>
      p \<in> fun_poss a \<Longrightarrow> p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix a b p
    assume ab: "(a,b) \<in> B" and pos: "p \<in> fun_poss a"
      and inactive: "p \<notin> mu_fun_poss \<mu> a"
    show "funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_inactive_subterm_delta[
        OF bridge_lhs_closed[OF ab] pos inactive])
  qed
  have pair_rhs_delta: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix l r
    assume lr: "(l,r) \<in> Q" and r: "is_Fun r"
    show "funas_term r \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_all_closed_funas_delta[
        OF pair_rhs_closed[OF lr r]])
  qed
  have bridge_rhs_delta: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix a b
    assume ab: "(a,b) \<in> B"
    show "funas_term b \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_all_closed_funas_delta[
        OF bridge_rhs_closed[OF ab]])
  qed
  show ?thesis
    by (rule I.finite_muterm_min_typed_dpp_i1_redpair[
      OF fresh marked_inj pair_rhs_marked_mu bridge_rhs_marked_mu redpair rewrite_weak pairs_order bridges_order
        pair_lhs_shape pair_rhs_shape bridge_rhs_shape pair_lhs_inactive
        pair_rhs_delta bridge_lhs_inactive bridge_rhs_delta fin])
qed

theorem finite_muterm_innermost_min_typed_dpp_general_rta08_redpair:
  fixes Rs :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab),string) rules"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes wf: "wf_trs (set Rs)"
    and overlay: "csr_switch_overlay (set Rs)"
    and closed: "csr_rta08_usable_rules_closed (set Rs) U \<mu> Q"
    and pair_rhs_closed: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (fun_poss r)"
    and bridge_lhs_closed: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U a
        {p\<in>fun_poss a. p \<notin> mu_fun_poss \<mu> a}"
    and bridge_rhs_closed: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U b (fun_poss b)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and pair_rhs_marked_mu: "\<And>l r g rs n. (l,r) \<in> Q \<Longrightarrow>
      r = Fun (Sharp g) rs \<Longrightarrow> \<mu> (Sharp g,n) = \<mu> (g,n)"
    and bridge_rhs_marked_mu: "\<And>a b g rs n. (a,b) \<in> B \<Longrightarrow>
      b = Fun (Sharp g) rs \<Longrightarrow> \<mu> (Sharp g,n) = \<mu> (g,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "Q \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_lhs_shape: "\<forall>(l,r)\<in>Q. \<exists>f ls. l = Fun (Sharp f) ls"
    and pair_rhs_shape: "\<forall>(l,r)\<in>Q. is_Var r \<or>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and bridge_rhs_shape: "\<forall>(a,b)\<in>B. \<exists>g rs. b = Fun (Sharp g) rs"
    and U_weak: "U \<subseteq> Rge"
    and ce: "ce_compatible Rge"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp \<mu> (set Rs)
      (Q - Rgt) B"
  shows "finite_muterm_innermost_min_typed_dpp Sharp \<mu> (set Rs) Q B"
proof (cases "Q = {}")
  case True
  with fin show ?thesis by simp
next
  case False
  then obtain dp where dp: "dp \<in> Q" by blast
  from pair_lhs_shape dp obtain f ss where lhs: "fst dp = Fun (Sharp f) ss"
    by (cases dp, auto)
  obtain n where ce_bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> Rge"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(Sharp f,n)"
  have ce_weak: "ce_trs ?cn \<subseteq> Rge" by (rule ce_bound, simp)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have rules_weak: "U \<union> ce_trs ?cn \<subseteq> Rge"
    using U_weak ce_weak by auto
  have rewrite_weak: "csstep \<mu> (U \<union> ce_trs ?cn) \<subseteq> Rge"
    by (rule subset_trans[OF csstep_subset_rstep
      subset_trans[OF rstep_mono[OF rules_weak] rp.rstep_NS]])
  have pair_lhs_inactive: "\<And>l r p. (l,r) \<in> Q \<Longrightarrow>
      p \<in> fun_poss l \<Longrightarrow> p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
      funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix l r p
    assume lr: "(l,r) \<in> Q" and p: "p \<in> fun_poss l"
      and inactive: "p \<notin> mu_fun_poss \<mu> l"
    from closed have pairs_closed:
      "\<forall>dp\<in>Q. csr_u3_root_rules_closed (set Rs) U (fst dp)
        {q\<in>fun_poss (fst dp). q \<notin> mu_fun_poss \<mu> (fst dp)}"
      unfolding csr_rta08_usable_rules_closed_def by blast
    have roots: "csr_u3_root_rules_closed (set Rs) U l
        {q\<in>fun_poss l. q \<notin> mu_fun_poss \<mu> l}"
      using pairs_closed[rule_format, OF lr] by simp
    show "funas_term (l |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_inactive_subterm_delta[OF roots p inactive])
  qed
  have bridge_lhs_inactive: "\<And>a b p. (a,b) \<in> B \<Longrightarrow>
      p \<in> fun_poss a \<Longrightarrow> p \<notin> mu_fun_poss \<mu> a \<Longrightarrow>
      funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
  proof -
    fix a b p
    assume ab: "(a,b) \<in> B" and pos: "p \<in> fun_poss a"
      and inactive: "p \<notin> mu_fun_poss \<mu> a"
    show "funas_term (a |_ p) \<subseteq> csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_inactive_subterm_delta[
        OF bridge_lhs_closed[OF ab] pos inactive])
  qed
  have pair_rhs_delta: "\<And>l r. (l,r) \<in> Q \<Longrightarrow> is_Fun r \<Longrightarrow>
      funas_term r \<subseteq> csr_u3_delta (set Rs) U"
    by (rule csr_u3_all_closed_funas_delta,
      rule pair_rhs_closed)
  have bridge_rhs_delta: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      funas_term b \<subseteq> csr_u3_delta (set Rs) U"
    by (rule csr_u3_all_closed_funas_delta,
      rule bridge_rhs_closed)
  show ?thesis
    by (rule finite_muterm_innermost_min_typed_dpp_i1_redpair[
      OF wf closed overlay fresh pair_rhs_marked_mu bridge_rhs_marked_mu
        redpair rewrite_weak pairs_order bridges_order pair_lhs_shape
        pair_rhs_shape bridge_rhs_shape pair_lhs_inactive pair_rhs_delta
        bridge_lhs_inactive bridge_rhs_delta fin])
qed

theorem muterm_general_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_general_ur_redpair_proc J \<mu> rp Premove U B dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.rules J dpp')) (set (dpp_ops.pairs J dpp')) (set B)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp)) (set (dpp_ops.pairs J dpp)) (set B)"
proof -
  interpret dpp_spec J by fact
  obtain F where not_wst: "rel_impl.not_wst rp = Some F"
    using proc unfolding muterm_general_ur_redpair_proc_def
    by (cases "rel_impl.not_wst rp"; auto)
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_general_ur_redpair_proc_def not_wst
      option.case Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and U_R_check: "list_all (\<lambda>lr. lr \<in> set (rules dpp)) U"
    and closed: "list_all (\<lambda>lr. csr_rta08_active_root_rules_check
      (rules dpp) U \<mu> (snd lr))
      (muterm_extended_basic_seed_list (pairs dpp) B U)"
    and conservative: "rhs_mu_vars_condition_list \<mu>
      (muterm_extended_basic_seed_list (pairs dpp) B U)"
    and lhs_partition: "list_all (\<lambda>(l,r).
      set (mu_vars_term_list \<mu> l) \<inter>
        set (non_mu_vars_term_list \<mu> l) = {}) (pairs dpp @ B @ U)"
    and collapsing_active: "list_all (\<lambda>(l,r). case r of
        Var x \<Rightarrow> x \<in> mu_vars_term (mu_of \<mu>) l
      | Fun f ts \<Rightarrow> True) (pairs dpp)"
    and shape: "muterm_general_typed_shape_check (pairs dpp) B"
    and bridge_lhs_shape: "list_all (is_Fun \<circ> fst) B"
    and marked: "muterm_marked_mu_equal_check \<mu>"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp
      (U @ B @ csr_rta08_projection_rules_list \<mu> F @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ B @ csr_rta08_projection_rules_list \<mu> F @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have all_rel': "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using all_rel' by presburger
  from rel_prop strict weak subst sn standard ce
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and B_NS: "set B \<subseteq> NS"
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
    and ce_NS: "ce_compatible NS"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have U_R: "set U \<subseteq> set (rules dpp)"
    using U_R_check by (auto simp: list_all_iff)
  have closed_rhs: "\<And>l r. (l,r) \<in>
      {lr \<in> set (pairs dpp). is_Fun (snd lr)} \<union> set B \<union> set U \<Longrightarrow>
      csr_u3_root_rules_closed (set (rules dpp)) (set U) r
        (mu_fun_poss (mu_of \<mu>) r)"
  proof -
    fix l r
    assume lr: "(l,r) \<in>
      {lr \<in> set (pairs dpp). is_Fun (snd lr)} \<union> set B \<union> set U"
    have all: "\<forall>lr\<in>set (muterm_extended_basic_seed_list
        (pairs dpp) B U).
        csr_rta08_active_root_rules_check (rules dpp) U \<mu> (snd lr)"
      using closed by (simp add: list_all_iff)
    have mem: "(l,r) \<in> set (muterm_extended_basic_seed_list
        (pairs dpp) B U)" using lr by simp
    have check: "csr_rta08_active_root_rules_check
        (rules dpp) U \<mu> r" using all[rule_format, OF mem] by simp
    show "csr_u3_root_rules_closed (set (rules dpp)) (set U) r
        (mu_fun_poss (mu_of \<mu>) r)"
      by (rule csr_rta08_active_root_rules_check_sound[OF check])
  qed
  have conservative_sem: "rhs_mu_vars_condition (mu_of \<mu>)
      ({lr \<in> set (pairs dpp). is_Fun (snd lr)} \<union> set B \<union> set U)"
    using rhs_mu_vars_condition_list_sound[OF conservative] by simp
  have lhs_partition_sem: "\<And>l r. (l,r) \<in>
      set (pairs dpp) \<union> set B \<union> set U \<Longrightarrow>
      mu_vars_term (mu_of \<mu>) l \<inter>
        non_mu_vars_term (mu_of \<mu>) l = {}"
    using lhs_partition
    by (auto simp: list_all_iff split: prod.splits)
  have collapsing_active_sem: "\<And>l y. (l,Var y) \<in> set (pairs dpp) \<Longrightarrow>
      y \<in> mu_vars_term (mu_of \<mu>) l"
    using collapsing_active
    by (auto simp: list_all_iff split: prod.splits term.splits)
  have shape_sem: "(\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))) \<and>
      (\<forall>(a,b)\<in>set B. \<exists>g rs. b = Fun (Sharp (UnLab g)) rs)"
    by (rule muterm_general_typed_shape_check_sound[OF shape])
  have pair_shapes: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))"
    by (rule conjunct1[OF shape_sem])
  have bridge_rhs_shape: "\<forall>(a,b)\<in>set B.
      \<exists>g rs. b = Fun (Sharp g) rs"
    using conjunct2[OF shape_sem] by blast
  have bridge_lhs_shape_sem: "\<forall>(a,b)\<in>set B. is_Fun a"
    using bridge_lhs_shape by (auto simp: list_all_iff split: prod.splits)
  have pair_lhs_shape: "\<forall>(l,r)\<in>set (pairs dpp).
      \<exists>f ls. l = Fun (Sharp f) ls"
  proof (intro ballI)
    fix dp
    assume dp: "dp \<in> set (pairs dpp)"
    show "case dp of (l,r) \<Rightarrow> \<exists>f ls. l = Fun (Sharp f) ls"
      using pair_shapes[rule_format, OF dp] by (cases dp; auto)
  qed
  have pair_rhs_shape: "\<forall>(l,r)\<in>set (pairs dpp). is_Var r \<or>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
  proof (intro ballI)
    fix dp
    assume dp: "dp \<in> set (pairs dpp)"
    show "case dp of (l,r) \<Rightarrow>
        is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs)"
      using pair_shapes[rule_format, OF dp] by (cases dp; auto)
  qed
  have pair_lhs_marked_mu: "\<And>l r g ss. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      l = Fun (Sharp g) ss \<Longrightarrow>
      mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
  proof -
    fix l r g ss
    assume lr: "(l,r) \<in> set (pairs dpp)" and l: "l = Fun (Sharp g) ss"
    from pair_shapes[rule_format, OF lr] l obtain h where g: "g = UnLab h" by auto
    show "mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
      unfolding g by (rule muterm_marked_mu_equal_check_sound_unlab[OF marked])
  qed
  have pair_rhs_marked_mu: "\<And>l r g ss. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      r = Fun (Sharp g) ss \<Longrightarrow>
      mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
  proof -
    fix l r g ss
    assume lr: "(l,r) \<in> set (pairs dpp)" and r: "r = Fun (Sharp g) ss"
    from pair_shapes[rule_format, OF lr] r obtain h where g: "g = UnLab h" by auto
    show "mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
      unfolding g by (rule muterm_marked_mu_equal_check_sound_unlab[OF marked])
  qed
  have bridge_rhs_marked_mu: "\<And>a b g ss. (a,b) \<in> set B \<Longrightarrow>
      b = Fun (Sharp g) ss \<Longrightarrow>
      mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
  proof -
    fix a b g ss
    assume ab: "(a,b) \<in> set B" and b: "b = Fun (Sharp g) ss"
    from conjunct2[OF shape_sem] ab b obtain h where g: "g = UnLab h" by auto
    show "mu_of \<mu> (Sharp g,length ss) = mu_of \<mu> (g,length ss)"
      unfolding g by (rule muterm_marked_mu_equal_check_sound_unlab[OF marked])
  qed
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq> set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have step_sub: "muterm_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B) \<subseteq>
      muterm_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - set Premove) (set B)"
    by (rule muterm_min_typed_pair_step_mono[OF sub])
  have fin_S: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B)"
    unfolding finite_muterm_min_typed_dpp_def
    by (rule SN_rel_mono[OF step_sub subset_refl
      fin[unfolded pairs' rules' finite_muterm_min_typed_dpp_def]])
  show ?thesis
    by (rule finite_muterm_min_typed_dpp_general_usable_redpair[
      OF wf closed_rhs conservative_sem lhs_partition_sem
        collapsing_active_sem U_R fresh inj_Sharp pair_lhs_marked_mu
        pair_rhs_marked_mu bridge_rhs_marked_mu redpair orient B_NS
        pair_lhs_shape pair_rhs_shape bridge_lhs_shape_sem bridge_rhs_shape
        U_NS ce_NS fin_S])
qed

text \<open>
  Executable soundness wrapper for the RTA'08/i1 usable-rule processor.  Its
  closure checks deliberately differ from the older conservative processor.
\<close>
theorem muterm_innermost_general_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_general_rta08_ur_redpair_proc J \<mu> rp Premove U B dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and overlay: "csr_switch_overlay (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.rules J dpp')) (set (dpp_ops.pairs J dpp')) (set B)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp)) (set (dpp_ops.pairs J dpp)) (set B)"
proof -
  interpret dpp_spec J by fact
  obtain F where not_wst: "rel_impl.not_wst rp = Some F"
    using proc unfolding muterm_general_rta08_ur_redpair_proc_def
    by (cases "rel_impl.not_wst rp"; auto)
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_general_rta08_ur_redpair_proc_def not_wst
      option.case Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and closed: "csr_rta08_usable_rules_check
      (rules dpp) U \<mu> (pairs dpp)"
    and pair_rhs: "list_all (\<lambda>dp. is_Var (snd dp) \<or>
      csr_u3_all_root_rules_check (rules dpp) U (snd dp)) (pairs dpp)"
    and bridge_lhs: "list_all (\<lambda>lr.
      csr_u3_inactive_root_rules_check (rules dpp) U \<mu> (fst lr)) B"
    and bridge_rhs: "list_all (\<lambda>lr.
      csr_u3_all_root_rules_check (rules dpp) U (snd lr)) B"
    and shape: "muterm_general_typed_shape_check (pairs dpp) B"
    and marked: "muterm_marked_mu_equal_check \<mu>"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp
      (U @ B @ csr_rta08_projection_rules_list \<mu> F @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ B @ csr_rta08_projection_rules_list \<mu> F @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have all_rel': "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using all_rel' by presburger
  from rel_prop strict weak subst sn standard ce
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and B_NS: "set B \<subseteq> NS"
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
    and ce_NS: "ce_compatible NS"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have closed_sem: "csr_rta08_usable_rules_closed
      (set (rules dpp)) (set U) (mu_of \<mu>) (set (pairs dpp))"
    by (rule csr_rta08_usable_rules_check_sound[OF closed])
  have pair_rhs_sem: "\<And>l r. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      csr_u3_root_rules_closed (set (rules dpp)) (set U) r (fun_poss r)"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set (pairs dpp)" and rfun: "is_Fun r"
    from pair_rhs have rhs_all: "\<forall>dp\<in>set (pairs dpp).
        is_Var (snd dp) \<or>
        csr_u3_all_root_rules_check (rules dpp) U (snd dp)"
      by (simp add: list_all_iff)
    have rhs_disj: "is_Var r \<or>
        csr_u3_all_root_rules_check (rules dpp) U r"
      using rhs_all[rule_format, OF lr] by simp
    have rhs_check: "csr_u3_all_root_rules_check (rules dpp) U r"
      using rhs_disj rfun by (cases r; auto)
    show "csr_u3_root_rules_closed (set (rules dpp)) (set U) r
        (fun_poss r)"
      by (rule csr_u3_all_root_rules_check_sound[OF rhs_check])
  qed
  have bridge_lhs_sem: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      csr_u3_root_rules_closed (set (rules dpp)) (set U) a
        {p\<in>fun_poss a. p \<notin> mu_fun_poss (mu_of \<mu>) a}"
  proof -
    fix a b
    assume ab: "(a,b) \<in> set B"
    from bridge_lhs have all: "\<forall>lr\<in>set B.
        csr_u3_inactive_root_rules_check (rules dpp) U \<mu> (fst lr)"
      by (simp add: list_all_iff)
    have check: "csr_u3_inactive_root_rules_check (rules dpp) U \<mu> a"
      using all[rule_format, OF ab] by simp
    show "csr_u3_root_rules_closed (set (rules dpp)) (set U) a
        {p\<in>fun_poss a. p \<notin> mu_fun_poss (mu_of \<mu>) a}"
      by (rule csr_u3_inactive_root_rules_check_sound[OF check])
  qed
  have bridge_rhs_sem: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      csr_u3_root_rules_closed (set (rules dpp)) (set U) b (fun_poss b)"
  proof -
    fix a b
    assume ab: "(a,b) \<in> set B"
    from bridge_rhs have all: "\<forall>lr\<in>set B.
        csr_u3_all_root_rules_check (rules dpp) U (snd lr)"
      by (simp add: list_all_iff)
    have check: "csr_u3_all_root_rules_check (rules dpp) U b"
      using all[rule_format, OF ab] by simp
    show "csr_u3_root_rules_closed (set (rules dpp)) (set U) b (fun_poss b)"
      by (rule csr_u3_all_root_rules_check_sound[OF check])
  qed
  have shape_sem: "(\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))) \<and>
      (\<forall>(a,b)\<in>set B. \<exists>g rs. b = Fun (Sharp (UnLab g)) rs)"
    by (rule muterm_general_typed_shape_check_sound[OF shape])
  have pair_shapes: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))"
    by (rule conjunct1[OF shape_sem])
  have bridge_rhs_shape: "\<forall>(a,b)\<in>set B.
      \<exists>g rs. b = Fun (Sharp g) rs"
    using conjunct2[OF shape_sem] by blast
  have pair_lhs_shape: "\<forall>(l,r)\<in>set (pairs dpp).
      \<exists>f ls. l = Fun (Sharp f) ls"
  proof (intro ballI)
    fix dp
    assume dp: "dp \<in> set (pairs dpp)"
    show "case dp of (l,r) \<Rightarrow> \<exists>f ls. l = Fun (Sharp f) ls"
      using pair_shapes[rule_format, OF dp] by (cases dp; auto)
  qed
  have pair_rhs_shape: "\<forall>(l,r)\<in>set (pairs dpp). is_Var r \<or>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
  proof (intro ballI)
    fix dp
    assume dp: "dp \<in> set (pairs dpp)"
    show "case dp of (l,r) \<Rightarrow>
        is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs)"
      using pair_shapes[rule_format, OF dp] by (cases dp; auto)
  qed
  have pair_rhs_marked_mu: "\<And>l r g rs n.
      (l,r) \<in> set (pairs dpp) \<Longrightarrow> r = Fun (Sharp g) rs \<Longrightarrow>
      mu_of \<mu> (Sharp g,n) = mu_of \<mu> (g,n)"
  proof -
    fix l r g rs n
    assume lr: "(l,r) \<in> set (pairs dpp)" and r: "r = Fun (Sharp g) rs"
    from pair_shapes[rule_format, OF lr] r obtain h where g: "g = UnLab h"
      by auto
    show "mu_of \<mu> (Sharp g,n) = mu_of \<mu> (g,n)"
      unfolding g by (rule muterm_marked_mu_equal_check_sound_unlab[OF marked])
  qed
  have bridge_rhs_marked_mu: "\<And>a b g rs n.
      (a,b) \<in> set B \<Longrightarrow> b = Fun (Sharp g) rs \<Longrightarrow>
      mu_of \<mu> (Sharp g,n) = mu_of \<mu> (g,n)"
  proof -
    fix a b g rs n
    assume ab: "(a,b) \<in> set B" and b: "b = Fun (Sharp g) rs"
    from conjunct2[OF shape_sem] ab b obtain h where g: "g = UnLab h"
      by auto
    show "mu_of \<mu> (Sharp g,n) = mu_of \<mu> (g,n)"
      unfolding g by (rule muterm_marked_mu_equal_check_sound_unlab[OF marked])
  qed
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq> set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have step_sub: "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B) \<subseteq>
      muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - set Premove) (set B)"
    by (rule muterm_innermost_min_typed_pair_step_mono_pairs[OF sub])
  have fin_S: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules dpp)) (set (pairs dpp) - S) (set B)"
    unfolding finite_muterm_innermost_min_typed_dpp_def
    by (rule SN_rel_mono[OF step_sub subset_refl
      fin[unfolded pairs' rules' finite_muterm_innermost_min_typed_dpp_def]])
  show ?thesis
    by (rule finite_muterm_innermost_min_typed_dpp_general_rta08_redpair[
      OF wf overlay closed_sem pair_rhs_sem bridge_lhs_sem bridge_rhs_sem fresh
        pair_rhs_marked_mu bridge_rhs_marked_mu redpair orient B_NS pair_lhs_shape pair_rhs_shape
        bridge_rhs_shape U_NS ce_NS fin_S])
qed

theorem muterm_innermost_general_ur_redpair_proc_sound_preserved_rules:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_general_rta08_ur_redpair_proc J \<mu> rp Premove U B dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and overlay: "csr_switch_overlay (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.rules J dpp)) (set (dpp_ops.pairs J dpp')) (set B)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.rules J dpp)) (set (dpp_ops.pairs J dpp)) (set B)"
proof -
  interpret dpp_spec J by fact
  obtain F where not_wst: "rel_impl.not_wst rp = Some F"
    using proc unfolding muterm_general_rta08_ur_redpair_proc_def
    by (cases "rel_impl.not_wst rp"; auto)
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from proc[unfolded muterm_general_rta08_ur_redpair_proc_def not_wst
      option.case Let_def split,simplified]
  have dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have fin': "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules dpp')) (set (pairs dpp')) (set B)"
    using fin unfolding rules' .
  show ?thesis
    by (rule muterm_innermost_general_ur_redpair_proc_sound[
      OF J rp proc wf overlay fresh fin'])
qed

theorem muterm_innermost_general_ur_redpair_proc_mk_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and proc: "muterm_general_rta08_ur_redpair_proc J \<mu> rp Premove U B
      (dpp_ops.mk J False False P [] [] [] R) = return dpp'"
    and rp: "rel_impl rp"
    and fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J dpp')) (set B)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set B)"
proof -
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  interpret dpp_spec J by fact
  have sem: "dpp ?d = (False,False,set P,{},{},{},set R)"
    using mk_sound[of False False P "[]" "[]" "[]" R] by simp
  have rules_d: "set (rules ?d) = set R"
    using sem dpp_sound[of ?d] rules_sound[of ?d] by auto
  have pairs_d: "set (pairs ?d) = set P"
    using sem dpp_sound[of ?d] pairs_sound[of ?d] by auto
  have wf_d: "wf_trs (set (rules ?d))" using wf unfolding rules_d .
  have overlay_d: "csr_switch_overlay (set (rules ?d))"
    using overlay unfolding rules_d .
  have fresh_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
    using fresh unfolding rules_d .
  have fin_d: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules ?d)) (set (pairs dpp')) (set B)"
    using fin unfolding rules_d .
  have full: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules ?d)) (set (pairs ?d)) (set B)"
    by (rule muterm_innermost_general_ur_redpair_proc_sound_preserved_rules[
      OF J rp proc wf_d overlay_d fresh_d fin_d])
  show ?thesis using full unfolding rules_d pairs_d .
qed

end
