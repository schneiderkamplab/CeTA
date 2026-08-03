theory CSR_Innermost_Unhiding_Checker
  imports CSR_Checker_Extensions.CSR_Innermost_DP_Checker
begin

definition direct_collapsing_mu_CSDP_on ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "direct_collapsing_mu_CSDP_on shp \<mu> R =
    {(sharp_term shp l, Var x) | l r x.
      (l,r) \<in> R \<and> x \<in> mu_vars_term \<mu> r \<and> x \<notin> mu_vars_term \<mu> l}"

definition direct_hidden_mu_CSDP_on ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow>
    'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "direct_hidden_mu_CSDP_on shp \<mu> D R =
    {(h, sharp_term shp h) | h. hidden_term_on \<mu> D R h}"

definition direct_innermost_csdp_coverage ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow>
    'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> bool"
where
  "direct_innermost_csdp_coverage shp \<mu> D R P S \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    direct_collapsing_mu_CSDP_on shp \<mu> R \<subseteq> P \<and>
    direct_hidden_mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    R \<subseteq> S \<and>
    (\<forall>f ts i. hides_position_on \<mu> D R (f,length ts) i \<longrightarrow>
      i < length ts \<longrightarrow> (Fun f ts, ts ! i) \<in> rstep S)"

lemma direct_coverage_mu:
  assumes "direct_innermost_csdp_coverage shp \<mu> D R P S"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding direct_innermost_csdp_coverage_def by auto

lemma direct_coverage_rules:
  assumes "direct_innermost_csdp_coverage shp \<mu> D R P S"
  shows "R \<subseteq> S"
  using assms unfolding direct_innermost_csdp_coverage_def by auto

lemma weak_prefix_relative_step:
  assumes pre: "(x,y) \<in> W\<^sup>*"
    and step: "(y,z) \<in> W\<^sup>* O P O W\<^sup>*"
  shows "(x,z) \<in> W\<^sup>* O P O W\<^sup>*"
proof -
  from step obtain a b where ya: "(y,a) \<in> W\<^sup>*"
    and ab: "(a,b) \<in> P" and bz: "(b,z) \<in> W\<^sup>*"
    unfolding relcomp_unfold by blast
  have xa: "(x,a) \<in> W\<^sup>*" by (rule rtrancl_trans[OF pre ya])
  show ?thesis unfolding relcomp_unfold using xa ab bz by blast
qed

lemma weak_prefix_relative_trancl:
  assumes pre: "(x,y) \<in> W\<^sup>*"
    and path: "(y,z) \<in> (W\<^sup>* O P O W\<^sup>*)\<^sup>+"
  shows "(x,z) \<in> (W\<^sup>* O P O W\<^sup>*)\<^sup>+"
  using path pre
proof (induct rule: trancl_induct)
  case (base z)
  from weak_prefix_relative_step[OF base.prems base.hyps]
  show ?case by (rule r_into_trancl)
next
  case (step y z)
  from step.hyps(3)[OF step.prems] step.hyps(2)
  show ?case by (rule trancl_into_trancl)
qed

lemma direct_hiding_context_unhides:
  assumes cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
    and C: "hiding_context_on \<mu> D R C"
  shows "(C\<langle>t\<rangle>,t) \<in> (rstep S)\<^sup>*"
  using C
proof (induct rule: hiding_context_on.induct)
  case hole
  then show ?case by simp
next
  case (more f bef aft C)
  let ?whole = "Fun f (bef @ C\<langle>t\<rangle> # aft)"
  have i: "length bef < length (bef @ C\<langle>t\<rangle> # aft)" by simp
  have nth: "(bef @ C\<langle>t\<rangle> # aft) ! length bef = C\<langle>t\<rangle>" by simp
  from cover[unfolded direct_innermost_csdp_coverage_def]
  have projections: "\<And>f ts i. hides_position_on \<mu> D R (f,length ts) i \<Longrightarrow>
      i < length ts \<Longrightarrow> (Fun f ts, ts ! i) \<in> rstep S"
    by blast
  have hide: "hides_position_on \<mu> D R
      (f,length (bef @ C\<langle>t\<rangle> # aft)) (length bef)"
    using more.hyps(1) by simp
  from projections[OF hide i] nth have
    first: "(?whole,C\<langle>t\<rangle>) \<in> rstep S" by simp
  from first more.hyps(3) show ?case by auto
qed

lemma direct_hidden_instance_step:
  assumes cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
    and hidden: "hidden_term_on \<mu> D R h"
  shows "(h \<cdot> \<sigma>, sharp_term shp (h \<cdot> \<sigma>)) \<in> rrstep P"
proof -
  have pair: "(h,sharp_term shp h) \<in> P"
    using cover hidden unfolding direct_innermost_csdp_coverage_def
      direct_hidden_mu_CSDP_on_def by blast
  have sharp: "sharp_term shp (h \<cdot> \<sigma>) = sharp_term shp h \<cdot> \<sigma>"
    using hidden_term_on_is_Fun[OF hidden] by (cases h, auto)
  show ?thesis using pair sharp by auto
qed

lemma direct_collapsing_instance_step:
  assumes cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
proof -
  have pair: "(sharp_term shp l,Var x) \<in> P"
    using cover lr xr xl unfolding direct_innermost_csdp_coverage_def
      direct_collapsing_mu_CSDP_on_def by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis using pair sharp by auto
qed

lemma direct_collapsing_hiding_path:
  assumes cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
    and C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
  shows "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp (h \<cdot> \<tau>)) \<in>
    ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  have first: "(sharp_term shp (l \<cdot> \<sigma>),\<sigma> x) \<in> rrstep P"
    by (rule direct_collapsing_instance_step[OF cover lr xr xl lhs])
  have middle: "(\<sigma> x,h \<cdot> \<tau>) \<in> (rstep S)\<^sup>*"
    using direct_hiding_context_unhides[OF cover C, of "h \<cdot> \<tau>"] sx by simp
  have last: "(h \<cdot> \<tau>,sharp_term shp (h \<cdot> \<tau>)) \<in> rrstep P"
    by (rule direct_hidden_instance_step[OF cover hidden])
  let ?A = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  have first_path: "(sharp_term shp (l \<cdot> \<sigma>),h \<cdot> \<tau>) \<in> ?A"
    using first middle by auto
  have last_path: "(h \<cdot> \<tau>,sharp_term shp (h \<cdot> \<tau>)) \<in> ?A"
    using last by auto
  have first_trancl: "(sharp_term shp (l \<cdot> \<sigma>),h \<cdot> \<tau>) \<in> ?A\<^sup>+"
    by (rule r_into_trancl[OF first_path])
  show ?thesis by (rule trancl_into_trancl[OF first_trancl last_path])
qed

lemma csrstep_hiding_rhs_imp_direct_path:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = u \<or> mu_supt \<mu> t u) \<and>
    (sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" by (elim csrstepE)
  from wf lr have lhs: "is_Fun l" and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f,length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)" by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_rhs: "t = ?u \<or> mu_supt \<mu> t ?u"
  proof (cases p)
    case Nil
    with t show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have "(r \<cdot> \<sigma>) |_ (i # q) = ?u" unfolding Cons by simp
    then show ?thesis unfolding t mu_supt_def using pos by blast
  qed
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> ?u = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r" and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from defs def len have fD: "(f,length ts) \<in> D" by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p" unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l" using iq mu_poss_imp_poss by blast
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
    have dp0: "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp ((r |_ p) \<cdot> \<sigma>))
        \<in> rrstep (mu_CSDP_on shp \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    have mono: "rrstep (mu_CSDP_on shp \<mu> D R) \<subseteq> rrstep P"
      by (rule rrstep_mono[OF direct_coverage_mu[OF cover]])
    from dp0 mono have pair: "(sharp_term shp s,sharp_term shp ?u) \<in> rrstep P"
      unfolding s sub_subst by auto
    have path: "(sharp_term shp s,sharp_term shp ?u) \<in>
        ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
      using pair by regexp
    with T_p active_rhs show ?thesis by blast
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x" and x_r: "x \<in> vars_term r"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)" and u: "?u = \<sigma> x |_ q2" by blast
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
        using supteq_Var[of x l] unfolding supt_supteq_conv by (cases l, auto)
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
        have sub: "\<sigma> x |_ (i # q) = ?u" using u Cons by simp
        show ?thesis unfolding mu_supt_def using ip sub by blast
      qed
      from hp s_supt_x not_mu_supt_x active_u T_p
      obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
        and hidden: "hidden_term_on \<mu> D R h"
        and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>" and uh: "?u = h \<cdot> \<tau>"
        unfolding has_hiding_property_def by blast
      have path: "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp (h \<cdot> \<tau>)) \<in>
          ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
        by (rule direct_collapsing_hiding_path[
          where shp=shp and \<mu>=\<mu> and D=D and R=R and P=P and S=S
            and l=l and r=r and x=x and \<sigma>=\<sigma> and C=C and h=h and \<tau>=\<tau>,
          OF cover lr xr_mu False lhs C hidden sx])
      with T_p active_rhs show ?thesis unfolding s uh by blast
    qed
  qed
qed

lemma hiding_imp_direct_relstep:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) t"
    and cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
    (sharp_term shp t,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R" using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    by (rule csnrsteps_hiding_property_preserve[OF wf defs pref hp sT])
  from csrstep_hiding_rhs_imp_direct_path[OF wf root hp_s notSN_v defs cover]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "v = u \<or> mu_supt \<mu> v u"
    and path: "(sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+" by blast
  have hp_u: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    by (rule csrstep_hiding_property_active_target[OF wf defs root hp_s active uT])
  have prefR: "(sharp_term shp t,sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have mono: "rstep R \<subseteq> rstep S"
    by (rule rstep_mono[OF direct_coverage_rules[OF cover]])
  have prefS: "(sharp_term shp t,sharp_term shp s) \<in> (rstep S)\<^sup>*"
    using prefR rtrancl_mono[OF mono] by blast
  have full_path: "(sharp_term shp t,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
    by (rule weak_prefix_relative_trancl[OF prefS path])
  with hp_u show ?thesis by blast
qed

theorem finite_direct_innermost_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "direct_innermost_csdp_coverage shp \<mu> D R P S"
    and fin: "finite_dpp (False,False,P,{},{},{},S)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_hiding_property \<mu> D R (csstep \<mu> R) t0"
    by (rule Tinf_has_hiding_property[OF t0_T])
  let ?A = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  have step_ex: "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule hiding_imp_direct_relstep[OF wf defs _ cover])
  have all_ex: "\<forall>t. \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) t \<longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+" using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
    "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) (nxt t) \<and>
      (sharp_term shp t,sharp_term shp (nxt t)) \<in> ?A\<^sup>+" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n),sharp_term shp (ts (Suc n))) \<in> ?A\<^sup>+" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A\<^sup>+"
    unfolding f_def using ts_step by simp
  have not_trancl: "\<not> SN (?A\<^sup>+)" unfolding SN_defs using chain by blast
  have sn_A: "SN ?A"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have "SN (?A\<^sup>+)" by (rule SN_imp_SN_trancl[OF sn_A])
  with not_trancl show False by contradiction
qed

definition direct_collapsing_mu_CSDP_list ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f muL \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "direct_collapsing_mu_CSDP_list shp \<mu> R =
    concat (map (\<lambda>(l,r).
      map (\<lambda>x. (sharp_term shp l, Var x))
        [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
          x \<notin> set (mu_vars_term_list \<mu> l)]) R)"

lemma direct_collapsing_mu_CSDP_list:
  "set (direct_collapsing_mu_CSDP_list shp \<mu> R) =
    direct_collapsing_mu_CSDP_on shp (mu_of \<mu>) (set R)"
  unfolding direct_collapsing_mu_CSDP_list_def
    direct_collapsing_mu_CSDP_on_def
  by (auto simp: set_concat split: prod.splits)

definition direct_hidden_mu_CSDP_list ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f muL \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "direct_hidden_mu_CSDP_list shp \<mu> D R =
    concat (map (\<lambda>(l,r).
      map (\<lambda>p. (r |_ p, sharp_term shp (r |_ p)))
        [p \<leftarrow> fun_poss_list r.
          p \<notin> set (mu_fun_poss_list \<mu> r) \<and>
          root (r |_ p) \<in> Some ` set D]) R)"

lemma direct_hidden_mu_CSDP_list:
  "set (direct_hidden_mu_CSDP_list shp \<mu> D R) =
    direct_hidden_mu_CSDP_on shp (mu_of \<mu>) (set D) (set R)"
  unfolding direct_hidden_mu_CSDP_list_def direct_hidden_mu_CSDP_on_def
    hidden_term_on_def inactive_fun_subterm_on_def
  by (auto simp: set_concat split: term.splits prod.splits)

definition direct_projection_rules_list ::
  "'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    ('f, string) rules"
where
  "direct_projection_rules_list \<mu> D R =
    concat (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs, xs ! i))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])
      (remdups (funas_trs_list R)))"

lemma direct_projection_rules_list_step:
  assumes fn: "(f,n) \<in> set (remdups (funas_trs_list R))"
    and hide: "hides_position_list \<mu> D R f n i"
    and len: "length ts = n" and i: "i < n"
  shows "(Fun f ts,ts ! i) \<in>
    rstep (set (direct_projection_rules_list \<mu> D R))"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  have ilen: "i < length ?xs" using i fresh by simp
  have nth_inst: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] ilen by simp
  let ?rs = "map (\<lambda>i. (Fun f ?xs,?xs ! i))
    [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i]"
  have rs_mem: "?rs \<in> set (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs,xs ! i))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])
      (remdups (funas_trs_list R)))"
    unfolding set_map
  proof (rule image_eqI[of _ _ "(f,n)"])
    show "?rs = (case (f,n) of (f,n) \<Rightarrow>
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs,xs ! i))
        [i \<leftarrow> [0..<n]. hides_position_list \<mu> D R f n i])"
      by (simp only: Let_def case_prod_conv)
    show "(f,n) \<in> set (remdups (funas_trs_list R))" by (rule fn)
  qed
  have pair_mem: "(Fun f ?xs,?xs ! i) \<in> set ?rs"
    using i hide by simp
  have rule: "(Fun f ?xs,?xs ! i) \<in>
      set (direct_projection_rules_list \<mu> D R)"
    unfolding direct_projection_rules_list_def
    using rs_mem pair_mem by (simp only: set_concat, blast)
  show ?thesis
  proof (rule rstepI[OF rule, where C = \<box> and \<sigma> = ?\<sigma>])
    show "Fun f ts = \<box>\<langle>Fun f ?xs \<cdot> ?\<sigma>\<rangle>" using inst by simp
    show "ts ! i = \<box>\<langle>?xs ! i \<cdot> ?\<sigma>\<rangle>" using nth_inst by simp
  qed
qed

definition direct_innermost_csr_dependency_pairs_tt ::
  "('dpp, ('f::{showl,compare_order},label_type) lab,string) dpp_ops \<Rightarrow>
    (('f,label_type) lab) muL \<Rightarrow>
    (('f,label_type) lab,string) rules \<Rightarrow>
    (('f,label_type) lab,string) rules \<Rightarrow>
    (('f,label_type) lab,string) rules \<Rightarrow> 'dpp result"
where
  "direct_innermost_csr_dependency_pairs_tt J \<mu> R P S \<equiv>
    let D = defined_list R;
        S0 = R @ direct_projection_rules_list \<mu> D R
    in check_return (do {
      check_wf_trs R;
      check_allm (\<lambda>(f,n). check ((Sharp f,n) \<notin> set D)
        (showsl_lit (STR ''sharping yields a defined symbol''))) D;
      check_all (\<lambda>dp. dp \<in> set P) (mu_CSDP_list Sharp R \<mu> D)
        <+? (\<lambda>_. showsl_lit (STR ''missing replacement-map dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (direct_collapsing_mu_CSDP_list Sharp \<mu> R)
        <+? (\<lambda>_. showsl_lit (STR ''missing direct collapsing dependency pair''));
      check_all (\<lambda>dp. dp \<in> set P)
        (direct_hidden_mu_CSDP_list Sharp \<mu> D R)
        <+? (\<lambda>_. showsl_lit (STR ''missing direct hidden-term dependency pair''));
      check_all (\<lambda>lr. lr \<in> set S) R
        <+? (\<lambda>_. showsl_lit (STR ''missing original weak rule''));
      check_all (\<lambda>lr. lr \<in> set S) (direct_projection_rules_list \<mu> D R)
        <+? (\<lambda>_. showsl_lit (STR ''missing direct unhiding projection rule''))
    }) (dpp_ops.mk J False False P [] [] [] S0)"

lemma direct_innermost_csr_dependency_pairs_tt_sound:
  fixes J :: "('dpp, ('f::{showl,compare_order},label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and tt: "direct_innermost_csr_dependency_pairs_tt J \<mu> R P S = return d"
  shows "d = dpp_ops.mk J False False P [] [] []
      (R @ direct_projection_rules_list \<mu> (defined_list R) R)"
    and "wf_trs (set R)"
    and "direct_innermost_csdp_coverage Sharp (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)
      (set (R @ direct_projection_rules_list \<mu> (defined_list R) R))"
proof -
  note tt' = tt[unfolded direct_innermost_csr_dependency_pairs_tt_def Let_def,
    simplified]
  from tt' show d: "d = dpp_ops.mk J False False P [] [] []
      (R @ direct_projection_rules_list \<mu> (defined_list R) R)" by auto
  from tt' show wf: "wf_trs (set R)" by auto
  have mu_cover: "mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R)
      \<subseteq> set P"
    using tt' mu_CSDP_list_split_semantics[of R \<mu> "defined_list R"] by auto
  have collapsing: "direct_collapsing_mu_CSDP_on Sharp (mu_of \<mu>) (set R)
      \<subseteq> set P"
    using tt' direct_collapsing_mu_CSDP_list[of Sharp \<mu> R] by auto
  have hidden: "direct_hidden_mu_CSDP_on Sharp (mu_of \<mu>)
      (set (defined_list R)) (set R) \<subseteq> set P"
    using tt' direct_hidden_mu_CSDP_list[of Sharp \<mu> "defined_list R" R] by auto
  let ?S0 = "R @ direct_projection_rules_list \<mu> (defined_list R) R"
  have rules: "set R \<subseteq> set ?S0" by auto
  have projections: "set (direct_projection_rules_list \<mu> (defined_list R) R)
      \<subseteq> set ?S0" by auto
  have projection_steps: "\<And>f ts i.
      hides_position_on (mu_of \<mu>) (set (defined_list R)) (set R)
        (f,length ts) i \<Longrightarrow>
      i < length ts \<Longrightarrow> (Fun f ts,ts ! i) \<in> rstep (set ?S0)"
  proof -
    fix f :: "('f,label_type) lab"
      and ts :: "(('f,label_type) lab,string) term list"
      and i
    assume hide: "hides_position_on (mu_of \<mu>) (set (defined_list R))
        (set R) (f,length ts) i" and i: "i < length ts"
    have fn0: "(f,length ts) \<in> set (funas_trs_list R)"
      using hides_position_on_funas[OF hide] by simp
    have fn: "(f,length ts) \<in> set (remdups (funas_trs_list R))"
      using fn0 by simp
    have hide_list: "hides_position_list \<mu> (defined_list R) R
        f (length ts) i"
      by (subst hides_position_list_correct, rule hide)
    have step: "(Fun f ts,ts ! i) \<in>
        rstep (set (direct_projection_rules_list \<mu> (defined_list R) R))"
      by (rule direct_projection_rules_list_step[
        where f = f and n = "length ts" and ts = ts,
        OF fn hide_list refl i])
    show "(Fun f ts,ts ! i) \<in> rstep (set ?S0)"
      using step rstep_mono[OF projections] by blast
  qed
  show "direct_innermost_csdp_coverage Sharp (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P) (set ?S0)"
    unfolding direct_innermost_csdp_coverage_def
    using mu_cover collapsing hidden rules projection_steps by blast
qed

lemma direct_innermost_csr_dependency_pairs_tt_finite_imp_SN:
  assumes J: "dpp_spec J"
    and tt: "direct_innermost_csr_dependency_pairs_tt J \<mu> R P S = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof -
  let ?S0 = "R @ direct_projection_rules_list \<mu> (defined_list R) R"
  from direct_innermost_csr_dependency_pairs_tt_sound[OF J tt]
  have d: "d = dpp_ops.mk J False False P [] [] [] ?S0"
    and wf: "wf_trs (set R)"
    and cover: "direct_innermost_csdp_coverage Sharp (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P) (set ?S0)" by auto
  have fin': "finite_dpp (False,False,set P,{},{},{},set ?S0)"
    using fin d dpp_spec.mk_sound[OF J] by simp
  have defs: "{f. defined (set R) f} \<subseteq> set (defined_list R)" by auto
  show ?thesis by (rule finite_direct_innermost_CSDP_imp_SN_csstep[
    OF wf defs cover fin'])
qed

end
