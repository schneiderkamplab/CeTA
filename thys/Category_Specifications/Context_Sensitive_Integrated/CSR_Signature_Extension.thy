theory CSR_Signature_Extension
  imports Category_Specification_Bridges.TRS_Context_Sensitive_Equivalence
    Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin

lemma csr_active_argument:
  assumes step: "(s,t) \<in> csstep mu R"
    and active: "length before \<in> mu (f,Suc (length before + length after))"
  shows "(Fun f (before @ s # after),Fun f (before @ t # after)) \<in> csstep mu R"
proof -
  obtain l r C sigma where rule: "(l,r) \<in> R"
    and act: "af_regarded_pos mu C\<langle>l \<cdot> sigma\<rangle> (hole_pos C)"
    and eq: "s = C\<langle>l \<cdot> sigma\<rangle>" "t = C\<langle>r \<cdot> sigma\<rangle>"
    using step unfolding csstep_context_iff by blast
  show ?thesis unfolding csstep_context_iff
    apply (rule exI[of _ l], rule exI[of _ r])
    apply (rule exI[of _ "More f before C after"], rule exI[of _ sigma])
    using rule act eq active by (simp add: nth_append)
qed

locale csr_signature_extension =
  cleaning F "\<lambda>_. Var (undefined::'v)" for F :: "'f sig" +
  fixes mu :: "'f mu" and R :: "('f,'v)trs"
  assumes rules: "funas_trs R \<subseteq> F" and wf: "Trs.wf_trs R"
begin

abbreviation good_aliens where
  "good_aliens t \<equiv> \<forall>u\<in>set (aliens F t). SN_on (csstep mu R) {u}"

lemma rule_aliens_preserved:
  assumes lr: "(l,r) \<in> R"
    and good: "good_aliens (l \<cdot> sigma)"
  shows "good_aliens (r \<cdot> sigma)"
proof -
  have fs: "funas_term l \<subseteq> F" "funas_term r \<subseteq> F"
    using lr rules by (force simp: funas_trs_def funas_rule_def)+
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf lr unfolding Trs.wf_trs_def var_rhs_subset_lhs_def by auto
  show ?thesis using good vars
    by (auto simp: aliens_subst[OF fs(1)] aliens_subst[OF fs(2)])
qed

lemma clean_root_step:
  assumes lr: "(l,r) \<in> R"
  shows "(clean_term (l \<cdot> sigma),clean_term (r \<cdot> sigma)) \<in> sig_step F (csstep mu R)"
proof -
  have fs: "funas_term l \<subseteq> F" "funas_term r \<subseteq> F"
    using lr rules by (force simp: funas_trs_def funas_rule_def)+
  have "(l \<cdot> clean_subst sigma,r \<cdot> clean_subst sigma) \<in> csstep mu R"
    unfolding csstep_context_iff
    apply (rule exI[of _ l], rule exI[of _ r])
    apply (rule exI[of _ Hole], rule exI[of _ "clean_subst sigma"])
    using lr by simp
  then show ?thesis using fs funas_term_clean_term
    by (auto simp: sig_step_def funas_term_subst)
qed

definition terminating_step where
  "terminating_step = {(s,t). (s,t) \<in> csstep mu R \<and> SN_on (csstep mu R) {s}}"

lemma listrel1_surround:
  "(xs,ys) \<in> listrel1 Q \<Longrightarrow> (as @ xs @ bs,as @ ys @ bs) \<in> listrel1 Q"
  by (auto simp: listrel1_def) (metis append_assoc)

lemma clean_context_step:
  assumes lr: "(l,r) \<in> R"
    and act: "af_regarded_pos mu (ctxt_apply_term C (l \<cdot> sigma)) (hole_pos C)"
    and good: "good_aliens (ctxt_apply_term C (l \<cdot> sigma))"
  shows "good_aliens (ctxt_apply_term C (r \<cdot> sigma)) \<and>
    ((clean_term (ctxt_apply_term C (l \<cdot> sigma)),clean_term (ctxt_apply_term C (r \<cdot> sigma)))
      \<in> sig_step F (csstep mu R) \<or>
     (clean_term (ctxt_apply_term C (l \<cdot> sigma)) = clean_term (ctxt_apply_term C (r \<cdot> sigma)) \<and>
      (aliens F (ctxt_apply_term C (l \<cdot> sigma)),aliens F (ctxt_apply_term C (r \<cdot> sigma))) \<in> listrel1 terminating_step))"
  using act good
proof (induct C)
  case Hole
  then show ?case using clean_root_step[OF lr] rule_aliens_preserved[OF lr] by simp
next
  case (More f before C after)
  let ?s = "ctxt_apply_term C (l \<cdot> sigma)"
  let ?t = "ctxt_apply_term C (r \<cdot> sigma)"
  let ?ss = "Fun f (before @ ?s # after)"
  let ?tt = "Fun f (before @ ?t # after)"
  have active: "length before \<in> mu (f,Suc (length before + length after))"
    and inner: "af_regarded_pos mu ?s (hole_pos C)"
    using More.prems(1) by (simp_all add: nth_append)
  show ?case
  proof (cases "(f,Suc (length before + length after)) \<in> F")
    case False
    have st: "(?ss,?tt) \<in> csstep mu R"
      unfolding csstep_context_iff
      apply (rule exI[of _ l], rule exI[of _ r])
      apply (rule exI[of _ "More f before C after"], rule exI[of _ sigma])
      using lr More.prems(1) by simp
    have sn: "SN_on (csstep mu R) {?ss}"
      using More.prems(2) False by simp
    have sn': "SN_on (csstep mu R) {?tt}" by (rule step_preserves_SN_on[OF st sn])
    have "([?ss],[?tt]) \<in> listrel1 terminating_step"
      using st sn by (auto simp: listrel1_def terminating_step_def)
    then show ?thesis using sn' False by simp
  next
    case True
    have igood: "good_aliens ?s" using More.prems(2) True by auto
    note ih = More.hyps[OF inner igood]
    have newgood: "good_aliens ?tt" using ih More.prems(2) True by auto
    show ?thesis
    proof (cases "(clean_term ?s,clean_term ?t) \<in> sig_step F (csstep mu R)")
      case True
      have st: "(clean_term ?s,clean_term ?t) \<in> csstep mu R"
        using True by (simp add: sig_step_def)
      have lifted: "(Fun f (map clean_term before @ clean_term ?s # map clean_term after),
        Fun f (map clean_term before @ clean_term ?t # map clean_term after)) \<in> csstep mu R"
        by (rule csr_active_argument[OF st]) (simp add: active)
      then show ?thesis using newgood \<open>(f,Suc (length before + length after)) \<in> F\<close>
        funas_term_clean_term by (auto simp: sig_step_def)
    next
      case False
      have eq: "clean_term ?s = clean_term ?t" and silent: "(aliens F ?s,aliens F ?t) \<in> listrel1 terminating_step"
        using ih False by blast+
      have "(concat (map (aliens F) before) @ aliens F ?s @ concat (map (aliens F) after),
        concat (map (aliens F) before) @ aliens F ?t @ concat (map (aliens F) after)) \<in> listrel1 terminating_step"
        by (rule listrel1_surround[OF silent])
      then show ?thesis using newgood eq True by simp
    qed
  qed
qed

lemma clean_step:
  assumes "(s,t) \<in> csstep mu R" "good_aliens s"
  shows "good_aliens t \<and> ((clean_term s,clean_term t) \<in> sig_step F (csstep mu R) \<or>
    (clean_term s=clean_term t \<and> (aliens F s,aliens F t) \<in> listrel1 terminating_step))"
  using assms clean_context_step unfolding csstep_context_iff by blast

lemma SN_terminating_step: "SN terminating_step"
  using SN_restrict_SN_idemp[of "csstep mu R"]
  by (simp add: terminating_step_def restrict_SN_def)
lemma SN_aliens_step: "SN (listrel1 terminating_step)"
  using SN_terminating_step by (simp add: SN_iff_wf listrel1_converse[symmetric])

lemma good_aliens_terminate:
  assumes sn: "SN (sig_step F (csstep mu R))" and good: "good_aliens t"
  shows "SN_on (csstep mu R) {t}"
proof -
  have main: "\<forall>t. clean_term t = u \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}" for u
  proof (rule SN_induct[OF sn])
    fix u
    assume outer: "\<And>v. (u,v) \<in> sig_step F (csstep mu R) \<Longrightarrow>
      \<forall>t. clean_term t = v \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}"
    have inner_main: "\<forall>t. clean_term t=u \<longrightarrow> aliens F t=xs \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}" for xs
    proof (rule SN_induct[OF SN_aliens_step])
      fix xs
      assume inner: "\<And>ys. (xs,ys) \<in> listrel1 terminating_step \<Longrightarrow>
        \<forall>t. clean_term t=u \<longrightarrow> aliens F t=ys \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}"
      show "\<forall>t. clean_term t=u \<longrightarrow> aliens F t=xs \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}"
      proof (intro allI impI)
        fix t
        assume ct: "clean_term t=u" and at: "aliens F t=xs" and good: "good_aliens t"
        show "SN_on (csstep mu R) {t}"
        proof (rule step_reflects_SN_on)
          fix v assume tv: "(t,v) \<in> csstep mu R"
          have gv: "good_aliens v" using clean_step[OF tv good] by blast
          show "SN_on (csstep mu R) {v}"
          proof (cases "(clean_term t,clean_term v) \<in> sig_step F (csstep mu R)")
            case True
            have e: "(u,clean_term v) \<in> sig_step F (csstep mu R)" using True ct by simp
            show ?thesis using outer[OF e, rule_format, of v] gv by simp
          next
            case False
            have cv: "clean_term v=u" and e: "(xs,aliens F v) \<in> listrel1 terminating_step"
              using clean_step[OF tv good] False ct at by auto
            show ?thesis using inner[OF e, rule_format, of v] cv gv by simp
          qed
        qed
      qed
    qed
    show "\<forall>t. clean_term t=u \<longrightarrow> good_aliens t \<longrightarrow> SN_on (csstep mu R) {t}"
      using inner_main by blast
  qed
  show ?thesis using main[of "clean_term t"] good by blast
qed

lemma extension:
  assumes sn: "SN (sig_step F (csstep mu R))"
  shows "SN (csstep mu R)"
proof -
  have all: "good_aliens t \<and> SN_on (csstep mu R) {t}" for t
  proof (induct t)
    case (Var x)
    show ?case using SN_on_csstep_Var[OF wf, of mu x] by simp
  next
    case (Fun f ts)
    show ?case
    proof (cases "(f,length ts) \<in> F")
      case True
      have good: "good_aliens (Fun f ts)" using Fun.hyps True by auto
      show ?thesis using good good_aliens_terminate[OF sn good] by blast
    next
      case False
      have undef: "\<not> defined R (f,length ts)"
      proof
        assume "defined R (f,length ts)"
        then obtain l r where lr: "(l,r) \<in> R" and root: "Term.root l = Some (f,length ts)"
          unfolding defined_def by blast
        have "(f,length ts) \<in> funas_term l" using root by (cases l) auto
        then have "(f,length ts) \<in> F" using lr rules
          by (force simp: funas_trs_def funas_rule_def)
        with False show False by contradiction
      qed
      have norm: "SN_on (csstep mu R) {Fun f ts}"
        using csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef] Fun.hyps
        by (meson nth_mem)
      then show ?thesis using False by simp
    qed
  qed
  show ?thesis using all unfolding SN_defs by blast
qed
end


text \<open>Unused constructors cannot introduce divergence when rules have
nonvariable left sides and do not introduce new variables. These hypotheses
are discharged by the relevant checker branches, not imposed on the category.\<close>
lemma csr_signature_extension:
  assumes "funas_trs R \<subseteq> F" "Trs.wf_trs R"
    "SN (sig_step F (csstep mu R))"
  shows "SN (csstep mu R)"
proof -
  interpret e: csr_signature_extension F mu R
    by unfold_locales (use assms in auto)
  show ?thesis by (rule e.extension[OF assms(3)])
qed
end
