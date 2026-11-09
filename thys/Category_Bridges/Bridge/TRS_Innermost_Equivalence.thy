theory TRS_Innermost_Equivalence
  imports Category_Properties.TRS_Innermost_Properties
    TRS_Standard_Equivalence SN.Countable_Term
begin

lemma normal_iff_no_standard_step:
  assumes problem: "trs_problem A R" and wf: "arity_correct A t"
  shows "innermost_normal A R t \<longleftrightarrow> \<not> (\<exists>u. fo_step A R t u)"
proof -
  have target: "\<And>l r C sigma. (l,r) \<in> R \<Longrightarrow> correct_context A C \<Longrightarrow>
      correct_substitution A sigma \<Longrightarrow>
      arity_correct A (fo_plug C (fo_subst sigma r))"
    using problem unfolding trs_problem_def
    by (auto simp: correct_substitution_def funas_term_subst to_substitution_def)
  show ?thesis unfolding innermost_normal_def fo_step_def using wf target by blast
qed

lemma normal_iff:
  assumes wf: "arity_correct A t"
  shows "innermost_normal A R t \<longleftrightarrow> to_term t \<in> NF_terms (lhss (to_rules R))"
proof -
  have match: "(\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and> t = fo_plug C (fo_subst sigma l))
    \<longleftrightarrow> (\<exists>C q sigma. to_term t = C\<langle>q \<cdot> sigma\<rangle> \<and> q \<in> lhss (to_rules R))"
  proof
    assume "\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and> t = fo_plug C (fo_subst sigma l)"
    then obtain l r C sigma where lr: "(l,r) \<in> R" and eq: "t = fo_plug C (fo_subst sigma l)" by blast
    show "\<exists>C q sigma. to_term t = C\<langle>q \<cdot> sigma\<rangle> \<and> q \<in> lhss (to_rules R)"
      apply (rule exI[of _ "to_context C"], rule exI[of _ "to_term l"], rule exI[of _ "to_substitution sigma"])
      using lr eq by (force simp: to_rules_def image_iff)
  next
    assume "\<exists>C q sigma. to_term t = C\<langle>q \<cdot> sigma\<rangle> \<and> q \<in> lhss (to_rules R)"
    then obtain C l r sigma where lr: "(l,r) \<in> R" and eq: "to_term t = C\<langle>to_term l \<cdot> sigma\<rangle>"
      by (force simp: to_rules_def image_iff)
    let ?sigma = "\<lambda>x. if x \<in> vars_term (to_term l) then sigma x else Var undefined"
    have image: "\<And>x. funas_term (?sigma x) \<subseteq> to_signature A"
      using wf unfolding correct_term_iff eq by (auto simp: funas_term_subst)
    have sub: "to_term l \<cdot> ?sigma = to_term l \<cdot> sigma"
      by (rule term_subst_eq) auto
    have ctxt: "correct_context A (from_context C)"
      using wf unfolding correct_term_iff eq by simp
    have subst: "correct_substitution A (from_substitution ?sigma)"
      using image by (simp add: correct_substitution_iff)
    have t: "t = fo_plug (from_context C) (fo_subst (from_substitution ?sigma) l)"
      by (rule to_term_inj[THEN iffD1]) (use eq sub in \<open>simp\<close>)
    show "\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and> t = fo_plug C (fo_subst sigma l)"
      using lr ctxt subst t by blast
  qed
  show ?thesis unfolding innermost_normal_def NF_ctxt_subst using match by simp
qed

lemma proper_subterms_iff:
  "u \<in> proper_subterms t \<longleftrightarrow> to_term t \<rhd> to_term u"
  proof (induct t)
  case (SVar x)
  then show ?case by (simp add: supt_var)
next
  case (SFun f ts)
  have decomp: "Fun f (map to_term ts) \<rhd> to_term u \<longleftrightarrow>
    (\<exists>v\<in>set ts. to_term v = to_term u \<or> to_term v \<rhd> to_term u)"
  proof
    assume "Fun f (map to_term ts) \<rhd> to_term u"
    then show "\<exists>v\<in>set ts. to_term v = to_term u \<or> to_term v \<rhd> to_term u"
      by (cases rule: supt.cases) auto
  next
    assume "\<exists>v\<in>set ts. to_term v = to_term u \<or> to_term v \<rhd> to_term u"
    then obtain v where v: "v \<in> set ts" and rel: "to_term v = to_term u \<or> to_term v \<rhd> to_term u" by blast
    have mem: "to_term v \<in> set (map to_term ts)" using v by simp
    from rel show "Fun f (map to_term ts) \<rhd> to_term u"
    proof
      assume eq: "to_term v = to_term u"
      show ?thesis by (rule supt.arg) (use mem eq in simp)
    next
      assume step: "to_term v \<rhd> to_term u"
      show ?thesis by (rule supt.subt[OF mem step])
    qed
  qed
  show ?case using SFun decomp by auto
qed


lemma proper_subterms_correct:
  "arity_correct A t \<Longrightarrow> u \<in> proper_subterms t \<Longrightarrow> arity_correct A u"
  unfolding correct_term_iff proper_subterms_iff
  by (meson supt_imp_funas_term_subset subset_trans)

lemma normal_subterms_iff:
  assumes wf: "arity_correct A t"
  shows "(\<forall>u\<in>proper_subterms t. innermost_normal A R u) \<longleftrightarrow>
    (\<forall>u \<lhd> to_term t. u \<in> NF_terms (lhss (to_rules R)))"
proof -
  have point: "\<And>u. u \<in> proper_subterms t \<Longrightarrow>
    innermost_normal A R u \<longleftrightarrow> to_term u \<in> NF_terms (lhss (to_rules R))"
    using normal_iff proper_subterms_correct[OF wf] by blast
  show ?thesis
    using point proper_subterms_iff[of _ t] proper_subterms_iff[of "from_term _" t]
    by (metis to_from)
qed

lemma innermost_step_iff:
  "innermost_step A R s t \<longleftrightarrow>
    (to_term s, to_term t) \<in> sig_step (to_signature A) (irstep False (to_rules R))"
proof
  assume "innermost_step A R s t"
  then obtain l r C sigma where
    wf: "arity_correct A s" "arity_correct A t" and lr: "(l,r) \<in> R"
    and nf: "\<forall>u\<in>proper_subterms (fo_subst sigma l). innermost_normal A R u"
    and eq: "s = fo_plug C (fo_subst sigma l)"
      "t = fo_plug C (fo_subst sigma r)"
    by (auto simp: innermost_step_def)
  have redex: "arity_correct A (fo_subst sigma l)" using wf(1) unfolding eq by simp
  have nf': "\<forall>u \<lhd> to_term l \<cdot> to_substitution sigma. u \<in> NF_terms (lhss (to_rules R))"
    using normal_subterms_iff[OF redex, of R] nf by simp
  have "(to_term s, to_term t) \<in> irstep False (to_rules R)"
    unfolding irstep_def
    apply (rule qrstepI[where C="to_context C" and \<sigma>="to_substitution sigma"
      and l="to_term l" and r="to_term r"])
    using nf' lr eq by (auto simp: to_rules_def)
  then show "(to_term s, to_term t) \<in> sig_step (to_signature A) (irstep False (to_rules R))"
    using wf by auto
next
  assume step: "(to_term s, to_term t) \<in> sig_step (to_signature A) (irstep False (to_rules R))"
  then have wf: "funas_term (to_term s) \<subseteq> to_signature A"
    "funas_term (to_term t) \<subseteq> to_signature A" and rs:
    "(to_term s, to_term t) \<in> irstep False (to_rules R)" by auto
  from rs obtain l' r' C sigma where lr': "(l',r') \<in> to_rules R"
    and nf: "\<forall>u \<lhd> l' \<cdot> sigma. u \<in> NF_terms (lhss (to_rules R))"
    and eq: "to_term s = C\<langle>l' \<cdot> sigma\<rangle>" "to_term t = C\<langle>r' \<cdot> sigma\<rangle>"
    unfolding irstep_def by (elim qrstepE) blast
  from lr' obtain l r where lr: "(l,r) \<in> R" and l: "l' = to_term l" and r: "r' = to_term r"
    by (auto simp: to_rules_def)
  let ?sigma = "\<lambda>x. if x \<in> vars_term l' \<union> vars_term r' then sigma x else Var undefined"
  have image: "\<And>x. funas_term (?sigma x) \<subseteq> to_signature A"
    using wf unfolding eq by (auto simp: funas_term_subst)
  have sub: "l' \<cdot> ?sigma = l' \<cdot> sigma" "r' \<cdot> ?sigma = r' \<cdot> sigma"
    by (auto intro: term_subst_eq)
  have ctxt: "correct_context A (from_context C)"
    using wf(1) unfolding eq by simp
  have subst: "correct_substitution A (from_substitution ?sigma)"
    using image by (simp add: correct_substitution_iff)
  have se: "s = fo_plug (from_context C) (fo_subst (from_substitution ?sigma) l)"
    by (rule to_term_inj[THEN iffD1]) (use eq(1) sub(1) in \<open>simp add: l\<close>)
  have te: "t = fo_plug (from_context C) (fo_subst (from_substitution ?sigma) r)"
    by (rule to_term_inj[THEN iffD1]) (use eq(2) sub(2) in \<open>simp add: r\<close>)
  have wf': "arity_correct A s" "arity_correct A t" using wf by simp_all
  have redex: "arity_correct A (fo_subst (from_substitution ?sigma) l)"
    using wf'(1) unfolding se by simp
  have nf': "\<forall>u\<in>proper_subterms (fo_subst (from_substitution ?sigma) l). innermost_normal A R u"
    using normal_subterms_iff[OF redex, of R] nf sub(1) by (simp add: l)
  show "innermost_step A R s t"
    unfolding innermost_step_def using wf' ctxt subst lr se te nf' by blast
qed
lemma trs_innermost_terminates_iff_signature:
  "trs_innermost_terminates A R \<longleftrightarrow> SN (sig_step (to_signature A) (irstep False (to_rules R)))"
proof -
  have chains: "(\<exists>ts. \<forall>i. innermost_step A R (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (irstep False (to_rules R)))"
  proof
    assume "\<exists>ts. \<forall>i. innermost_step A R (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. innermost_step A R (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (irstep False (to_rules R))"
      by (intro exI[of _ "to_term \<circ> ts"]) (simp add: innermost_step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (irstep False (to_rules R))"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (irstep False (to_rules R))" by blast
    then show "\<exists>ts. \<forall>i. innermost_step A R (ts i) (ts (Suc i))"
      by (intro exI[of _ "from_term \<circ> ts"]) (simp add: innermost_step_iff)
  qed
  show ?thesis unfolding trs_innermost_terminates_def no_infinite_steps_def SN_defs using chains by blast
qed



text \<open>The signature-extension proof uses an injection of terms into
variables. We expose that assumption, then discharge it for countable symbols
and countably infinite variables. The signature-restricted theorem above has
no cardinality restriction.\<close>
theorem trs_innermost_terminates_iff_injection:
  fixes R :: "(('f,'v) fo_term \<times> ('f,'v) fo_term) set"
  assumes problem: "trs_problem A R"
    and injection: "inj (c :: ('f,'v) term \<Rightarrow> 'v)"
  shows "trs_innermost_terminates A R \<longleftrightarrow> SN (irstep False (to_rules R))"
proof -
  interpret cleaning_innermost "to_signature A" c by unfold_locales (rule injection)
  show ?thesis
  proof
    assume "trs_innermost_terminates A R"
    then have sn: "SN (sig_step (to_signature A) (irstep False (to_rules R)))"
      by (simp add: trs_innermost_terminates_iff_signature)
    have F: "funas_trs (to_rules R) \<subseteq> to_signature A" by (rule correct_rules[OF problem])
    have wwf: "wwf_qtrs (lhss (to_rules R)) (to_rules R)"
      using SN_sig_qrstep_imp_wwf_trs[OF sn[unfolded irstep_def] F] by simp
    have rel: "SN_rel (irstep False (to_rules R)) (qrstep False (lhss (to_rules R)) {})"
      unfolding irstep_def
      apply (rule clean_SN_rel)
      using F wwf sn by (simp_all add: irstep_def SN_rel_defs sig_step_def)
    then show "SN (irstep False (to_rules R))" by (simp add: SN_rel_defs)
  next
    assume "SN (irstep False (to_rules R))"
    then have "SN (sig_step (to_signature A) (irstep False (to_rules R)))"
      by (rule SN_subset) (auto simp: sig_step_def)
    then show "trs_innermost_terminates A R"
      by (simp add: trs_innermost_terminates_iff_signature)
  qed
qed

theorem trs_innermost_terminates_iff:
  fixes R :: "(('f::countable,'v::countable) fo_term \<times> ('f,'v) fo_term) set"
  assumes problem: "trs_problem A R"
  shows "trs_innermost_terminates A R \<longleftrightarrow> SN (irstep False (to_rules R))"
proof -
  have infinite_V: "infinite (UNIV :: 'v set)" using problem unfolding trs_problem_def by simp
  from ex_inj obtain tn :: "('f,'v) term \<Rightarrow> nat" where tn: "inj tn" by auto
  from infinite_countable_subset[OF infinite_V] obtain nv :: "nat \<Rightarrow> 'v" where nv: "inj nv" by blast
  have "inj (nv \<circ> tn)" using nv tn by (rule inj_compose)
  then show ?thesis by (rule trs_innermost_terminates_iff_injection[OF problem])
qed

theorem trs_innermost_terminates_iff_on:
  fixes R :: "(('f::countable,'v::countable) fo_term \<times> ('f,'v) fo_term) set"
  assumes problem: "trs_problem A R"
  shows "trs_innermost_terminates A R \<longleftrightarrow>
    SN_on (irstep False (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
proof
  assume "trs_innermost_terminates A R"
  then have "SN (irstep False (to_rules R))"
    using trs_innermost_terminates_iff[OF problem] by blast
  then show "SN_on (irstep False (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
    unfolding SN_defs by blast
next
  assume "SN_on (irstep False (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
  then have "SN (sig_step (to_signature A) (irstep False (to_rules R)))"
    unfolding SN_defs sig_step_def by blast
  then show "trs_innermost_terminates A R"
    by (simp add: trs_innermost_terminates_iff_signature)
qed

corollary trs_innermost_nonterminates_iff:
  fixes R :: "(('f::countable,'v::countable) fo_term \<times> ('f,'v) fo_term) set"
  assumes "trs_problem A R"
  shows "(\<not> trs_innermost_terminates A R) \<longleftrightarrow> \<not> SN (irstep False (to_rules R))"
  using trs_innermost_terminates_iff[OF assms] by blast
end
