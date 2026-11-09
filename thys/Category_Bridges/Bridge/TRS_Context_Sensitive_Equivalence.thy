theory TRS_Context_Sensitive_Equivalence
  imports Category_Properties.TRS_Context_Sensitive_Properties
    Rewriting_Sequence_Equivalence TRS_Representation CSR_Checker_Extensions.CSR_Innermost_Switch
begin
lemma permitted_context_iff:
  "permitted_context mu C \<longleftrightarrow>
    af_regarded_pos mu ((ctxt_apply_term (to_context C) (t))) (hole_pos (to_context C))"
  by (induct C) (auto simp: nth_append)

lemma csstep_context_iff:
  "(s,t) \<in> csstep mu R \<longleftrightarrow>
    (\<exists>l r C sigma. (l,r) \<in> R \<and>
      af_regarded_pos mu ((ctxt_apply_term C (l \<cdot> sigma))) (hole_pos C) \<and>
      s = (ctxt_apply_term C (l \<cdot> sigma)) \<and> t = (ctxt_apply_term C (r \<cdot> sigma)))"
proof
  assume "(s,t) \<in> csstep mu R"
  then obtain p lr sigma where step: "(s,t) \<in> rstep_r_p_s R lr p sigma"
    and cond: "csstep_cond mu p s"
    unfolding csstep_def csstep_p_def by auto
  obtain l r where lr_def: "lr = (l,r)" by (cases lr) auto
  have lr: "(l,r) \<in> R" and p: "p \<in> poss s"
    and eq: "s = (ctxt_apply_term (ctxt_of_pos_term p s) (l \<cdot> sigma))"
      "t = (ctxt_apply_term (ctxt_of_pos_term p s) (r \<cdot> sigma))"
    using step by (auto simp: rstep_r_p_s_def Let_def lr_def)
  have active: "af_regarded_pos mu s p" by (rule csstep_cond_imp_af_regarded_pos[OF cond p])
  show "\<exists>l r C sigma. (l,r) \<in> R \<and>
      af_regarded_pos mu ((ctxt_apply_term C (l \<cdot> sigma))) (hole_pos C) \<and>
      s = (ctxt_apply_term C (l \<cdot> sigma)) \<and> t = (ctxt_apply_term C (r \<cdot> sigma))"
    apply (rule exI[of _ l], rule exI[of _ r], rule exI[of _ "ctxt_of_pos_term p s"], rule exI[of _ sigma])
    using lr active eq hole_pos_ctxt_of_pos_term[OF p] by metis
next
  assume "\<exists>l r C sigma. (l,r) \<in> R \<and>
      af_regarded_pos mu ((ctxt_apply_term C (l \<cdot> sigma))) (hole_pos C) \<and>
      s = (ctxt_apply_term C (l \<cdot> sigma)) \<and> t = (ctxt_apply_term C (r \<cdot> sigma))"
  then obtain l r C sigma where lr: "(l,r) \<in> R"
    and active: "af_regarded_pos mu ((ctxt_apply_term C (l \<cdot> sigma))) (hole_pos C)"
    and eq: "s = (ctxt_apply_term C (l \<cdot> sigma))" "t = (ctxt_apply_term C (r \<cdot> sigma))" by blast
  have pos: "hole_pos C \<in> poss s" unfolding eq by simp
  have cond: "csstep_cond mu (hole_pos C) s"
    by (rule af_regarded_pos_imp_csstep_cond[OF pos]) (simp add: eq active)
  show "(s,t) \<in> csstep mu R"
    unfolding csstep_def csstep_p_def
    apply (intro CollectI case_prodI exI[of _ "hole_pos C"])
    apply (rule exI[of _ s], rule exI[of _ t])
    using lr cond pos eq by (auto simp: rstep_r_p_s_def)
qed
lemma context_sensitive_step_iff:
  "context_sensitive_step A mu R s t \<longleftrightarrow>
    (to_term s, to_term t) \<in> sig_step (to_signature A) (csstep mu (to_rules R))"
proof
  assume "context_sensitive_step A mu R s t"
  then obtain l r C sigma where
    wf: "arity_correct A s" "arity_correct A t" and lr: "(l,r) \<in> R"
    and permitted: "permitted_context mu C"
    and eq: "s = fo_plug C (fo_subst sigma l)"
      "t = fo_plug C (fo_subst sigma r)"
    by (auto simp: context_sensitive_step_def)
  have active: "af_regarded_pos mu ((ctxt_apply_term (to_context C) (to_term l \<cdot> to_substitution sigma))) (hole_pos (to_context C))"
    using permitted permitted_context_iff[of mu C "to_term l \<cdot> to_substitution sigma"] by blast
  have "(to_term s, to_term t) \<in> csstep mu (to_rules R)"
    unfolding csstep_context_iff
    apply (rule exI[of _ "to_term l"], rule exI[of _ "to_term r"])
    apply (rule exI[of _ "to_context C"], rule exI[of _ "to_substitution sigma"])
    using active eq lr by (auto simp: to_rules_def)
  then show "(to_term s, to_term t) \<in> sig_step (to_signature A) (csstep mu (to_rules R))"
    using wf by auto
next
  assume step: "(to_term s, to_term t) \<in> sig_step (to_signature A) (csstep mu (to_rules R))"
  then have wf: "funas_term (to_term s) \<subseteq> to_signature A"
    "funas_term (to_term t) \<subseteq> to_signature A" and rs:
    "(to_term s, to_term t) \<in> csstep mu (to_rules R)" by auto
  from rs obtain l' r' C sigma where lr': "(l',r') \<in> to_rules R"
    and eq: "to_term s = (ctxt_apply_term C (l' \<cdot> sigma))" "to_term t = (ctxt_apply_term C (r' \<cdot> sigma))"
    and active: "af_regarded_pos mu ((ctxt_apply_term C (l' \<cdot> sigma))) (hole_pos C)"
    unfolding csstep_context_iff by blast
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
  have permitted: "permitted_context mu (from_context C)"
    using active permitted_context_iff[of mu "from_context C" "l' \<cdot> sigma"] by simp
  have wf': "arity_correct A s" "arity_correct A t" using wf by simp_all
  show "context_sensitive_step A mu R s t"
    unfolding context_sensitive_step_def using wf' ctxt subst lr se te permitted by blast
qed


theorem trs_context_sensitive_terminates_iff:
  "trs_context_sensitive_terminates A mu R \<longleftrightarrow>
    SN (sig_step (to_signature A) (csstep mu (to_rules R)))"
proof -
  interpret step_translation to_term from_term "context_sensitive_step A mu R"
    "sig_step (to_signature A) (csstep mu (to_rules R))"
    by unfold_locales (simp_all add: context_sensitive_step_iff)
  show ?thesis by (simp only: trs_context_sensitive_terminates_def termination_iff)
qed
corollary trs_context_sensitive_nonterminates_iff:
  "(\<not> trs_context_sensitive_terminates A mu R) \<longleftrightarrow>
    \<not> SN (sig_step (to_signature A) (csstep mu (to_rules R)))"
  by (simp add: trs_context_sensitive_terminates_iff)
end
