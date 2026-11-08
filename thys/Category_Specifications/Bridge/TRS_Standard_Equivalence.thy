theory TRS_Standard_Equivalence
  imports Category_Specifications.TRS_Standard_Spec TRS.Signature_Extension
begin

text \<open>The translations are structural bijections. The signature graph
forgets only the option encoding, not arities.\<close>
fun to_term :: "('f,'v) standard_term \<Rightarrow> ('f,'v) term" where
  "to_term (SVar x) = Var x"
| "to_term (SFun f ts) = Fun f (map to_term ts)"
fun from_term :: "('f,'v) term \<Rightarrow> ('f,'v) standard_term" where
  "from_term (Var x) = SVar x"
| "from_term (Fun f ts) = SFun f (map from_term ts)"
lemma from_to [simp]: "from_term (to_term t) = t"
  by (induct t) (auto simp: map_idI)
lemma to_from [simp]: "to_term (from_term t) = t"
  by (induct t) (auto simp: map_idI)
lemma to_term_inj [simp]: "to_term s = to_term t \<longleftrightarrow> s = t"
  by (metis from_to)
definition to_signature where "to_signature A = {(f,n). A f = Some n}"
definition to_rules where "to_rules R = {(to_term l, to_term r) | l r. (l,r) \<in> R}"
definition from_rules where "from_rules R = {(from_term l, from_term r) | l r. (l,r) \<in> R}"
definition to_substitution where "to_substitution sigma = to_term \<circ> sigma"
definition from_substitution where "from_substitution sigma = from_term \<circ> sigma"
fun to_context where
  "to_context SHole = Hole"
| "to_context (SMore f ls C rs) = More f (map to_term ls) (to_context C) (map to_term rs)"
fun from_context where
  "from_context Hole = SHole"
| "from_context (More f ls C rs) = SMore f (map from_term ls) (from_context C) (map from_term rs)"
lemma contexts_roundtrip [simp]:
  "from_context (to_context C) = C" "to_context (from_context D) = D"
  by (induct C; simp add: map_idI) (induct D; simp add: map_idI)
lemma rules_roundtrip [simp]: "from_rules (to_rules R) = R" "to_rules (from_rules S) = S"
  by (auto simp: from_rules_def to_rules_def; metis from_to to_from)+
lemma substitutions_roundtrip [simp]:
  "from_substitution (to_substitution s) = s" "to_substitution (from_substitution sigma) = sigma"
  by (auto simp: from_substitution_def to_substitution_def fun_eq_iff)
lemma translate_subst [simp]:
  "to_term (standard_subst sigma t) = to_term t \<cdot> to_substitution sigma"
  by (induct t) (auto simp: to_substitution_def)
lemma translate_plug [simp]:
  "to_term (standard_plug C t) = (to_context C)\<langle>to_term t\<rangle>"
  by (induct C) auto
lemma correct_term_iff [simp]:
  "arity_correct A t \<longleftrightarrow> funas_term (to_term t) \<subseteq> to_signature A"
  by (induct t) (auto simp: to_signature_def list_all_iff)
lemma correct_context_iff [simp]:
  "correct_context A C \<longleftrightarrow> funas_ctxt (to_context C) \<subseteq> to_signature A"
  by (induct C) (auto simp: to_signature_def list_all_iff)
lemma correct_substitution_iff:
  "correct_substitution A sigma \<longleftrightarrow>
   (\<forall>x. funas_term (to_substitution sigma x) \<subseteq> to_signature A)"
  by (simp add: correct_substitution_def to_substitution_def)
lemma correct_rules:
  "standard_problem A R \<Longrightarrow> funas_trs (to_rules R) \<subseteq> to_signature A"
  by (fastforce simp: standard_problem_def to_rules_def funas_trs_def funas_rule_def)

text \<open>For reflection, repair substitution images of variables unused by the
rule to a variable. This matters: an arbitrary witness substitution may have
ill-sorted images outside the rule, even when its two instances are sorted.\<close>
lemma standard_step_iff:
  "standard_step A R s t \<longleftrightarrow>
    (to_term s, to_term t) \<in> sig_step (to_signature A) (rstep (to_rules R))"
proof
  assume "standard_step A R s t"
  then obtain l r C sigma where
    wf: "arity_correct A s" "arity_correct A t" and lr: "(l,r) \<in> R"
    and eq: "s = standard_plug C (standard_subst sigma l)"
      "t = standard_plug C (standard_subst sigma r)"
    by (auto simp: standard_step_def)
  have "(to_term s, to_term t) \<in> rstep (to_rules R)"
    unfolding eq
    apply (simp only: translate_plug translate_subst)
    apply (rule rstep.rstep[where C="to_context C" and \<sigma>="to_substitution sigma"
      and l="to_term l" and r="to_term r"])
    using lr by (auto simp: to_rules_def)
  then show "(to_term s, to_term t) \<in> sig_step (to_signature A) (rstep (to_rules R))"
    using wf by auto
next
  assume step: "(to_term s, to_term t) \<in> sig_step (to_signature A) (rstep (to_rules R))"
  then have wf: "funas_term (to_term s) \<subseteq> to_signature A"
    "funas_term (to_term t) \<subseteq> to_signature A" and rs:
    "(to_term s, to_term t) \<in> rstep (to_rules R)" by auto
  from rs obtain l' r' C sigma where lr': "(l',r') \<in> to_rules R"
    and eq: "to_term s = C\<langle>l' \<cdot> sigma\<rangle>" "to_term t = C\<langle>r' \<cdot> sigma\<rangle>"
    by (cases rule: rstep.cases) blast
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
  have se: "s = standard_plug (from_context C) (standard_subst (from_substitution ?sigma) l)"
    by (rule to_term_inj[THEN iffD1]) (use eq(1) sub(1) in \<open>simp add: l\<close>)
  have te: "t = standard_plug (from_context C) (standard_subst (from_substitution ?sigma) r)"
    by (rule to_term_inj[THEN iffD1]) (use eq(2) sub(2) in \<open>simp add: r\<close>)
  have wf': "arity_correct A s" "arity_correct A t" using wf by simp_all
  show "standard_step A R s t"
    unfolding standard_step_def using wf' ctxt subst lr se te by blast
qed

lemma trs_standard_terminates_iff_signature:
  "trs_standard_terminates A R \<longleftrightarrow> SN (sig_step (to_signature A) (rstep (to_rules R)))"
proof -
  have chains: "(\<exists>ts. \<forall>i. standard_step A R (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R)))"
  proof
    assume "\<exists>ts. \<forall>i. standard_step A R (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. standard_step A R (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))"
      by (intro exI[of _ "to_term \<circ> ts"]) (simp add: standard_step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))" by blast
    then show "\<exists>ts. \<forall>i. standard_step A R (ts i) (ts (Suc i))"
      by (intro exI[of _ "from_term \<circ> ts"]) (simp add: standard_step_iff)
  qed
  show ?thesis unfolding trs_standard_terminates_def SN_defs using chains by blast
qed

text \<open>Signature extension removes the restriction on terms. Its existing
proof also handles rules with variable left sides or extra right variables.\<close>
theorem trs_standard_terminates_iff:
  assumes "standard_problem A R"
  shows "trs_standard_terminates A R \<longleftrightarrow> SN (rstep (to_rules R))"
  unfolding trs_standard_terminates_iff_signature
  using SN_sig_rstep_imp_SN_rstep[OF correct_rules[OF assms]]
    SN_subset[of "rstep (to_rules R)" "sig_step (to_signature A) (rstep (to_rules R))"]
  unfolding sig_step_def by blast

theorem trs_standard_terminates_iff_on:
  assumes problem: "standard_problem A R"
  shows "trs_standard_terminates A R \<longleftrightarrow>
    SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
proof
  assume "trs_standard_terminates A R"
  then have "SN (rstep (to_rules R))"
    using trs_standard_terminates_iff[OF problem] by blast
  then show "SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
    unfolding SN_defs by blast
next
  assume "SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
  then have "SN (sig_step (to_signature A) (rstep (to_rules R)))"
    unfolding SN_defs sig_step_def by blast
  then show "trs_standard_terminates A R"
    by (simp add: trs_standard_terminates_iff_signature)
qed

corollary trs_standard_nonterminates_iff:
  "standard_problem A R \<Longrightarrow>
   (\<not> trs_standard_terminates A R) \<longleftrightarrow> \<not> SN (rstep (to_rules R))"
  by (simp add: trs_standard_terminates_iff)
end
