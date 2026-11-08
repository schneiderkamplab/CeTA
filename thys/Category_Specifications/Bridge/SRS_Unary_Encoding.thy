theory SRS_Unary_Encoding
  imports SRS_Equivalence
begin
text \<open>A word is a chain of unary function symbols ending in one variable.
The same variable ends both sides of each encoded rule, including empty words.\<close>
definition word_rules where
  "word_rules x R = {(string_to_term (Var x) l,string_to_term (Var x) r) | l r. (l,r) \<in> R}"
lemma word_roundtrip [simp]:
  "term_to_string (string_to_term (Var x) w) = w"
  by (induct w) auto
lemma word_unary [simp]: "unary_term (string_to_term (Var x) w)"
  by (induct w) auto
lemma word_vars [simp]: "vars_term (string_to_term (Var x) w) = {x}"
  by (induct w) auto
lemma word_funas:
  "funas_term (string_to_term (Var x) w) \<subseteq> UNIV \<times> {1}"
  by (induct w) auto
lemma encoded_rules_funas:
  "funas_trs (word_rules x R) \<subseteq> UNIV \<times> {1}"
  using word_funas unfolding word_rules_def funas_trs_def funas_rule_def by fastforce
lemma encoded_rules_vars:
  "(l,r) \<in> word_rules x R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  by (auto simp: word_rules_def)
lemma word_rules_roundtrip [simp]: "srs_of_trs (word_rules x R) = R"
  by (auto simp: srs_of_trs_def word_rules_def; metis word_roundtrip word_unary)
lemma encoded_word_step:
  "(s,t) \<in> srs_step R \<Longrightarrow>
    (string_to_term (Var x) s,string_to_term (Var x) t) \<in> rstep (word_rules x R)"
  using srs_of_trs_step[of s t "word_rules x R" "Var x"] by simp
lemma projection_substitution:
  "term_to_string (string_to_term (Var x) w \<cdot> sigma) = w @ term_to_string (sigma x)"
  by (induct w) auto
lemma projection_context:
  "unary_ctxt C \<Longrightarrow> term_to_string C\<langle>t\<rangle> =
    term_to_string C\<langle>Var x\<rangle> @ term_to_string t"
  by (induct rule: unary_ctxt_induct) auto
lemma project_word_step:
  assumes "(s,t) \<in> sig_step (UNIV \<times> {1}) (rstep (word_rules x R))"
  shows "(term_to_string s,term_to_string t) \<in> srs_step R"
proof -
  from assms have unary: "unary_term s" and step: "(s,t) \<in> rstep (word_rules x R)"
    by (auto simp: sig_step_def intro!: funas_unary_conv)
  from step obtain l r C sigma where lr: "(l,r) \<in> R"
    and eq: "s = C\<langle>string_to_term (Var x) l \<cdot> sigma\<rangle>"
      "t = C\<langle>string_to_term (Var x) r \<cdot> sigma\<rangle>"
    by (cases rule: rstep.cases) (auto simp: word_rules_def)
  have C: "unary_ctxt C" using unary unfolding eq by (rule unary_ctxt_appl_imp_unary_ctxt)
  have se: "term_to_string s = term_to_string C\<langle>Var x\<rangle> @ l @ term_to_string (sigma x)"
    using projection_context[OF C, of "string_to_term (Var x) l \<cdot> sigma" x]
    by (simp only: eq(1) projection_substitution)
  have te: "term_to_string t = term_to_string C\<langle>Var x\<rangle> @ r @ term_to_string (sigma x)"
    using projection_context[OF C, of "string_to_term (Var x) r \<cdot> sigma" x]
    by (simp only: eq(2) projection_substitution)
  show ?thesis unfolding se te by (rule srs_step.step[OF lr])
qed

theorem srs_relative_unary_iff:
  "srs_relative_terminates R S \<longleftrightarrow>
    SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))"
proof
  assume "srs_relative_terminates R S"
  then have sn: "SN_rel (srs_step R) (srs_step S)" by (simp add: srs_relative_terminates_iff)
  have restricted: "SN_rel (sig_step (UNIV \<times> {1}) (rstep (word_rules x R)))
    (sig_step (UNIV \<times> {1}) (rstep (word_rules x S)))"
    by (rule relative_direct_simulation[OF sn project_word_step project_word_step])
  show "SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))"
    by (rule sig_ext_relative_rewriting_var_cond[OF encoded_rules_vars
      encoded_rules_funas encoded_rules_funas restricted])
next
  assume sn: "SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))"
  have "SN_rel (srs_step R) (srs_step S)"
    by (rule relative_direct_simulation[OF sn encoded_word_step encoded_word_step])
  then show "srs_relative_terminates R S" by (simp add: srs_relative_terminates_iff)
qed

lemma srs_empty [simp]: "srs_step {} = {}"
  by (auto elim: srs_step.cases)

theorem srs_standard_unary_iff:
  "srs_standard_terminates R \<longleftrightarrow> SN (rstep (word_rules x R))"
  using srs_relative_unary_iff[of R "{}" x]
  by (simp add: srs_standard_terminates_iff srs_relative_terminates_iff word_rules_def)
end
