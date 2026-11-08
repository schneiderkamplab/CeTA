theory SRS_Relative_Integrated
  imports SRS_Standard_Integrated
begin

text \<open>Renaming the tail separately in each rule preserves the entire
rewrite relation, not only termination. Apply this to both rule partitions.\<close>
lemma word_rules_step_subset:
  assumes rep: "represents_words T R"
  shows "Trs.rstep (word_rules x R) \<subseteq> Trs.rstep T"
proof
  fix st assume "st \<in> Trs.rstep (word_rules x R)"
  then obtain C u v sigma where uv: "(u,v) \<in> R"
    and st: "st = (C\<langle>string_to_term (Var x) u \<cdot> sigma\<rangle>,
      C\<langle>string_to_term (Var x) v \<cdot> sigma\<rangle>)"
    by (cases st) (auto elim: Trs.rstep.cases simp: word_rules_def)
  obtain y where rule: "(string_to_term (Var y) u,string_to_term (Var y) v) \<in> T"
    using rep uv unfolding represents_words_def by blast
  show "st \<in> Trs.rstep T"
    using rstep_ctxt[OF rstep_subst[OF rstep_rule[OF rule], of "\<lambda>_. sigma x"], of C]
    by (simp add: st word_tail_subst)
qed

lemma represented_word_steps:
  assumes rep: "represents_words T R"
  shows "Trs.rstep T = Trs.rstep (word_rules x R)"
  by (rule subset_antisym[OF represented_step_subset[OF rep] word_rules_step_subset[OF rep]])

lemma represented_relative_words_iff:
  assumes "represents_words T R" "represents_words U S"
  shows "srs_relative_terminates R S \<longleftrightarrow> SN_rel (Trs.rstep T) (Trs.rstep U)"
proof -
  have T: "Trs.rstep T = Trs.rstep (word_rules undefined R)"
    by (rule represented_word_steps[OF assms(1)])
  have U: "Trs.rstep U = Trs.rstep (word_rules undefined S)"
    by (rule represented_word_steps[OF assms(2)])
  show ?thesis unfolding T U by (rule srs_relative_unary_iff)
qed

text \<open>The weak-rule variable condition follows from the string encoding.
Neither answer requires an additional branching-symbol or signature guard.\<close>
theorem srs_relative_integrated_decision:
  assumes strict: "represents_words (set Rs) R"
    and weak: "represents_words (set Ss) S"
    and accepted: "certify_integrated_cert_problem False
      (Inn_TRS_input No_Strategy Rs Ss) Termination (Decision b) certificate = Certified"
  shows "b \<longleftrightarrow> srs_relative_terminates R S"
  using certify_integrated_cert_problem_sound[OF accepted]
  by (simp add: desired_property_def default_nfs_flag_def SN_qrel_def
      represented_relative_words_iff[OF strict weak])

corollary srs_relative_integrated_YES:
  "represents_words (set Rs) R \<Longrightarrow> represents_words (set Ss) S \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
     Termination (Decision True) certificate = Certified \<Longrightarrow>
   srs_relative_terminates R S"
  using srs_relative_integrated_decision[where b=True] by blast

corollary srs_relative_integrated_NO:
  "represents_words (set Rs) R \<Longrightarrow> represents_words (set Ss) S \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
     Termination (Decision False) certificate = Certified \<Longrightarrow>
   \<not> srs_relative_terminates R S"
  using srs_relative_integrated_decision[where b=False] by blast

theorem srs_relative_serialized_decision:
  assumes strict: "represents_words (set Rs) R" and weak: "represents_words (set Ss) S"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (Inn_TRS_input No_Strategy Rs Ss, Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> srs_relative_terminates R S"
proof -
  have "certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
      Termination (Decision b) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule srs_relative_integrated_decision[OF strict weak])
qed

ML \<open>
  val results = @{thms represented_word_steps represented_relative_words_iff
    srs_relative_integrated_decision srs_relative_integrated_YES
    srs_relative_integrated_NO srs_relative_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof results then error "SRS Relative: admitted proof" else ()
  val names = Thm_Deps.all_oracles results
    |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("SRS Relative integrated oracle dependencies: " ^ commas names)
\<close>
end
