theory SRS_Checker_Bridge
  imports SRS_Unary_Encoding TRS_Standard_Checker_Bridge
begin

text \<open>All SRS Standard configuration fields are explicit: unrestricted mode,
empty Q, and no weak rules. False in the checker call disallows assumptions.
These theorems concern the semantic checker input, not parsing or dispatch.\<close>
theorem srs_standard_checker_YES:
  assumes problem: "string_problem R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = word_rules x R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "srs_standard_terminates R"
proof -
  have "SN_qrel (tp_ops.qreltrs I tp)"
    by (rule check_trs_termination_proof[OF I J accepted])
  then have "SN (rstep (word_rules x R))"
    by (simp add: tp_spec.qreltrs_sound[OF I] mode Q strict weak standard_framework_iff)
  then show ?thesis using srs_standard_unary_iff[of R x] by blast
qed

theorem srs_standard_checker_NO:
  assumes problem: "string_problem R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = word_rules x R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_nontermination_proof I J False i tp prf)"
  shows "\<not> srs_standard_terminates R"
proof -
  have "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
    by (rule check_trs_nontermination_proof[OF I J accepted])
  then have "\<not> SN (rstep (word_rules x R))"
    by (simp add: tp_spec.rules_sound[OF I] mode Q strict weak)
  then show ?thesis using srs_standard_unary_iff[of R x] by blast
qed

theorem srs_relative_checker_YES:
  assumes problem: "string_problem R \<and> string_problem S"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = word_rules x R"
    and weak: "set (tp_ops.Rw I tp) = word_rules x S"
    and accepted: "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "srs_relative_terminates R S"
proof -
  have "SN_qrel (tp_ops.qreltrs I tp)"
    by (rule check_trs_termination_proof[OF I J accepted])
  then have "SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))"
    by (simp add: tp_spec.qreltrs_sound[OF I] mode Q strict weak SN_qrel_def)
  then show ?thesis using srs_relative_unary_iff[of R S x] by blast
qed

theorem srs_relative_checker_NO:
  assumes problem: "string_problem R \<and> string_problem S"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = word_rules x R"
    and weak: "set (tp_ops.Rw I tp) = word_rules x S"
    and accepted: "isOK (check_reltrs_nontermination_proof I J False i tp prf)"
  shows "\<not> srs_relative_terminates R S"
proof -
  have "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
    by (rule check_reltrs_nontermination_proof[OF I J accepted])
  then have "\<not> SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))"
    by (simp add: mode Q strict weak SN_qrel_def)
  then show ?thesis using srs_relative_unary_iff[of R S x] by blast
qed

ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms string_step_iff
    srs_standard_terminates_iff srs_relative_terminates_iff
    srs_standard_unary_iff srs_relative_unary_iff
    srs_standard_checker_YES srs_standard_checker_NO
    srs_relative_checker_YES srs_relative_checker_NO}
    then error "SRS: admitted proof in dependencies" else ()
\<close>
end
