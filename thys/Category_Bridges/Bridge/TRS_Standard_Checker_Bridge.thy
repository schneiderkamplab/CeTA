theory TRS_Standard_Checker_Bridge
  imports TRS_Standard_Equivalence
    Proof_Checker_Base.Check_Termination Proof_Checker.Check_Nontermination
begin

lemma standard_framework_iff:
  "SN_qrel (False, {}, R, {}) \<longleftrightarrow> SN (rstep R)"
  by (simp add: SN_qrel_def)

text \<open>All Standard configuration fields are explicit: unrestricted mode,
empty Q, and no weak rules. False in the checker call disallows assumptions.
These theorems concern the semantic checker input, not parsing or dispatch.\<close>
theorem trs_standard_checker_YES:
  assumes problem: "trs_problem A R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "trs_standard_terminates A R"
proof -
  have "SN_qrel (tp_ops.qreltrs I tp)"
    by (rule check_trs_termination_proof[OF I J accepted])
  then have "SN (rstep (to_rules R))"
    by (simp add: tp_spec.qreltrs_sound[OF I] mode Q strict weak standard_framework_iff)
  then show ?thesis using trs_standard_terminates_iff[OF problem] by blast
qed

theorem trs_standard_checker_NO:
  assumes problem: "trs_problem A R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_nontermination_proof I J False i tp prf)"
  shows "\<not> trs_standard_terminates A R"
proof -
  have "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
    by (rule check_trs_nontermination_proof[OF I J accepted])
  then have "\<not> SN (rstep (to_rules R))"
    by (simp add: tp_spec.rules_sound[OF I] mode Q strict weak)
  then show ?thesis using trs_standard_nonterminates_iff[OF problem] by blast
qed

text \<open>The build rejects admitted proofs, including admissions inherited
through any of the equivalence or checker soundness theorems.\<close>
ML \<open>
  val _ =
    if Thm_Deps.has_skip_proof @{thms standard_step_iff
        trs_standard_terminates_iff_signature trs_standard_terminates_iff
        trs_standard_terminates_iff_on trs_standard_nonterminates_iff
        trs_standard_checker_YES trs_standard_checker_NO}
    then error "TRS Standard: admitted proof in theorem dependencies"
    else ()
\<close>
end
