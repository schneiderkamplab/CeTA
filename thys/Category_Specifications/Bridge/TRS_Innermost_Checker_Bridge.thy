theory TRS_Innermost_Checker_Bridge
  imports TRS_Innermost_Equivalence
    Proof_Checker_Base.Check_Termination Proof_Checker.Check_Nontermination
begin

lemma innermost_framework_iff:
  "SN_qrel (False, lhss R, R, {}) \<longleftrightarrow> SN (irstep False R)"
  by (simp only: SN_qrel_def case_prod_conv irstep_def qrstep_empty_r SN_rel_empty2)

text \<open>The default Innermost configuration is explicit: normal-form substitution
mode is disabled, Q contains exactly the left sides, and there are no weak rules. False in the checker call disallows assumptions.
These theorems concern the semantic checker input, not parsing or dispatch.\<close>
theorem trs_innermost_checker_YES:
  fixes R :: "((('f::{countable,compare_order,showl},nat list) lab,string) standard_term \<times> (('f,nat list) lab,string) standard_term) set"
  assumes problem: "standard_problem A R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "set (tp_ops.Q I tp) = lhss (to_rules R)"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "trs_innermost_terminates A R"
proof -
  have "SN_qrel (tp_ops.qreltrs I tp)"
    by (rule check_trs_termination_proof[OF I J accepted])
  then have "SN (irstep False (to_rules R))"
    by (simp add: tp_spec.qreltrs_sound[OF I] mode Q strict weak innermost_framework_iff irstep_def)
  then show ?thesis using trs_innermost_terminates_iff[OF problem] by blast
qed

theorem trs_innermost_checker_NO:
  fixes R :: "((('f::{countable,compare_order,showl},nat list) lab,string) standard_term \<times> (('f,nat list) lab,string) standard_term) set"
  assumes problem: "standard_problem A R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "set (tp_ops.Q I tp) = lhss (to_rules R)"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "tp_ops.Rw I tp = []"
    and accepted: "isOK (check_trs_nontermination_proof I J False i tp prf)"
  shows "\<not> trs_innermost_terminates A R"
proof -
  have "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
    by (rule check_trs_nontermination_proof[OF I J accepted])
  then have "\<not> SN (irstep False (to_rules R))"
    by (simp add: tp_spec.rules_sound[OF I] mode Q strict weak irstep_def)
  then show ?thesis using trs_innermost_nonterminates_iff[OF problem] by blast
qed

text \<open>The build rejects admitted proofs, including admissions inherited
through any of the equivalence or checker soundness theorems.\<close>
ML \<open>
  val _ =
    if Thm_Deps.has_skip_proof @{thms innermost_step_iff
        trs_innermost_terminates_iff_signature trs_innermost_terminates_iff
        trs_innermost_terminates_iff_injection trs_innermost_terminates_iff_on
        trs_innermost_nonterminates_iff
        trs_innermost_checker_YES trs_innermost_checker_NO}
    then error "TRS Innermost: admitted proof in theorem dependencies"
    else ()
\<close>
end
