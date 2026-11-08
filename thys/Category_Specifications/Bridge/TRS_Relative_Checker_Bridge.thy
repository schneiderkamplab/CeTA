theory TRS_Relative_Checker_Bridge
  imports TRS_Relative_Equivalence
    Proof_Checker_Base.Check_Termination Proof_Checker.Check_Nontermination
begin

text \<open>The YES direction needs no signature-extension assumption. The NO
direction does: unrestricted nontermination need not live inside the declared
signature. Both calls forbid certificate assumptions.\<close>
theorem trs_relative_checker_YES:
  assumes problem: "relative_problem A R S"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "set (tp_ops.Rw I tp) = to_rules S"
    and accepted: "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "trs_relative_terminates A R S"
proof -
  have "SN_qrel (tp_ops.qreltrs I tp)"
    by (rule check_trs_termination_proof[OF I J accepted])
  then have "SN_rel (rstep (to_rules R)) (rstep (to_rules S))"
    by (simp add: tp_spec.qreltrs_sound[OF I] mode Q strict weak SN_qrel_def)
  then show ?thesis by (rule ordinary_relative_implies_ranked)
qed

theorem trs_relative_checker_NO:
  assumes problem: "relative_problem A R S"
    and extension: "relative_extension_condition A S"
    and I: "tp_spec I" and J: "dpp_spec J"
    and mode: "tp_ops.nfs I tp = False"
    and Q: "tp_ops.Q I tp = []"
    and strict: "set (tp_ops.R I tp) = to_rules R"
    and weak: "set (tp_ops.Rw I tp) = to_rules S"
    and accepted: "isOK (check_reltrs_nontermination_proof I J False i tp prf)"
  shows "\<not> trs_relative_terminates A R S"
proof -
  have "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
    by (rule check_reltrs_nontermination_proof[OF I J accepted])
  then have "\<not> SN_rel (rstep (to_rules R)) (rstep (to_rules S))"
    by (simp add: mode Q strict weak SN_qrel_def)
  then show ?thesis using trs_relative_nonterminates_iff[OF problem extension] by blast
qed

ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms relative_step_iff
    trs_relative_terminates_iff_signature trs_relative_terminates_iff
    trs_relative_checker_YES trs_relative_checker_NO}
    then error "TRS Relative: admitted proof in dependencies" else ()
\<close>
end
