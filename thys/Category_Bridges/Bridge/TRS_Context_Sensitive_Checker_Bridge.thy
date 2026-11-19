theory TRS_Context_Sensitive_Checker_Bridge
  imports TRS_Context_Sensitive_Equivalence Category_Checker_Base
begin
text \<open>Generic dispatcher nontermination transfers from the rule signature
into any total arity containing the rules. For YES, the concrete integrated
bridge proves signature extension for every accepted CSR proof family.\<close>
theorem trs_context_sensitive_checker_NO:
  fixes I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  assumes problem: "trs_problem A R"
    and rules: "set Rs = to_rules R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and accepted: "isOK (check_cert I J K L False
      (FP_TRS_input (Context_Sensitive mu) Rs) (Termination :: (_,string) property) (Decision False) proof)"
  shows "\<not> trs_context_sensitive_terminates A (from_replacement_map A (mu_of mu)) R"
proof -
  have nontermination: "\<not> SN (sig_step (funas_trs (to_rules R)) (csstep (mu_of mu) (to_rules R)))"
    using category_checker_decision_sound[OF I J K L accepted]
    by (simp add: desired_property_def rules)
  have inclusion: "sig_step (funas_trs (to_rules R)) (csstep (mu_of mu) (to_rules R))
    \<subseteq> sig_step (to_signature A) (csstep (mu_of mu) (to_rules R))"
    using correct_rules[OF problem] by (auto simp: sig_step_def)
  show ?thesis using SN_subset[OF _ inclusion] nontermination
    by (auto simp: trs_context_sensitive_terminates_iff[OF problem])
qed
ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms context_sensitive_step_iff context_sensitive_step_iff_lifted
    trs_context_sensitive_terminates_iff trs_context_sensitive_terminates_iff_lifted
    trs_context_sensitive_checker_NO}
    then error "TRS Context-sensitive: admitted proof in dependencies" else ()
\<close>
end
