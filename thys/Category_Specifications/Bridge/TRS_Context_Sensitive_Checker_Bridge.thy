theory TRS_Context_Sensitive_Checker_Bridge
  imports TRS_Context_Sensitive_Equivalence Category_Checker_Base
begin
text \<open>These general-dispatcher corollaries cover the rule signature. They do not
restrict the canonical category to that signature. The concrete integrated
bridge additionally covers larger signatures for NO and direct CSR YES proofs.\<close>
theorem trs_context_sensitive_checker_decision:
  fixes I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  assumes problem: "standard_problem A R"
    and signature: "to_signature A = funas_trs (to_rules R)"
    and rules: "set Rs = to_rules R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and accepted: "isOK (check_cert I J K L False
      (FP_TRS_input (Context_Sensitive mu) Rs) (Termination :: (_,string) property) (Decision b) proof)"
  shows "b \<longleftrightarrow> trs_context_sensitive_terminates A (mu_of mu) R"
  using category_checker_decision_sound[OF I J K L accepted]
  by (simp add: desired_property_def trs_context_sensitive_terminates_iff signature rules)
corollary trs_context_sensitive_checker_YES:
  fixes I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  assumes problem: "standard_problem A R"
    and signature: "to_signature A = funas_trs (to_rules R)"
    and rules: "set Rs = to_rules R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and accepted: "isOK (check_cert I J K L False
      (FP_TRS_input (Context_Sensitive mu) Rs) (Termination :: (_,string) property) (Decision True) proof)"
  shows "trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_checker_decision[OF problem signature rules I J K L accepted] by simp
corollary trs_context_sensitive_checker_NO:
  fixes I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  assumes problem: "standard_problem A R"
    and signature: "to_signature A = funas_trs (to_rules R)"
    and rules: "set Rs = to_rules R"
    and I: "tp_spec I" and J: "dpp_spec J"
    and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and accepted: "isOK (check_cert I J K L False
      (FP_TRS_input (Context_Sensitive mu) Rs) (Termination :: (_,string) property) (Decision False) proof)"
  shows "\<not> trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_checker_decision[OF problem signature rules I J K L accepted] by simp
ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms context_sensitive_step_iff
    trs_context_sensitive_terminates_iff trs_context_sensitive_checker_YES
    trs_context_sensitive_checker_NO}
    then error "TRS Context-sensitive: admitted proof in dependencies" else ()
\<close>
end
