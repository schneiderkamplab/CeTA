theory Category_Checker_Base
  imports Proof_Checker.Proof_Checker
begin
text \<open>The semantic certificate checker is used with assumptions disabled.
This lemma covers the concrete input/property/answer triple; it makes no claim
about parsing a serialized certificate or a compiled executable.\<close>
lemma category_checker_decision_sound:
  fixes I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and accepted: "isOK (check_cert I J K L False input (Termination :: (_,string) property) (Decision b) proof)"
  shows "desired_property input (Termination :: (_,string) property) (Decision b)"
    apply (rule check_cert_with_assms_sound)
       apply (rule I)
      apply (rule J)
     apply (rule K)
    apply (rule L)
   apply (rule accepted)
  by simp
end
