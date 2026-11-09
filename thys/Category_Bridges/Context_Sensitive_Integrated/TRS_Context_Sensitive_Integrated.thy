theory TRS_Context_Sensitive_Integrated
  imports CSR_Global_Checker
begin

text \<open>Every accepted CSR termination family implies unrestricted
termination. The signature-extension proof discharges the rule conditions
inside the relevant checker branches; unused source declarations are allowed.\<close>

theorem trs_context_sensitive_bound_decision:
  assumes problem: "trs_problem A R"
    and rules: "set Rs = to_rules R"
    and accepted: "certify_integrated_cert_problem False
      (FP_TRS_input (Context_Sensitive mu) Rs) Termination (Decision b) certificate = Certified"
  shows "b \<longleftrightarrow> trs_context_sensitive_terminates A (mu_of mu) R"
proof -
  have valid: "funas_trs (to_rules R) \<subseteq> to_signature A"
    by (rule correct_rules[OF problem])
  have restricted: "b \<longleftrightarrow> SN (sig_step (funas_trs (to_rules R)) (csstep (mu_of mu) (to_rules R)))"
    using certify_integrated_cert_problem_sound[OF accepted]
    by (simp add: desired_property_def rules)
  show ?thesis
  proof (cases b)
    case True
    have accepted_true: "certify_integrated_cert_problem False
      (FP_TRS_input (Context_Sensitive mu) Rs) Termination (Decision True) certificate = Certified"
      using accepted True by simp
    have global: "SN (csstep (mu_of mu) (to_rules R))"
      using csr_integrated_global_sound[OF accepted_true] by (simp add: rules)
    have "SN (sig_step (to_signature A) (csstep (mu_of mu) (to_rules R)))"
      by (rule SN_subset[OF global]) (auto simp: sig_step_def)
    then show ?thesis using True trs_context_sensitive_terminates_iff by blast
  next
    case False
    have subset: "sig_step (funas_trs (to_rules R)) (csstep (mu_of mu) (to_rules R))
      \<subseteq> sig_step (to_signature A) (csstep (mu_of mu) (to_rules R))"
      using valid by (auto simp: sig_step_def)
    show ?thesis using SN_subset[OF _ subset] restricted False
      by (auto simp: trs_context_sensitive_terminates_iff)
  qed
qed

corollary trs_context_sensitive_bound_YES:
  assumes "trs_problem A R" "set Rs = to_rules R"
    "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
      Termination (Decision True) certificate = Certified"
  shows "trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_bound_decision[OF assms] by simp

corollary trs_context_sensitive_bound_NO:
  assumes "trs_problem A R" "set Rs = to_rules R"
    "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
      Termination (Decision False) certificate = Certified"
  shows "\<not> trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_bound_decision[OF assms] by simp

theorem trs_context_sensitive_serialized_decision:
  assumes "trs_problem A R" "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (FP_TRS_input (Context_Sensitive mu) Rs, Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> trs_context_sensitive_terminates A (mu_of mu) R"
proof -
  have "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
    Termination (Decision b) certificate = Certified"
    by (rule integrated_serialized_acceptance[OF parsed accepted])
  then show ?thesis by (rule trs_context_sensitive_bound_decision[OF assms(1,2)])
qed

ML \<open>
  val checked = @{thms csr_signature_extension csr_integrated_global_sound trs_context_sensitive_bound_decision
    trs_context_sensitive_bound_YES trs_context_sensitive_bound_NO trs_context_sensitive_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof checked then error "CSR: admitted proof" else ()
  val names = Thm_Deps.all_oracles checked |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("CSR integrated oracle dependencies: " ^ commas names)
\<close>
end
