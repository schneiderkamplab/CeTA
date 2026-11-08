theory TRS_Context_Sensitive_Integrated
  imports Category_Specification_Bridges.TRS_Context_Sensitive_Equivalence
    Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin

text \<open>The general checker proves termination on the rule signature. A
negative answer transfers to every signature containing the rules. For positive
answers on a larger signature, the direct CSR proof language has a stronger,
unrestricted soundness theorem. Other proof languages require exact signatures.\<close>

definition csr_direct_certificate where
  "csr_direct_certificate certificate \<longleftrightarrow>
    (\<exists>p. certificate = Inl (CSR_Termination_Proof (Existing_CSR_Proof (Direct_CSR_Proof p))))"

definition csr_signature_guard where
  "csr_signature_guard A R b certificate \<longleftrightarrow>
    (b \<longrightarrow> to_signature A = funas_trs (to_rules R) \<or> csr_direct_certificate certificate)"

lemma csr_direct_integrated_sound:
  assumes direct: "csr_direct_certificate certificate"
    and accepted: "certify_integrated_cert_problem False
      (FP_TRS_input (Context_Sensitive mu) Rs) Termination (Decision True) certificate = Certified"
  shows "SN (csstep (mu_of mu) (set Rs))"
proof -
  obtain p where cert: "certificate = Inl (CSR_Termination_Proof (Existing_CSR_Proof (Direct_CSR_Proof p)))"
    using direct unfolding csr_direct_certificate_def by blast
  have checked: "isOK (check_csr_termination_proof_min tp_impl dpp_impl False
    (showsl_lit (STR ''1'')) mu Rs p)"
    using accepted unfolding cert certify_integrated_cert_problem_def
      certify_cert_problem_rfc_absolute_def certify_cert_problem_def Let_def
    by (auto simp: check_cert_def split: sum.splits if_splits)
  show ?thesis
    by (rule check_csr_termination_proof_min_sound[OF tp_rbt_impl dpp_rbt_impl checked])
qed

theorem trs_context_sensitive_bound_decision:
  assumes problem: "standard_problem A R"
    and rules: "set Rs = to_rules R"
    and guard: "csr_signature_guard A R b certificate"
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
    note b_true = True
    have "SN (sig_step (to_signature A) (csstep (mu_of mu) (to_rules R)))"
    proof (cases "to_signature A = funas_trs (to_rules R)")
      case True
      then show ?thesis using restricted b_true by simp
    next
      case False
      have direct: "csr_direct_certificate certificate"
        using guard b_true False by (simp add: csr_signature_guard_def)
      have accepted_true: "certify_integrated_cert_problem False
        (FP_TRS_input (Context_Sensitive mu) Rs) Termination (Decision True) certificate = Certified"
        using accepted b_true by simp
      have global: "SN (csstep (mu_of mu) (to_rules R))"
        using csr_direct_integrated_sound[OF direct accepted_true] by (simp add: rules)
      show ?thesis by (rule SN_subset[OF global]) (auto simp: sig_step_def)
    qed
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
  assumes "standard_problem A R" "set Rs = to_rules R"
    "csr_signature_guard A R True certificate"
    "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
      Termination (Decision True) certificate = Certified"
  shows "trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_bound_decision[OF assms] by simp

corollary trs_context_sensitive_bound_NO:
  assumes "standard_problem A R" "set Rs = to_rules R"
    "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
      Termination (Decision False) certificate = Certified"
  shows "\<not> trs_context_sensitive_terminates A (mu_of mu) R"
  using trs_context_sensitive_bound_decision[OF assms(1,2) _ assms(3)]
  by (simp add: csr_signature_guard_def)

theorem trs_context_sensitive_serialized_decision:
  assumes "standard_problem A R" "set Rs = to_rules R"
    "csr_signature_guard A R b certificate"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (FP_TRS_input (Context_Sensitive mu) Rs, Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> trs_context_sensitive_terminates A (mu_of mu) R"
proof -
  have "certify_integrated_cert_problem False (FP_TRS_input (Context_Sensitive mu) Rs)
    Termination (Decision b) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_context_sensitive_bound_decision[OF assms(1-3)])
qed

ML \<open>
  val checked = @{thms csr_direct_integrated_sound trs_context_sensitive_bound_decision
    trs_context_sensitive_bound_YES trs_context_sensitive_bound_NO trs_context_sensitive_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof checked then error "CSR: admitted proof" else ()
  val names = Thm_Deps.all_oracles checked |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("CSR integrated oracle dependencies: " ^ commas names)
\<close>
end
