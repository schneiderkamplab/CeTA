theory TRS_Conditional_Checker_Bridge
  imports Category_Conditional_Bridge.TRS_Conditional_Operational_Transfer
    Relative_ADP_Ceta_Dev.Relative_ADP_Ceta Conditional_Ordinary.Conditional_Erasure
begin
text \<open>The ordinary and operational conclusions remain distinct even when
the same quasi-reductive certificate can establish both. No checker module or
certificate assumption is supplied as an unproved contract.\<close>
theorem trs_conditional_integrated_ordinary_YES:
  assumes rules: "set Rs = to_conditional_rules R"
    and accepted: "certify_integrated_cert_problem False (CTRS_input Rs)
      Termination (Decision True) certificate = Certified"
  shows "trs_conditional_terminates A R"
proof -
  have "SN (Conditional_Rewriting.cstep (to_conditional_rules R))"
    using certify_integrated_cert_problem_sound[OF accepted]
    by (simp add: desired_property_def rules)
  then show ?thesis by (rule conditional_ordinary_termination_transfer)
qed

lemma conditional_integrated_quasi_acceptance:
  assumes "certify_integrated_cert_problem False (CTRS_input Rs)
    Termination (Decision True) (Inl (Quasi_Reductive_Proof p)) = Certified"
  shows "isOK (check_quasi_reductive_proof False (showsl_lit (STR ''1''))
    tp_impl dpp_impl Rs p)"
  using assms
  by (cases "check_quasi_reductive_proof False (showsl_lit (STR ''1'')) tp_impl dpp_impl Rs p";
    simp_all add: certify_integrated_cert_problem_def certify_cert_problem_rfc_absolute_def
      certify_cert_problem_def check_cert_def Let_def
      del: check_quasi_reductive_proof.simps split: sum.splits if_splits)

theorem trs_conditional_integrated_operational_YES:
  assumes rules: "set Rs = to_conditional_rules R"
    and accepted: "certify_integrated_cert_problem False (CTRS_input Rs)
      Termination (Decision True) (Inl (Quasi_Reductive_Proof p)) = Certified"
  shows "trs_conditional_operationally_terminates A R"
proof -
  have "quasi_reductive (set Rs)"
    by (rule check_quasi_reductive_proof_sound[OF tp_rbt_impl dpp_rbt_impl
      conditional_integrated_quasi_acceptance[OF accepted]])
  then have "quasi_decreasing (to_conditional_rules R)"
    using quasi_reductive_quasi_decreasing by (simp add: rules)
  then show ?thesis by (rule conditional_operational_termination_transfer)
qed

theorem trs_conditional_erasure_ordinary_YES:
  assumes rules: "set Rs = to_conditional_rules R"
    and accepted: "check_conditional_erasure tp_impl dpp_impl Rs p"
  shows "trs_conditional_terminates A R"
  using check_conditional_erasure_sound[OF tp_rbt_impl dpp_rbt_impl accepted]
  by (simp add: rules conditional_ordinary_termination_transfer)

theorem trs_conditional_serialized_operational_YES:
  assumes rules: "set Rs = to_conditional_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (CTRS_input Rs, Termination, Decision True, Inl (Quasi_Reductive_Proof p))"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "trs_conditional_operationally_terminates A R"
proof -
  have "certify_integrated_cert_problem False (CTRS_input Rs) Termination
      (Decision True) (Inl (Quasi_Reductive_Proof p)) = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_conditional_integrated_operational_YES[OF rules])
qed

theorem trs_conditional_serialized_ordinary_YES:
  assumes rules: "set Rs = to_conditional_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (CTRS_input Rs, Termination, Decision True, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "trs_conditional_terminates A R"
proof -
  have "certify_integrated_cert_problem False (CTRS_input Rs) Termination
      (Decision True) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_conditional_integrated_ordinary_YES[OF rules])
qed

ML \<open>
  val results = @{thms conditional_success_embedding operational_implies_ordinary
    conditional_operational_termination_transfer trs_conditional_integrated_ordinary_YES
    trs_conditional_integrated_operational_YES trs_conditional_erasure_ordinary_YES
    trs_conditional_serialized_ordinary_YES trs_conditional_serialized_operational_YES}
  val _ = if Thm_Deps.has_skip_proof results then error "Conditional: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Conditional YES oracle dependencies: " ^ commas names)
\<close>
end
