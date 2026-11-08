theory TRS_Equational_Checker_Bridge
  imports Category_Equational_Bridge.TRS_Equational_Equivalence
    Category_Standard_Integrated.TRS_Standard_Integrated
begin
theorem trs_equational_integrated_YES:
  fixes assoc_symbols comm_symbols
  assumes rules: "set Rs=to_rules R" and symbols: "set As=assoc_symbols" "set Cs=comm_symbols"
    and accepted: "certify_integrated_cert_problem False (AC_input Rs As Cs)
      Termination (Decision True) certificate = Certified"
  shows "trs_equational_terminates A R assoc_symbols comm_symbols"
  using certify_integrated_cert_problem_sound[OF accepted]
  by (auto simp: desired_property_def rules symbols intro: equational_termination_transfer)

theorem trs_equational_integrated_NO:
  fixes assoc_symbols comm_symbols
  assumes problem: "equational_problem A R assoc_symbols comm_symbols"
    and rules: "set Rs=to_rules R"
    and accepted: "certify_integrated_cert_problem False (AC_input Rs As Cs)
      Termination (Decision False) (Inl (TRS_Nontermination_Proof p)) = Certified"
  shows "\<not> trs_equational_terminates A R assoc_symbols comm_symbols"
proof -
  have dispatch:
    "certify_integrated_cert_problem False (AC_input Rs As Cs)
      Termination (Decision False) (Inl (TRS_Nontermination_Proof p)) =
     certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
      Termination (Decision False) (Inl (TRS_Nontermination_Proof p))"
    by (simp add: certify_integrated_cert_problem_def certify_cert_problem_rfc_absolute_def
      certify_cert_problem_def check_cert_def Let_def default_nfs_flag_def check_def
      check_cert_rfc_absolute.simps)
  have ordinary: "certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
      Termination (Decision False) (Inl (TRS_Nontermination_Proof p)) = Certified"
    using accepted by (simp only: dispatch)
  have "\<not> trs_standard_terminates A R"
    by (rule trs_standard_integrated_NO[OF _ rules ordinary])
      (use problem in \<open>simp add: equational_problem_def\<close>)
  then show ?thesis by (rule ordinary_nontermination_equational)
qed

theorem trs_equational_serialized_YES:
  fixes assoc_symbols comm_symbols
  assumes rules: "set Rs = to_rules R"
    and symbols: "set As = assoc_symbols" "set Cs = comm_symbols"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (AC_input Rs As Cs, Termination, Decision True, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "trs_equational_terminates A R assoc_symbols comm_symbols"
proof -
  have "certify_integrated_cert_problem False (AC_input Rs As Cs) Termination
      (Decision True) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_equational_integrated_YES[OF rules symbols])
qed

theorem trs_equational_serialized_NO:
  fixes assoc_symbols comm_symbols
  assumes problem: "equational_problem A R assoc_symbols comm_symbols"
    and rules: "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (AC_input Rs As Cs, Termination, Decision False, Inl (TRS_Nontermination_Proof p))"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "\<not> trs_equational_terminates A R assoc_symbols comm_symbols"
proof -
  have "certify_integrated_cert_problem False (AC_input Rs As Cs) Termination
      (Decision False) (Inl (TRS_Nontermination_Proof p)) = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_equational_integrated_NO[OF problem rules])
qed

ML \<open>
  val results = @{thms trs_equational_integrated_YES trs_equational_integrated_NO
    trs_equational_serialized_YES trs_equational_serialized_NO}
  val _ = if Thm_Deps.has_skip_proof results then error "Equational: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Equational checker oracle dependencies: " ^ commas names)
\<close>
end
