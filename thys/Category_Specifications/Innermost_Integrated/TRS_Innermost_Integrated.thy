theory TRS_Innermost_Integrated
  imports Category_Specification_Bridges.TRS_Innermost_Equivalence
    Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin

text \<open>The category uses explicit False substitution mode, arbitrary rule
pairs, and no weak rules. No normal-form-substitution equivalence premise is needed.\<close>

theorem trs_innermost_integrated_decision:
  assumes problem: "standard_problem A R"
    and rules: "set Rs = to_rules R"
    and accepted: "certify_integrated_cert_problem False
      (Inn_TRS_input (Innermost False) Rs []) Termination (Decision b) certificate = Certified"
  shows "b \<longleftrightarrow> trs_innermost_terminates A R"
  using certify_integrated_cert_problem_sound[OF accepted]
  by (simp add: desired_property_def SN_qrel_def rules
      trs_innermost_terminates_iff[OF problem] irstep_def)

corollary trs_innermost_integrated_YES:
  "standard_problem A R \<Longrightarrow> set Rs = to_rules R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input (Innermost False) Rs [])
     Termination (Decision True) certificate = Certified \<Longrightarrow>
   trs_innermost_terminates A R"
  using trs_innermost_integrated_decision[where b=True] by blast

corollary trs_innermost_integrated_NO:
  "standard_problem A R \<Longrightarrow> set Rs = to_rules R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input (Innermost False) Rs [])
     Termination (Decision False) certificate = Certified \<Longrightarrow>
   \<not> trs_innermost_terminates A R"
  using trs_innermost_integrated_decision[where b=False] by blast

theorem trs_innermost_serialized_decision:
  assumes problem: "standard_problem A R"
    and rules: "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (Inn_TRS_input (Innermost False) Rs [], Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> trs_innermost_terminates A R"
proof -
  have "certify_integrated_cert_problem False (Inn_TRS_input (Innermost False) Rs [])
      Termination (Decision b) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_innermost_integrated_decision[OF problem rules])
qed

ML \<open>
  val checked = @{thms trs_innermost_integrated_decision
    trs_innermost_integrated_YES trs_innermost_integrated_NO trs_innermost_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof checked then error "Innermost: admitted proof" else ()
  val names = Thm_Deps.all_oracles checked |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Innermost integrated oracle dependencies: " ^ commas names)
\<close>
end
