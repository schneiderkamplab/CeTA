theory TRS_Standard_Serialized
  imports TRS_Standard_Integrated
begin

text \<open>The parser correspondence premise names the exact result of the
production parser, with no external input/property/answer overrides. It remains
a premise until a verified ARI/CPF correspondence implementation is available.\<close>
theorem trs_standard_serialized_decision:
  assumes problem: "standard_problem A R"
    and rules: "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (Inn_TRS_input No_Strategy Rs [], Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> trs_standard_terminates A R"
proof -
  have "certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
      Termination (Decision b) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_standard_integrated_decision[OF problem rules])
qed

ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms trs_standard_serialized_decision}
    then error "TRS Standard serialized bridge: admitted proof" else ()
  val names = Thm_Deps.all_oracles @{thms trs_standard_serialized_decision}
    |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Standard integrated oracle dependencies: " ^ commas names)
\<close>
end
