theory Category_Integrated_Base
  imports Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin
text \<open>Serialized acceptance yields semantic checker acceptance of precisely
the parser's input, property, answer and certificate, with assumptions disabled.
This common fact does not prove correspondence with an external source parser.\<close>
lemma integrated_serialized_acceptance:
  assumes parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (parsed_input, parsed_property, parsed_answer, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "certify_integrated_cert_problem False parsed_input parsed_property parsed_answer certificate = Certified"
  using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
end
