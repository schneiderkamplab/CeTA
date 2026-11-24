theory Relative_ADP_Composition_Code
  imports Relative_ADP_Composition.Relative_ADP_Composition_Parser
    Certificate_Performance_CPF_Export.Certificate_Performance_CPF_Export
begin

text \<open>Keep the existing CPF export and its verified performance refinements.
The additional entry point accepts closed ADP compositions as well as all
certificate forms handled by the integrated entry point.\<close>

export_code certify_proof_integrated certify_proof_composed
  Certified Unsupported Error Inl Inr nat_of_integer literal.explode
  in Haskell module_name Ceta_Relative

end
