theory Usable_Rules_CPF_Export
 imports "Relative_ADP_Ceta_Dev.Relative_ADP_Code_Haskell" "Usable_Rules_Membership.Usable_Rules_Membership"
begin
export_code certify_proof_integrated Certified Unsupported Error Inl Inr
  nat_of_integer literal.explode
  in Haskell module_name Ceta_Relative


end
