theory Relative_ADP_Code_Haskell
  imports
    Relative_ADP_Ceta
    Proof_Checker.Ceta
begin

export_code certify_proof_integrated Certified Unsupported Error Inl Inr
  nat_of_integer literal.explode
  in Haskell module_name Ceta_Relative

end
