theory RFC_Absolute_Code
  imports RFC_Absolute_Cert "Proof_Checker.Code_CSR_Production"
begin

text \<open>The existing relative checker remains the first route. The additional
  route discharges RFC deletion by absolute termination of the retained rules,
  using the separately proved forward-closure theorem. It does not accept
  assumptions or weaken checking of the input rewrite strategy.\<close>

export_code certify_proof_rfc_absolute certify_proof Certified Unsupported Error Inl Inr version
  nat_of_integer literal.explode
  in Haskell

end
