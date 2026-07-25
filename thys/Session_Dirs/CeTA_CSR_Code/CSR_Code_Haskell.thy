(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Code_Haskell
  imports
    CeTA_CSR_Proofs.CSR_Improved_CSDP_Checker
    "Code.Code_Haskell"
begin

export_code certify_proof_csr Certified Unsupported Error Inl Inr version
  nat_of_integer
  literal.explode
  in Haskell

end
