theory Higher_Order_Lambda_Access_Code
  imports Higher_Order_Lambda_Access_Schema "Higher_Order_Checker.Higher_Order_Code"
begin

export_code ho_check_lambda_access_schema ho_check_semantic_schema ho_check_call_comparison ho_check_termination ho_check_polynomial_removal ho_polynomial_residual
  ho_check_polynomial_rule_ge ho_check_polynomial_rule_gt ho_polynomial_normalize
  ho_check_application ho_check_loop ho_check_embedding ho_check_rule_pump ho_check_plain_pump
  ho_check_step ho_typeof nat_of_integer
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HRule HBeta HLeft HRight HUnder HHole HCLeft HCRight
  HPVar HPNumber HPAdd HPMultiply HPApply HPAbstract
  HOEmpty HOApplication HOGeneralSchema HOPartialSchema HOPolynomial
  in Haskell module_name Higher_Order_Checker

end
