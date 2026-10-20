theory Higher_Order_Guarded_Code
  imports Higher_Order_Guarded_Schema "Higher_Order_Prefix.Higher_Order_Prefix_Code"
begin

datatype ho_guarded_certificate =
    HOGBase ho_modular_certificate
  | HOGSchema "nat list" "nat list" "nat list" "nat list" nat "nat list"
  | HOGPolynomial "ho_polynomial list" nat ho_guarded_certificate

fun ho_check_guarded_certificate where
  "ho_check_guarded_certificate S R (HOGBase cert)=ho_check_modular S R cert"
| "ho_check_guarded_certificate S R (HOGSchema ranks arities priorities sorts fuel guards)=
    ho_check_guarded_schema (set guards) S R ranks arities priorities sorts fuel"
| "ho_check_guarded_certificate S R (HOGPolynomial ps fuel child)=
    (ho_check_polynomial_removal S ps fuel R \<and>
     ho_check_guarded_certificate S (ho_polynomial_residual S ps fuel R) child)"

theorem ho_check_guarded_certificate_sound:
  "ho_check_guarded_certificate S R cert \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
  by (induction cert arbitrary: R)
    (auto intro: ho_check_modular_sound ho_check_guarded_schema_sound ho_check_polynomial_removal_sound)

export_code ho_check_guarded_certificate HOGBase HOGSchema HOGPolynomial
  ho_check_prefix_schema ho_check_blocked_schema ho_check_lex_semantic_schema ho_check_meta ho_check_meta_removal ho_meta_polynomial_residual ho_check_modular HOMBase HOMFunctional HOMLambda HOMSemantic HOMComponent HOMPolynomial ho_check_functional_access_schema ho_check_component_schema ho_check_lambda_access_schema ho_check_semantic_schema ho_check_call_comparison ho_check_termination ho_check_polynomial_removal ho_polynomial_residual
  ho_check_polynomial_rule_ge ho_check_polynomial_rule_gt ho_polynomial_normalize
  ho_check_application ho_check_loop ho_check_embedding ho_check_rule_pump ho_check_plain_pump
  ho_check_step ho_typeof nat_of_integer
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HRule HBeta HLeft HRight HUnder HHole HCLeft HCRight
  HPVar HPNumber HPAdd HPMultiply HPApply HPAbstract
  HOEmpty HOApplication HOGeneralSchema HOPartialSchema HOPolynomial
  in Haskell module_name Higher_Order_Checker

end
