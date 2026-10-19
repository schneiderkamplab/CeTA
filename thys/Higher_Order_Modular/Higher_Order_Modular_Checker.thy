theory Higher_Order_Modular_Checker
  imports "Higher_Order_Functional_Access.Higher_Order_Functional_Access_Schema"
begin

datatype ho_modular_certificate = HOMBase ho_termination_certificate
  | HOMFunctional "nat list" "nat list" "nat list" "nat list" nat
  | HOMLambda "nat list" "nat list" "nat list" "nat list" nat
  | HOMSemantic "ho_polynomial list" "ho_polynomial list" nat "nat list" "nat list" "nat list" "nat list" nat
  | HOMComponent "ho_polynomial list list" "ho_polynomial list list" nat "nat list" "nat list" "nat list" "nat list" nat
  | HOMPolynomial "ho_polynomial list" nat ho_modular_certificate

fun ho_check_modular where
  "ho_check_modular S R (HOMBase cert)=ho_check_termination S R cert"
| "ho_check_modular S R (HOMFunctional ranks arities priorities sorts fuel)=ho_check_functional_access_schema S R ranks arities priorities sorts fuel"
| "ho_check_modular S R (HOMLambda ranks arities priorities sorts fuel)=ho_check_lambda_access_schema S R ranks arities priorities sorts fuel"
| "ho_check_modular S R (HOMSemantic ps ms ofuel ranks arities priorities sorts fuel)=ho_check_semantic_schema S R ps ms ofuel ranks arities priorities sorts fuel"
| "ho_check_modular S R (HOMComponent ps ms ofuel ranks arities priorities sorts fuel)=ho_check_component_schema S R ps ms ofuel ranks arities priorities sorts fuel"
| "ho_check_modular S R (HOMPolynomial ps fuel child)=(ho_check_polynomial_removal S ps fuel R \<and>
    ho_check_modular S (ho_polynomial_residual S ps fuel R) child)"

theorem ho_check_modular_sound:
  "ho_check_modular S R cert \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
  by (induction cert arbitrary: R)
    (auto intro: ho_check_termination_sound ho_check_functional_access_schema_sound
      ho_check_lambda_access_schema_sound ho_check_semantic_schema_sound
      ho_check_component_schema_sound ho_check_polynomial_removal_sound)

end
