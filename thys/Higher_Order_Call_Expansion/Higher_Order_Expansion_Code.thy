theory Higher_Order_Expansion_Code
  imports Higher_Order_Expansion_Schema
begin

definition ho_check_expansion_input where
  "ho_check_expansion_input S R ds efuel ps ms ofuel ranks arities priorities sorts fuel=
    ho_check_expansion_schema S R (\<lambda>c. if c<length ds then ds!c else None)
      efuel ps ms ofuel ranks arities priorities sorts fuel"

theorem ho_check_expansion_input_sound:
  "ho_check_expansion_input S R ds efuel ps ms ofuel ranks arities priorities sorts fuel
    \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
  unfolding ho_check_expansion_input_def by (rule ho_check_expansion_schema_sound)

definition ho_expansion_diagnostics where
  "ho_expansion_diagnostics S R ds efuel ps ms ofuel ranks arities priorities sorts fuel=
    (let defs=(\<lambda>c. if c<length ds then ds!c else None);
         rank=(\<lambda>b. if b<length sorts then sorts!b else 0)
     in [ho_check_polynomial_signature S ps, ho_check_polynomial_signature S ms] @
       map (\<lambda>(G,l,r). ho_check_weak_polynomial_rule S ps ofuel G l r) R @
       map (ho_check_expansion_schema_rule S R (ho_expansion_sorts S R) defs efuel rank
         ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel) R)"

export_code ho_check_expansion_input ho_expansion_diagnostics ho_check_guarded_certificate HOGBase HOGSchema HOGPolynomial
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

