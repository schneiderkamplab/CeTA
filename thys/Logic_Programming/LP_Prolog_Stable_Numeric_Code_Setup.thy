theory LP_Prolog_Stable_Numeric_Code_Setup
  imports LP_Prolog_Stable_Numeric_Rows LP_Prolog_Numeric_Code_Setup
begin

derive ccompare lpp_stable_numeric_key
derive (eq) ceq lpp_stable_numeric_key
derive (rbt) set_impl lpp_stable_numeric_key
derive (no) cenum lpp_stable_numeric_key

end
