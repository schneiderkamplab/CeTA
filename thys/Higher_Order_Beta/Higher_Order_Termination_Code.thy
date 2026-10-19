theory Higher_Order_Termination_Code
  imports Higher_Order_Application "Higher_Order_Checker.Higher_Order_Code"
begin

export_code ho_check_application ho_check_loop ho_check_embedding ho_check_rule_pump ho_check_plain_pump
  ho_check_step ho_typeof nat_of_integer
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HRule HBeta HLeft HRight HUnder HHole HCLeft HCRight
  in Haskell module_name Higher_Order_Checker

end
