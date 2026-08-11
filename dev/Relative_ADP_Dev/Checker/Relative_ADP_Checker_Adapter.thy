theory Relative_ADP_Checker_Adapter
  imports
    Relative_ADP_Origin_Dev.Relative_ADP_Origin
begin

datatype relative_adp_checker_error = Relative_ADP_Unsupported

definition check_relative_adp_placeholder :: "relative_adp_checker_error check" where
  "check_relative_adp_placeholder = error Relative_ADP_Unsupported"

end
