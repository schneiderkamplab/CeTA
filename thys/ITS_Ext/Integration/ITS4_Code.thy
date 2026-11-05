theory ITS4_Code
  imports ITS4_Parser
begin

export_code check_its4_string Inl Inr char_of_integer integer_of_char in Haskell module_name ITS_Checker
end
