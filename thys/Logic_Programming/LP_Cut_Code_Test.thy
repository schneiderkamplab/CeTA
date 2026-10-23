theory LP_Cut_Code_Test
imports LP_Cut_Table_XML
begin
declare [[code_timing = true]]
ML \<open>
val _ = Code_Target.produce_code @{context} true
  [@{const_name lpc_check_table}] "Haskell" "CutTableCheck" NONE [];
writeln "CUT_TABLE_CODE_GENERATION_OK";
\<close>
end
