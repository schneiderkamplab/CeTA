theory LP_Prolog_Separation_Check_Code
 imports LP_Prolog_Separation_Table_Check LP_Prolog_Separation_Head_Tests
begin

text \<open>Compile the local table predicate independently of the production
checker export. This checks executability, not source certification or promotion.\<close>

ML \<open>
val (separation_check_modules, _) = Code_Target.produce_code @{context} true
  [@{const_name lpp_check_separation_control}] "SML" "Prolog_Separation_Check" NONE [];
\<close>

end
