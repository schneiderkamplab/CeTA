theory LP_Prolog_Finite_Direct_Control_Test
 imports LP_Prolog_Finite_Direct_Program LP_Prolog_Finite_Direct_Test
begin

lemma distinct_variable_head_accepted:
 "lpp_check_direct_head (Fun (LPCUser ''renamed'') [Var ''x'',Var ''y''])"
 by simp

lemma repeated_head_variable_rejected:
 "\<not>lpp_check_direct_head (Fun (LPCUser ''renamed'') [Var ''x'',Var ''x''])"
 by simp

lemma constructor_head_rejected:
 "\<not>lpp_check_direct_head (Fun (LPCUser ''renamed'') [Fun (LPCUser ''f'') [Var ''x'']])"
 by simp

lemma omitted_signature_rejected:
 "\<not>lpp_check_finite_direct_program
   [(Fun (LPCUser ''renamed'') [Var ''x''], [LPCAtom (Fun (LPCUser ''2:is'') [Var ''x'',Var ''e''])])] []"
 by (simp add: lpp_check_finite_direct_program_def lpp_static_program_def)

lemma arithmetic_program_accepted:
 "lpp_check_finite_direct_program
   [(Fun (LPCUser ''renamed'') [Var ''x''], [LPCAtom (Fun (LPCUser ''2:is'') [Var ''x'',Var ''e''])])]
   [(''2:is'',2)]"
 by (simp add: lpp_check_finite_direct_program_def lpp_static_program_def lpp_direct_arithmetic_name_def)

lemma unsupported_builtin_signature_rejected:
 "\<not>lpp_check_finite_direct_program ([]::(string,string) lp_cut_program) [(''2:length'',2)]"
 by eval

end
