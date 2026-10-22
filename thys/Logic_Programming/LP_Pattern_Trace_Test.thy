theory LP_Pattern_Trace_Test
  imports LP_Pattern_Trace LP_Success_Pattern_Test
begin

definition pt_atom :: "(string,nat) lp_atom" where
  "pt_atom = (''f'',[Var 0,Var 1])"
definition pt_program :: "(string,nat) lp_clause list" where
  "pt_program = [
    (pt_atom,[(''nat'',[Var 0]),(''nat'',[Var 1]),(''f'',[sp_s (Var 0),sp_s (Var 1)])]),
    ((''nat'',[sp_zero]),[]),
    ((''nat'',[sp_s (Var 0)]),[(''nat'',[Var 0])])]"
definition pt_sig :: "(string,nat) substL" where
  "pt_sig = [(0,sp_s (Var 0)),(1,sp_s (Var 1))]"
definition pt_mu :: "(string,nat) substL" where
  "pt_mu = [(0,sp_zero),(1,sp_zero)]"
definition pt_steps :: "(string,nat) lp_pattern_step list" where
  "pt_steps = [
    LPPatternSuccess [] [] [(1,[])] [(2,[])],
    LPPatternSuccess [] [] [(1,[])] [(2,[(0,Var 1)])]]"

lemma two_successful_prefixes:
  "lp_pattern_loop_check pt_program ''f'' 2 [0,1] pt_atom pt_sig pt_mu [(0,[])] pt_steps"
  by eval

lemma reject_root_mutations:
  "\<not>lp_pattern_loop_check pt_program ''other'' 2 [0,1] pt_atom pt_sig pt_mu [(0,[])] pt_steps \<and>
   \<not>lp_pattern_loop_check pt_program ''f'' 1 [0,1] pt_atom pt_sig pt_mu [(0,[])] pt_steps \<and>
   \<not>lp_pattern_loop_check pt_program ''f'' 2 [2] pt_atom pt_sig pt_mu [(0,[])] pt_steps \<and>
   \<not>lp_pattern_loop_check pt_program ''f'' 2 [0,1] pt_atom pt_sig [] [(0,[])] pt_steps \<and>
   \<not>lp_pattern_loop_check pt_program ''f'' 2 [0,1] pt_atom pt_sig pt_mu [] pt_steps \<and>
   \<not>lp_pattern_loop_check pt_program ''f'' 2 [0,1] pt_atom pt_sig pt_mu [(0,[])] (tl pt_steps)"
  by eval

end
