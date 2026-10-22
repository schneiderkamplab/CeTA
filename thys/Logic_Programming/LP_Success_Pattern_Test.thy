theory LP_Success_Pattern_Test
  imports LP_Success_Pattern_Check
begin

text \<open>An accumulator transfer is a genuinely nontrivial instance:
  both the input and output grow, while the recursive step moves two
  constructors from the input counter to the accumulator.\<close>

definition sp_s :: "(string,nat) term \<Rightarrow> (string,nat) term" where
  "sp_s t = Fun ''s'' [t]"
definition sp_zero :: "(string,nat) term" where
  "sp_zero = Fun ''0'' []"
definition sp_atom :: "(string,nat) lp_atom" where
  "sp_atom = (''acc'',[Var 0,Var 1,Var 2])"
definition sp_program :: "(string,nat) lp_clause list" where
  "sp_program = [
    ((''acc'',[sp_zero,Var 1,Var 1]),[]),
    ((''acc'',[sp_s (Var 0),Var 1,Var 2]),
      [(''acc'',[Var 0,sp_s (sp_s (Var 1)),Var 2])])]"
definition sp_sig where
  "sp_sig = [(0,sp_s (Var 0)),(2,sp_s (sp_s (Var 2)))]"
definition sp_tau where
  "sp_tau = [(1,sp_s (sp_s (Var 1))),(2,sp_s (sp_s (Var 2)))]"
definition sp_mu where
  "sp_mu = [(0,sp_zero),(2,Var 1)]"
definition sp_nu where
  "sp_nu = [(1,sp_s (sp_s (Var 1))) ]"
definition sp_base where
  "sp_base = [(0,[])]"
definition sp_step where
  "sp_step = [(1,[(2,sp_s (sp_s (Var 2)))])]"

lemma accumulator_success:
  "lp_success_pattern_check sp_program sp_atom sp_sig sp_tau sp_mu sp_nu sp_base sp_step"
  by eval

lemma reject_mutations:
  "\<not>lp_success_pattern_check sp_program sp_atom sp_sig sp_tau sp_mu [] sp_base sp_step \<and>
   \<not>lp_success_pattern_check sp_program sp_atom [] sp_tau sp_mu sp_nu sp_base sp_step \<and>
   \<not>lp_success_pattern_check sp_program sp_atom sp_sig [] sp_mu sp_nu sp_base sp_step \<and>
   \<not>lp_success_pattern_check sp_program sp_atom sp_sig sp_tau [] sp_nu sp_base sp_step \<and>
   \<not>lp_success_pattern_check sp_program sp_atom sp_sig sp_tau sp_mu sp_nu [] sp_step \<and>
   \<not>lp_success_pattern_check sp_program sp_atom sp_sig sp_tau sp_mu sp_nu sp_base []"
  by eval

end
