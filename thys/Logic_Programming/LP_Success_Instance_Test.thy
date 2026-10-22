theory LP_Success_Instance_Test
  imports LP_Success_Instance LP_Success_Pattern_Test
begin

definition si_program :: "(string,nat) lp_clause list" where
  "si_program = [
    ((''transfer'',[sp_zero,Var 1]),[]),
    ((''transfer'',[sp_s (Var 0),Var 1]),[(''transfer'',[Var 0,sp_s (Var 1)])])]"
definition si_call :: "(string,nat) lp_atom" where
  "si_call = (''transfer'',[Var 0,Var 0])"
definition si_general :: "(string,nat) lp_atom" where
  "si_general = (''transfer'',[Var 1,Var 2])"
definition si_sig :: "(string,nat) substL" where "si_sig = [(0,sp_s (Var 0))]"
definition si_local_sig :: "(string,nat) substL" where
  "si_local_sig = si_sig @ [(1,sp_s (Var 1)),(2,sp_s (Var 2))]"
definition si_mu :: "(string,nat) substL" where "si_mu = [(0,sp_zero)]"
definition si_local_mu :: "(string,nat) substL" where "si_local_mu = [(1,sp_zero)]"
definition si_theta :: "(string,nat) substL" where "si_theta = [(1,Var 0),(2,Var 0)]"
definition si_eta :: "(string,nat) substL" where "si_eta = [(0,sp_zero),(2,sp_zero)]"
definition si_tau :: "(string,nat) substL" where "si_tau = [(2,sp_s (sp_s (Var 2)))]"
definition si_base :: "(nat \<times> (string,nat) substL) list" where "si_base = [(0,[(1,Var 2)])]"
definition si_step :: "(nat \<times> (string,nat) substL) list" where
  "si_step = [(1,[(0,Var 1),(1,sp_s (Var 2))])]"

lemma independent_accumulator_instantiated_to_shared_call:
  "lp_success_instance_check si_program si_call si_sig si_mu si_general si_local_sig
    si_local_mu si_theta si_eta si_tau si_tau si_base si_step"
  by eval

lemma reject_transport_mutations:
  "\<not>lp_success_instance_check si_program si_call si_sig si_mu si_general si_local_sig
      si_local_mu [] si_eta si_tau si_tau si_base si_step \<and>
   \<not>lp_success_instance_check si_program si_call si_sig si_mu si_general si_sig
      si_local_mu si_theta si_eta si_tau si_tau si_base si_step \<and>
   \<not>lp_success_instance_check si_program si_call si_sig si_mu si_general si_local_sig
      si_local_mu si_theta [] si_tau si_tau si_base si_step \<and>
   \<not>lp_success_instance_check si_program si_call si_sig si_mu si_general si_local_sig
      si_local_mu si_theta si_eta [] si_tau si_base si_step"
  by eval

end
