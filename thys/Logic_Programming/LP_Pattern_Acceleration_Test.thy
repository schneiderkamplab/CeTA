theory LP_Pattern_Acceleration_Test
  imports LP_Pattern_Acceleration
begin

definition ac_z :: "(nat,nat) term" where "ac_z=Fun 0 []"
definition ac_s :: "(nat,nat) term \<Rightarrow> (nat,nat) term" where "ac_s t=Fun 1 [t]"
definition ac_sig where "ac_sig=[(0,ac_s (Var 0)),(1,ac_s (ac_s (Var 1)))]"
definition ac_mu where "ac_mu=[(0,ac_s ac_z),(1,ac_s (ac_s ac_z))]"
definition ac_ls where "ac_ls=[(2,ac_s (Var 2))]"
definition ac_lm where "ac_lm=[(2,ac_s ac_z)]"
definition ac_theta where "ac_theta=[(0,ac_z),(1,ac_z),(2,Var 0)]"
definition ac_eta where "ac_eta=[(0,ac_z),(1,ac_z),(2,ac_s ac_z)]"
definition ac_delta where "ac_delta=[(0,ac_z),(1,ac_z),(2,Var 1)]"

lemma doubling_transport:
  "lp_pattern_acceleration_check (3::nat,[Var 0]) (3,[Var 1]) ac_sig ac_mu
    (3,[Var 2]) ac_ls ac_lm ac_theta ac_eta ac_delta 2 1"
  by eval

lemma rejects_wrong_rate_offset_embedding_and_closing:
  "\<not>lp_pattern_acceleration_check (3::nat,[Var 0]) (3,[Var 1]) ac_sig ac_mu
    (3,[Var 2]) ac_ls ac_lm ac_theta ac_eta ac_delta 1 1 \<and>
   \<not>lp_pattern_acceleration_check (3::nat,[Var 0]) (3,[Var 1]) ac_sig ac_mu
    (3,[Var 2]) ac_ls ac_lm ac_theta ac_eta ac_delta 2 0 \<and>
   \<not>lp_pattern_acceleration_check (3::nat,[Var 0]) (3,[Var 1]) ac_sig ac_mu
    (3,[Var 2]) ac_ls ac_lm [] ac_eta ac_delta 2 1 \<and>
   \<not>lp_pattern_acceleration_check (3::nat,[Var 0]) (3,[Var 1]) ac_sig []
    (3,[Var 2]) ac_ls ac_lm ac_theta ac_eta ac_delta 2 1"
  by eval

end
