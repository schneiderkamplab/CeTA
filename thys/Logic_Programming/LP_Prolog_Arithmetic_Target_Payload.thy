theory LP_Prolog_Arithmetic_Target_Payload
 imports LP_Prolog_Observer_Arithmetic_Parameter_Node
begin

lemma lpp_arithmetic_target_payload_parameter:
 fixes rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes represented: "lpc_reinterface project
   ((LPCGoals (LPCUnify actual_output (LPIFun (LPCUser scalar) [])#gs),env)#saved) =
   lpc_return_eval rho ((LPCGoals target_goals,payload)#target_saved)"
 and coordinate: "slot<length payload" "payload!slot=Var parameter_slot"
 and tracked: "lpp_runtime_parameter initial_parameter (project env slot)"
 shows "rho parameter_slot = project env slot \<and>
   lpp_runtime_parameter initial_parameter (rho parameter_slot)"
proof -
 have payload: "project env=lpc_return_env payload rho"
  using represented by (auto simp: lpc_reinterface_def lpc_return_eval_def)
 have same: "rho parameter_slot = project env slot"
  using fun_cong[OF payload, of slot] coordinate by (simp add: lpc_return_env_def)
 show ?thesis using same tracked by simp
qed

ML \<open>
val checked = @{thms lpp_arithmetic_target_payload_parameter};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic target payload" else ();
\<close>
end
