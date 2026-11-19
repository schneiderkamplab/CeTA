theory LP_Prolog_Arithmetic_Target_Parameter
 imports LP_Prolog_Observer_Arithmetic_Node LP_Prolog_Runtime_Parameter
begin

text \<open>The represented normalization target itself identifies the scalar
coordinate. This does not authenticate the following equality or boundary.\<close>

lemma lpp_arithmetic_target_parameter:
 fixes rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes represented: "lpc_reinterface project
   ((LPCGoals (LPCUnify actual_output (LPIFun (LPCUser scalar) [])#gs),env)#saved) =
   lpc_return_eval rho ((LPCGoals (LPCUnify (Var output_slot) (Var scalar_slot)#target_rest),payload)#target_saved)"
 and ground: "vars_term initial_parameter = {}"
 shows "rho output_slot=actual_output \<and> rho scalar_slot=LPIFun (LPCUser scalar) [] \<and>
   lpp_runtime_parameter initial_parameter (rho scalar_slot)"
proof -
 have coordinates: "rho output_slot=actual_output" "rho scalar_slot=LPIFun (LPCUser scalar) []"
  using represented by (auto simp: lpc_reinterface_def lpc_return_eval_def)
 have tracked: "lpp_runtime_parameter initial_parameter (LPIFun (LPCUser scalar) [])"
  using ground by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)
 show ?thesis using coordinates tracked by simp
qed

ML \<open>
val checked = @{thms lpp_arithmetic_target_parameter};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic target parameter" else ();
\<close>
end
