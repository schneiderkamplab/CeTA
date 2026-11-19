theory LP_Prolog_Recursive_Partial_Prefix
 imports LP_Prolog_Split_Prefix_Partial_Entry
begin

text \<open>The actual cons MGU and both coordinate checks establish prefix entry.
No recursive-entry invariant is supplied as a premise. This result does not
assert preservation across the helper call.\<close>

lemma lpp_recursive_partial_prefix_initial:
 fixes k :: nat
 and helper_env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and hp q :: "string lp_cut_symbol"
 and eta sigma rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_recursive_entry_coordinates
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs l x y n m fresh_variable
   input_slot parameter_slot helper_slot tail_slot caller_slot bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs sigma rho"
 and spine: "lpp_list_length (lp_ieval input_term eta) spine_length"
 and finite_call: "lpp_finite_term (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_variable)"
 and prefix: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 defines target_env: "nu \<equiv> (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))"
 shows "\<exists>xs caller_shape.
   lpp_runtime_structure ((lpc_return_env payload nu) ti) (lpp_structural_argument_list xs) \<and>
   lpp_runtime_structure ((lpc_return_env payload nu) ci) caller_shape \<and>
   lpp_finite_term ((lpc_return_env payload nu) ci) \<and>
   (\<exists>v. (lpc_return_env payload nu) hi=LPIVar v) \<and>
   (\<exists>n. lpp_list_length ((lpc_return_env payload nu) ti) n) \<and>
   set2_lp_iterm ((lpc_return_env payload nu) hi) \<inter> (set2_lp_iterm ((lpc_return_env payload nu) ti) \<union> set2_lp_iterm ((lpc_return_env payload nu) ci))={} \<and>
   lpp_observer_invariant A [(ti,lpp_structural_argument_list xs),(ci,caller_shape)] [LPCAtom (Fun q [Var ti,Var hi,Var ci])]
    [(LPCGoals [LPCAtom (LPIFun hp [nu input_slot,nu parameter_slot,nu helper_slot])],
      case_sum helper_env (lpc_return_env payload nu))]"
proof -
 have entry: "lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot nu"
  using lpp_checked_recursive_partial_entry[OF checked mgu spine finite_call tracked, of k]
  by (simp add: target_env)
 show ?thesis
  by (rule lpp_split_prefix_partial_initial[OF prefix entry])
qed

ML \<open>
val checked = @{thms lpp_recursive_partial_prefix_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted recursive prefix composition" else ();
\<close>
end
