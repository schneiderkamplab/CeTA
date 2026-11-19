theory LP_Prolog_Cons_Successor_Facts
 imports LP_Prolog_Attached_Cons_Head
begin

text \<open>Discharge the post-unification finiteness premise of fresh recursive
output transport from a finite incoming call and a proper spine. Tail length
is preserved separately; a proper spine alone does not prove finite elements.\<close>

lemma lpp_cons_recursive_successor_facts:
 assumes head_shape: "heads=Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H"
 and parameter_map: "lpp_check_clause_coordinate l (heads!i) target_parameter bindings"
 and fresh_map: "lpp_check_body_output (Fun p heads) bs l body_variable target_output bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p (input_value#actuals)) gs (Fun p heads) bs sigma rho"
 and bound: "i<length heads"
 and tracked: "lpp_runtime_parameter initial_parameter ((input_value#actuals)!i)"
 and spine: "lpp_list_length input_value spine_length"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and finite_call: "lpp_finite_term (LPIFun p (input_value#actuals))"
 shows "lpp_runtime_parameter initial_parameter (lp_ieval target_parameter
   (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))) \<and>
  (\<exists>v. lp_ieval target_output
   (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))=LPIVar v) \<and>
  set2_lp_iterm (lp_ieval target_output
   (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho)))
   \<inter> set2_lp_iterm (lp_isubst (LPIFun p (input_value#actuals)) sigma)={}"
proof -
 have finite_subst: "lpp_finite_term (lp_isubst (LPIFun p (input_value#actuals)) sigma)"
  by (rule lpp_cons_head_finite_instance[OF spine mgu[unfolded head_shape] distinct lengths finite_call])
 show ?thesis by (rule lpp_checked_recursive_head_successor_facts[OF parameter_map fresh_map mgu bound tracked finite_subst])
qed

ML \<open>
val checked = @{thms lpp_cons_recursive_successor_facts};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted cons successor facts" else ();
\<close>
end
