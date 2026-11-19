theory Global_Cons_Context_Check
 imports Global_Cons_Residual_Check
begin

lemma actual_cons_simple_context_payload:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and spine: "lpp_list_length (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and head_map: "lpp_check_clause_coordinate l (Var x) target_head bindings"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and tail_map: "lpp_check_clause_coordinate l (Var y) target_tail bindings"
 and output_map: "lpp_check_clause_coordinate l (Var out) target_output bindings"
 and fresh_map: "lpp_check_body_output
  (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs l body_variable target_fresh bindings"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x)
   (lp_cut_resolution_env k l eta sigma rho)"
 shows "lpc_return_env [Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail],target_parameter,target_output] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma) \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter nu) \<and>
  lpp_stable_context_holds operation SP
   ([],[LPPSOpaque target_parameter],[LPPOGround target_parameter,
    LPPOShape lpp_spine_grammar (LPReturnShape 0)
     (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail])]) nu \<and>
  (\<exists>v. lp_ieval target_fresh nu = LPIVar v)"
proof -
 have coordinates: "lp_ieval target_head nu = rho x" "lp_ieval target_parameter nu = rho n"
   "lp_ieval target_tail nu = rho y" "lp_ieval target_output nu = rho out"
  using lpp_checked_clause_coordinate_value[OF head_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF parameter_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF tail_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF output_map, of k eta sigma rho]
  by (simp_all add: nu_def)
 have equations: "LPIFun (LPCUser ''2:prolog_data_2e'') [rho x,rho y] = lp_isubst (eta input_slot) sigma"
   "rho n = lp_isubst (eta parameter_slot) sigma" "rho out = lp_isubst (eta output_slot) sigma"
  using actual by (auto simp: lpc_mgu_resolve_def)
 have ground: "lp_seg_ground (eta parameter_slot)" by (rule lpp_runtime_parameter_ground[OF tracked])
 have parameter_eq: "lp_ieval target_parameter nu = eta parameter_slot"
  using coordinates equations lp_seg_ground_subst[OF ground] by simp
 have payload: "lpc_return_env [Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail],target_parameter,target_output] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
  by (rule lpc_return_env_active) (simp add: coordinates equations)
 have shape: "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0)
   (lp_ieval (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail]) nu)"
  using lpp_list_length_return_shape[OF lpp_list_length_subst[OF spine, of sigma]]
  by (simp add: coordinates equations)
 have context_fact: "lpp_stable_context_holds operation SP
   ([],[LPPSOpaque target_parameter],[LPPOGround target_parameter,
    LPPOShape lpp_spine_grammar (LPReturnShape 0)
     (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail])]) nu"
  using shape ground parameter_eq
  by (simp add: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)
 have fresh: "\<exists>v. lp_ieval target_fresh nu = LPIVar v"
  using lpp_checked_body_output_free[OF fresh_map actual, of k eta] by (auto simp: nu_def)
 show ?thesis using payload tracked parameter_eq context_fact fresh by simp
qed

ML \<open>
val checked = @{thms actual_cons_simple_context_payload};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons successor context" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-context/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Conditional simple cons successor context and total payload; full family remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "CONS_CONTEXT_KERNEL_CHECKED";
\<close>
end
