theory Recursive_Split_Observer_Check
 imports Global_Copy_Invariant_Check
begin

lemma split_30_observer_initial:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and p q :: "string lp_cut_symbol"
 assumes entry: "lpp_recursive_partial_entry initial_parameter ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' eta"
 defines rest_def: "rest \<equiv> [LPCAtom (Fun q [Var 2,Var 1,Var 3])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun p [eta ''V0'',eta ''V1'',eta ''V2''])],
   case_sum (lpc_return_env (map Var [''V0'',''V1'',''V2'']) eta) (lpc_return_env (map Var [''V1'',''V2'',''V3'',''V4'']) eta))]"
 shows "\<exists>xs caller_shape.
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(1,Fun (Inr ()) []),(2,lpp_structural_argument_list xs),(3,caller_shape)] rest 2 1 runtime \<and>
  lpp_check_attached_leaf_slots [1,2,3] rest \<and>
  lpp_caller_output_mode (eta ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (eta ''V2'')"
proof -
 have coordinates: "lpp_check_prefix_caller_coordinates (map Var [''V1'',''V2'',''V3'',''V4'']) ''V2'' ''V3'' ''V4'' 1 2 3"
  by (simp add: lpp_check_prefix_caller_coordinates_def)
 obtain xs caller_shape where invariant:
  "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(1,Fun (Inr ()) []),(2,lpp_structural_argument_list xs),(3,caller_shape)] rest 2 1 runtime"
  using lpp_observer_output_prefix_initial[OF coordinates entry,
    where helper_payload="map Var [''V0'',''V1'',''V2'']" and oi=2 and p=p and q=q and f=f and g=g]
  by (auto simp: rest_def runtime_def)
 have tracked: "lpp_runtime_parameter initial_parameter (eta ''V1'')"
  using entry by (simp add: lpp_recursive_partial_entry_def)
 have facts: "lpp_caller_output_mode (eta ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (eta ''V2'')"
  by (rule copy_output_facts_from_invariant[OF invariant[unfolded runtime_def] _ tracked])
   (simp_all add: lpc_return_env_def)
 have covered: "lpp_check_attached_leaf_slots [1,2,3] rest"
  by (simp add: rest_def lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)
 show ?thesis using invariant facts covered by blast
qed

lemma split_44_observer_initial:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and p q :: "string lp_cut_symbol"
 assumes entry: "lpp_recursive_partial_entry initial_parameter ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' eta"
 defines rest_def: "rest \<equiv> [LPCAtom (Fun q [Var 1,Var 0,Var 2])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun p [eta ''V0'',eta ''V1'',eta ''V2''])],
   case_sum (lpc_return_env (map Var [''V0'',''V1'',''V2'']) eta) (lpc_return_env (map Var [''V2'',''V3'',''V4'']) eta))]"
 shows "\<exists>xs caller_shape.
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(0,Fun (Inr ()) []),(1,lpp_structural_argument_list xs),(2,caller_shape)] rest 2 0 runtime \<and>
  lpp_check_attached_leaf_slots [0,1,2] rest \<and>
  lpp_caller_output_mode (eta ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (eta ''V2'')"
proof -
 have coordinates: "lpp_check_prefix_caller_coordinates (map Var [''V2'',''V3'',''V4'']) ''V2'' ''V3'' ''V4'' 0 1 2"
  by (simp add: lpp_check_prefix_caller_coordinates_def)
 obtain xs caller_shape where invariant:
  "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(0,Fun (Inr ()) []),(1,lpp_structural_argument_list xs),(2,caller_shape)] rest 2 0 runtime"
  using lpp_observer_output_prefix_initial[OF coordinates entry,
    where helper_payload="map Var [''V0'',''V1'',''V2'']" and oi=2 and p=p and q=q and f=f and g=g]
  by (auto simp: rest_def runtime_def)
 have tracked: "lpp_runtime_parameter initial_parameter (eta ''V1'')"
  using entry by (simp add: lpp_recursive_partial_entry_def)
 have facts: "lpp_caller_output_mode (eta ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (eta ''V2'')"
  by (rule copy_output_facts_from_invariant[OF invariant[unfolded runtime_def] _ tracked])
   (simp_all add: lpc_return_env_def)
 have covered: "lpp_check_attached_leaf_slots [0,1,2] rest"
  by (simp add: rest_def lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)
 show ?thesis using invariant facts covered by blast
qed

lemma actual_split_30_observer_initial:
 fixes k :: nat
 and eta sigma rho nu :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and helper_pred tail_pred :: "string lp_cut_symbol"
 assumes checked: "lpp_check_recursive_entry_coordinates
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs l x y n m fresh_variable
   ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs sigma rho"
 and spine: "lpp_list_length (lp_ieval input_term eta) spine_length"
 and finite_call: "lpp_finite_term (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_variable)"
 defines target_env: "nu \<equiv> (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))"
 and rest_def: "rest \<equiv> [LPCAtom (Fun tail_pred [Var 2,Var 1,Var 3])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun helper_pred [nu ''V0'',nu ''V1'',nu ''V2''])],
   case_sum (lpc_return_env (map Var [''V0'',''V1'',''V2'']) nu) (lpc_return_env (map Var [''V1'',''V2'',''V3'',''V4'']) nu))]"
 shows "\<exists>xs caller_shape.
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(1,Fun (Inr ()) []),(2,lpp_structural_argument_list xs),(3,caller_shape)] rest 2 1 runtime \<and>
  lpp_check_attached_leaf_slots [1,2,3] rest \<and>
  lpp_caller_output_mode (nu ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (nu ''V2'')"
proof -
 have entry: "lpp_recursive_partial_entry initial_parameter ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' nu"
  using lpp_checked_recursive_partial_entry[OF checked mgu spine finite_call tracked, of k]
  by (simp add: target_env)
 show ?thesis using split_30_observer_initial[OF entry, where q=tail_pred and p=helper_pred and f=f and g=g]
  by (simp add: rest_def runtime_def)
qed

lemma actual_split_44_observer_initial:
 fixes k :: nat
 and eta sigma rho nu :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and helper_pred tail_pred :: "string lp_cut_symbol"
 assumes checked: "lpp_check_recursive_entry_coordinates
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs l x y n m fresh_variable
   ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs sigma rho"
 and spine: "lpp_list_length (lp_ieval input_term eta) spine_length"
 and finite_call: "lpp_finite_term (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_variable)"
 defines target_env: "nu \<equiv> (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))"
 and rest_def: "rest \<equiv> [LPCAtom (Fun tail_pred [Var 1,Var 0,Var 2])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun helper_pred [nu ''V0'',nu ''V1'',nu ''V2''])],
   case_sum (lpc_return_env (map Var [''V0'',''V1'',''V2'']) nu) (lpc_return_env (map Var [''V2'',''V3'',''V4'']) nu))]"
 shows "\<exists>xs caller_shape.
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   [(0,Fun (Inr ()) []),(1,lpp_structural_argument_list xs),(2,caller_shape)] rest 2 0 runtime \<and>
  lpp_check_attached_leaf_slots [0,1,2] rest \<and>
  lpp_caller_output_mode (nu ''V2'') \<and>
  lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inr ()) []) (nu ''V2'')"
proof -
 have entry: "lpp_recursive_partial_entry initial_parameter ''V0'' ''V1'' ''V2'' ''V3'' ''V4'' nu"
  using lpp_checked_recursive_partial_entry[OF checked mgu spine finite_call tracked, of k]
  by (simp add: target_env)
 show ?thesis using split_44_observer_initial[OF entry, where q=tail_pred and p=helper_pred and f=f and g=g]
  by (simp add: rest_def runtime_def)
qed

ML \<open>
val checked = @{thms split_30_observer_initial split_44_observer_initial actual_split_30_observer_initial actual_split_44_observer_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted recursive split observer" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-recursive-split-observer/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Actual cons resolution initializes observer slots; full family assembly remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "RECURSIVE_SPLIT_OBSERVER_KERNEL_CHECKED";
\<close>
end
