theory Global_Cons_Functor_Check
 imports Global_Cons_Contract_Check
begin

lemma cons_functor_successor_coordinates:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and functor_fact: "lpp_functor_fact_holds names eta
   (LPPFunctorFact (Var functor_slot) (Var name_slot) (Var input_slot))"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and head_map: "lpp_check_clause_coordinate l (Var x) target_head bindings"
 and tail_map: "lpp_check_clause_coordinate l (Var y) target_tail bindings"
 and output_map: "lpp_check_clause_coordinate l (Var out) target_output bindings"
 and name_map: "target_name \<cdot> lp_cut_instance_subst bindings = Var name_slot"
 and functor_map: "target_functor \<cdot> lp_cut_instance_subst bindings = Var (lp_prefix k functor_slot)"
 and short: "length name_slot < k" "length functor_slot < k"
 and bounds: "2 * k \<le> l"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"
 shows "lp_ieval target_parameter nu = eta parameter_slot \<and>
  lp_ieval target_name nu = eta name_slot \<and>
  lp_seg_ground (lp_ieval target_name nu) \<and>
  lp_ieval target_functor nu = lp_isubst (eta functor_slot) sigma \<and>
  lpp_functor_fact_holds names nu
   (LPPFunctorFact target_functor target_name
    (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail])) \<and>
  lpc_return_env [target_functor,target_parameter,target_output] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var functor_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
proof -
 have coordinates: "lp_ieval target_head nu = rho x" "lp_ieval target_tail nu = rho y"
   "lp_ieval target_parameter nu = rho n" "lp_ieval target_output nu = rho out"
  using lpp_checked_clause_coordinate_value[OF head_map, of k eta sigma rho]
   lpp_checked_clause_coordinate_value[OF tail_map, of k eta sigma rho]
   lpp_checked_clause_coordinate_value[OF parameter_map, of k eta sigma rho]
   lpp_checked_clause_coordinate_value[OF output_map, of k eta sigma rho]
  by (simp_all add: nu_def)
 have equations: "LPIFun (LPCUser ''2:prolog_data_2e'') [rho x,rho y] = lp_isubst (eta input_slot) sigma"
   "rho n = lp_isubst (eta parameter_slot) sigma" "rho out = lp_isubst (eta output_slot) sigma"
  using actual by (auto simp: lpc_mgu_resolve_def)
 have ground: "lp_seg_ground (eta parameter_slot)" by (rule lpp_runtime_parameter_ground[OF tracked])
 have parameter_eq: "lp_ieval target_parameter nu = eta parameter_slot"
  using coordinates equations lp_seg_ground_subst[OF ground] by simp
 have named: "lp_ieval target_name nu = eta name_slot"
  using name_map short bounds
  by (simp add: nu_def lp_ieval_finite_subst[symmetric] lp_cut_resolution_env_def)
 have name_ground: "lp_seg_ground (eta name_slot)"
  using lpp_functor_observation_name_ground functor_fact by auto
 have old_bounds: "k + length functor_slot < l" using short bounds by arith
 have constructed: "lp_ieval target_functor nu = lp_isubst (eta functor_slot) sigma"
  using functor_map old_bounds short
  by (simp add: nu_def lp_ieval_finite_subst[symmetric] lp_cut_resolution_env_def lp_prefix_def)
 have transported: "lpp_functor_fact_holds names (\<lambda>v. lp_isubst (eta v) sigma)
   (LPPFunctorFact (Var functor_slot) (Var name_slot) (Var input_slot))"
  by (rule lpp_functor_fact_runtime_subst[OF functor_fact])
 have target_fact: "lpp_functor_fact_holds names nu
   (LPPFunctorFact target_functor target_name
    (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail]))"
  using transported by (simp add: constructed named coordinates equations lp_seg_ground_subst[OF name_ground])
 have payload: "lpc_return_env [target_functor,target_parameter,target_output] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var functor_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
  by (rule lpc_return_env_active) (simp add: constructed coordinates equations)
 show ?thesis using parameter_eq named name_ground constructed target_fact payload by simp
qed

lemma cons_actual_functor_observation:
 fixes input_value parameter output_value original_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and spine: "lpp_list_length input_value spine_length"
 and distinct: "distinct [x,y,n,out]"
 and functor_fact: "lpp_functor_observation names original_value name_value input_value"
 and observed: "observed_leaf_coordinate encode A initial_tree original_value shadow"
 shows "observed_leaf_coordinate encode A initial_tree (lp_isubst original_value sigma) shadow"
proof -
 obtain witness where matching: "lp_ieval
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) witness =
   LPIFun p [input_value,parameter,output_value]"
  using lpp_spine_head_matching_witness[where H="[n,out]", unfolded list.map, OF spine actual distinct] by auto
 have comparison: "lp_isubst (LPIFun p [input_value,parameter,output_value]) LPIVar =
  lp_ieval (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) witness"
  using matching by simp
 obtain delta where inverse_call: "lp_isubst (lp_isubst (LPIFun p [input_value,parameter,output_value]) sigma) delta =
  LPIFun p [input_value,parameter,output_value]"
  using actual comparison unfolding lpc_mgu_resolve_def by fastforce
 have inverse_input: "lp_isubst (lp_isubst input_value sigma) delta = input_value"
  using inverse_call by simp
 obtain ctor children where original_shape: "original_value = LPIFun ctor children"
 and input_shape: "input_value = lpp_argument_list children"
  using functor_fact by (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def)
 have inverse_children: "map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) children = children"
  using inverse_input by (simp add: input_shape lpp_argument_list_subst map_map o_def lpp_argument_list_injective)
 have inverse_original: "lp_isubst (lp_isubst original_value sigma) delta = original_value"
  by (simp add: original_shape map_map o_def inverse_children)
 obtain current_tree where current: "lpp_runtime_structure original_value current_tree"
 and effect: "lpp_leaf_effect A initial_tree current_tree"
 and shadow_eq: "shadow = lp_ieval (map_term encode id (lpp_reify_structure current_tree)) (\<lambda>_. LPIVar undefined)"
  using observed by (auto simp: observed_leaf_coordinate_def)
 have finite_original: "lpp_finite_term original_value" by (rule lpp_runtime_structure_finite[OF current])
 obtain preserved_tree where before: "lpp_runtime_structure original_value preserved_tree"
 and after: "lpp_runtime_structure (lp_isubst original_value sigma) preserved_tree"
  using lpp_finite_inverse_structural_observation[OF finite_original inverse_original] by blast
 have equal_trees: "preserved_tree = current_tree"
  by (rule lpp_runtime_structure_unique[OF before current])
 show ?thesis using after effect shadow_eq equal_trees by (auto simp: observed_leaf_coordinate_def)
qed

ML \<open>
val checked = @{thms cons_functor_successor_coordinates cons_actual_functor_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons functor coordinates" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-functor/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Full larger cons residual and node contract remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "CONS_FUNCTOR_KERNEL_CHECKED";
\<close>
end
