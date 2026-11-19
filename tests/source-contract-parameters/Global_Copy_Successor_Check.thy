theory Global_Copy_Successor_Check
 imports Global_Copy_Observation_Check
begin

text \<open>The extra coordinates at 0:25 denote the constructor name and the
original constructed value, not additional numeric parameters. Actual copy
success forces its argument list empty; the retained functor fact therefore
makes both values nullary and unchanged by the actual substitution.\<close>

lemma copy_empty_arguments_functor:
 assumes observation: "lpp_functor_observation names original_value name_value
   (LPIFun (LPCUser ''0:prolog_data_5b5d'') [])"
 shows "\<exists>f. original_value = LPIFun f [] \<and> name_value = LPIFun (names f) []"
proof -
 obtain f ts where shape: "original_value = LPIFun f ts"
 and args: "LPIFun (LPCUser ''0:prolog_data_5b5d'') [] = lpp_argument_list ts"
 and name: "name_value = LPIFun (names f) []"
  using observation by (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def)
 have empty: "ts = []" using args by (cases ts) auto
 show ?thesis using shape name empty by blast
qed

lemma copy_functor_successor_coordinates:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and functor_fact: "lpp_functor_fact_holds names eta
   (LPPFunctorFact (Var functor_slot) (Var name_slot) (Var input_slot))"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and name_map: "target_name \<cdot> lp_cut_instance_subst bindings = Var name_slot"
 and functor_map: "target_functor \<cdot> lp_cut_instance_subst bindings = Var (lp_prefix k functor_slot)"
 and short: "length name_slot < k" "length functor_slot < k"
 and bounds: "2 * k \<le> l"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"
 shows "lp_ieval target_parameter nu = eta parameter_slot \<and>
  lp_ieval target_name nu = eta name_slot \<and>
  lp_ieval target_functor nu = eta functor_slot \<and>
  lp_seg_ground (eta name_slot) \<and> lp_seg_ground (eta functor_slot) \<and>
  lpp_functor_fact_holds names nu
   (LPPFunctorFact target_functor target_name (Fun (LPCUser ''0:prolog_data_5b5d'') [])) \<and>
  lpc_return_env [target_functor,target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var functor_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
proof -
 have input_nil: "eta input_slot = LPIFun (LPCUser ''0:prolog_data_5b5d'') []"
  by (rule lpp_parameter_copy_head_input[OF spine actual])
 obtain ctor where scalar: "eta functor_slot = LPIFun ctor []"
 and name_scalar: "eta name_slot = LPIFun (names ctor) []"
  using copy_empty_arguments_functor[of names "eta functor_slot" "eta name_slot"] functor_fact input_nil by auto
 have parameter_ground: "lp_seg_ground (eta parameter_slot)"
  by (rule lpp_runtime_parameter_ground[OF tracked])
 have copied: "rho n = eta parameter_slot" "lp_isubst (eta output_slot) sigma = eta parameter_slot"
  using actual parameter_ground by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)
 have parameter: "lp_ieval target_parameter nu = eta parameter_slot"
  using lpp_checked_clause_coordinate_value[OF parameter_map, of k eta sigma rho] copied
  by (simp add: nu_def)
 have named: "lp_ieval target_name nu = eta name_slot"
  using name_map short bounds
  by (simp add: nu_def lp_ieval_finite_subst[symmetric] lp_cut_resolution_env_def)
 have old_bounds: "k + length functor_slot < l" using short bounds by arith
 have constructed: "lp_ieval target_functor nu = eta functor_slot"
  using functor_map old_bounds short
  by (simp add: nu_def lp_ieval_finite_subst[symmetric] lp_cut_resolution_env_def lp_prefix_def scalar)
 have target_fact: "lpp_functor_fact_holds names nu
   (LPPFunctorFact target_functor target_name (Fun (LPCUser ''0:prolog_data_5b5d'') []))"
  by (simp add: parameter named constructed scalar name_scalar lpp_functor_observation_exact)
 have payload: "lpc_return_env [target_functor,target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var functor_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
  by (rule lpc_return_env_active)
   (simp add: parameter constructed scalar copied lp_seg_ground_subst[OF parameter_ground])
 show ?thesis using parameter named constructed scalar name_scalar target_fact payload by simp
qed

lemma copy_simple_successor_payload:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"
 shows "lp_ieval target_parameter nu = eta parameter_slot \<and>
  lpc_return_env [Fun nil [],target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
proof -
 have input_nil: "eta input_slot = LPIFun nil []"
  by (rule lpp_parameter_copy_head_input[OF spine actual])
 have ground: "lp_seg_ground (eta parameter_slot)" by (rule lpp_runtime_parameter_ground[OF tracked])
 have copied: "rho n = eta parameter_slot" "lp_isubst (eta output_slot) sigma = eta parameter_slot"
  using actual ground by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)
 have parameter: "lp_ieval target_parameter nu = eta parameter_slot"
  using lpp_checked_clause_coordinate_value[OF parameter_map, of k eta sigma rho] copied by (simp add: nu_def)
 have payload: "lpc_return_env [Fun nil [],target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
  by (rule lpc_return_env_active) (simp add: parameter input_nil copied lp_seg_ground_subst[OF ground])
 show ?thesis using parameter payload by blast
qed

lemma copy_functor_successor_observations:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and functor_fact: "lpp_functor_fact_holds names eta
   (LPPFunctorFact (Var functor_slot) (Var name_slot) (Var input_slot))"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and name_map: "target_name \<cdot> lp_cut_instance_subst bindings = Var name_slot"
 and functor_map: "target_functor \<cdot> lp_cut_instance_subst bindings = Var (lp_prefix k functor_slot)"
 and short: "length name_slot < k" "length functor_slot < k"
 and bounds: "2 * k \<le> l"
 and mode: "lpp_caller_output_mode (eta output_slot)"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree (eta output_slot)"
 and parameter_observed: "observed_leaf_coordinate encode B parameter_tree (eta parameter_slot) parameter_shadow"
 and name_observed: "observed_leaf_coordinate encode C name_tree (eta name_slot) name_shadow"
 and functor_observed: "observed_leaf_coordinate encode D functor_tree (eta functor_slot) functor_shadow"
 and clause: "((source_symbol,map Var [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [rn,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"
 shows "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_ieval target_parameter nu) parameter_shadow \<and>
  observed_leaf_coordinate encode C name_tree (lp_ieval target_name nu) name_shadow \<and>
  observed_leaf_coordinate encode D functor_tree (lp_ieval target_functor nu) functor_shadow \<and>
  ([(source_symbol,[eta input_slot,eta parameter_slot,eta output_slot,eta name_slot,eta functor_slot,
     input_shadow,parameter_shadow,output_shadow,name_shadow,functor_shadow])],
   [(target_symbol,[lp_ieval target_parameter nu,lp_ieval target_name nu,lp_ieval target_functor nu,
     parameter_shadow,name_shadow,functor_shadow])]) \<in> (lp_ild Q)\<^sup>+"
proof -
 have coordinates: "lp_ieval target_parameter nu = eta parameter_slot \<and>
   lp_ieval target_name nu = eta name_slot \<and> lp_ieval target_functor nu = eta functor_slot"
  using copy_functor_successor_coordinates[OF actual spine tracked functor_fact parameter_map name_map functor_map short bounds]
  by (simp add: nu_def)
 have copied: "lp_isubst (eta output_slot) sigma = eta parameter_slot \<and>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst (eta output_slot) sigma) parameter_shadow"
  using copy_resolution_reuses_observation[OF actual spine tracked mode finite_rest effect parameter_observed] by blast
 have edge: "([(source_symbol,[eta input_slot,eta parameter_slot,eta output_slot,eta name_slot,eta functor_slot,
     input_shadow,parameter_shadow,output_shadow,name_shadow,functor_shadow])],
   [(target_symbol,[eta parameter_slot,eta name_slot,eta functor_slot,
     parameter_shadow,name_shadow,functor_shadow])]) \<in> lp_ild Q"
  by (rule copy_ten_to_six_global_step[OF clause distinct])
 show ?thesis using coordinates copied name_observed functor_observed edge by (auto intro: r_into_trancl)
qed

ML \<open>
val checked = @{thms copy_empty_arguments_functor copy_functor_successor_coordinates copy_simple_successor_payload
 copy_functor_successor_observations};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted copy successor representation" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-successor/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Remaining row conditions and family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_SUCCESSOR_KERNEL_CHECKED";
\<close>
end
