theory Global_Cons_Output_Check
 imports Global_Fresh_Output_Observation_Check
begin

lemma cons_actual_output_structure:
 fixes input_value parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes spine: "lpp_list_length input_value spine_length"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and distinct: "distinct [x,y,n,out]"
 and finite: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and observed: "lpp_runtime_structure output_value output_tree"
 shows "lpp_runtime_structure (rho out) output_tree"
proof -
 obtain witness where matching: "lp_ieval
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) witness =
   LPIFun p [input_value,parameter,output_value]"
  using lpp_spine_head_matching_witness[where H="[n,out]", unfolded list.map, OF spine actual distinct] by auto
 obtain template rename where before: "LPIFun p [input_value,parameter,output_value] = lp_ieval template LPIVar"
 and after: "lp_ieval (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) rho =
   lp_ieval template (LPIVar \<circ> rename)"
  using lpp_matching_head_preserves_structure[OF actual matching finite] by blast
 obtain input_template parameter_template output_template where template:
  "template = Fun p [input_template,parameter_template,output_template]"
 and output_before: "output_value = lp_ieval output_template LPIVar"
  using before by (cases template) (auto simp: map_eq_Cons_conv)
 have output_after: "rho out = lp_ieval output_template (LPIVar \<circ> rename)"
  using after by (simp add: template)
 have old: "lpp_runtime_structure output_value (lpp_structure_template output_template)"
  unfolding lpp_runtime_structure_def by (rule exI[of _ output_template]) (simp add: output_before)
 have current: "lpp_runtime_structure (rho out) (lpp_structure_template output_template)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "map_term id rename output_template"])
   (simp add: output_after lpp_ieval_template_rename lpp_structure_template_rename)
 show ?thesis using lpp_runtime_structure_unique[OF observed old] current by simp
qed

lemma cons_actual_parameter_output_observations:
 fixes input_value parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes spine: "lpp_list_length input_value spine_length"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and distinct: "distinct [x,y,n,out]"
 and finite: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and parameter_observed: "observed_leaf_coordinate encode A parameter_tree parameter parameter_shadow"
 and output_observed: "observed_leaf_coordinate encode B output_tree output_value output_shadow"
 shows "rho n = parameter \<and> lpp_runtime_parameter initial_parameter (rho n) \<and>
  observed_leaf_coordinate encode A parameter_tree (rho n) parameter_shadow \<and>
  observed_leaf_coordinate encode B output_tree (rho out) output_shadow"
proof -
 have ground: "lp_seg_ground parameter" by (rule lpp_runtime_parameter_ground[OF tracked])
 have parameter_eq: "rho n = parameter"
  using actual ground by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)
 obtain current_tree where observed: "lpp_runtime_structure output_value current_tree"
 and effect: "lpp_leaf_effect B output_tree current_tree"
 and shadow: "output_shadow = lp_ieval (map_term encode id (lpp_reify_structure current_tree)) (\<lambda>_. LPIVar undefined)"
  using output_observed by (auto simp: observed_leaf_coordinate_def)
 have current: "lpp_runtime_structure (rho out) current_tree"
  by (rule cons_actual_output_structure[OF spine actual distinct finite observed])
 have output_result: "observed_leaf_coordinate encode B output_tree (rho out) output_shadow"
  using current effect shadow by (auto simp: observed_leaf_coordinate_def)
 show ?thesis using parameter_eq tracked parameter_observed output_result by simp
qed

lemma cons_five_successor_observations:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes spine: "lpp_list_length input_value spine_length"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and distinct: "distinct [x,y,n,out]"
 and finite: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and input_observed: "observed_leaf_coordinate encode C input_tree input_value input_shadow"
 and parameter_observed: "observed_leaf_coordinate encode A parameter_tree parameter parameter_shadow"
 and output_observed: "observed_leaf_coordinate encode B output_tree output_value output_shadow"
 and head_map: "lpp_check_clause_coordinate l (Var x) target_head bindings"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and tail_map: "lpp_check_clause_coordinate l (Var y) target_tail bindings"
 and output_map: "lpp_check_clause_coordinate l (Var out) target_output bindings"
 and fresh_map: "lpp_check_body_output
  (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs l body_variable target_fresh bindings"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x)
   (lp_cut_resolution_env k l eta sigma rho)"
 shows "\<exists>head_tree tail_tree head_shadow tail_shadow.
  lp_ieval target_parameter nu = parameter \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter nu) \<and>
  observed_leaf_coordinate encode C head_tree (lp_ieval target_head nu) head_shadow \<and>
  observed_leaf_coordinate encode A parameter_tree (lp_ieval target_parameter nu) parameter_shadow \<and>
  observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh nu) (LPIFun (encode LPPStructureLeaf) []) \<and>
  observed_leaf_coordinate encode C tail_tree (lp_ieval target_tail nu) tail_shadow \<and>
  observed_leaf_coordinate encode B output_tree (lp_ieval target_output nu) output_shadow \<and>
  input_shadow = LPIFun (encode LPPStructureNode)
   [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
    LPIFun (encode LPPStructureCons) [head_shadow,
     LPIFun (encode LPPStructureCons) [tail_shadow,LPIFun (encode LPPStructureNil) []]]]"
proof -
 have coordinates: "lp_ieval target_head nu = rho x" "lp_ieval target_parameter nu = rho n"
   "lp_ieval target_tail nu = rho y" "lp_ieval target_output nu = rho out"
  using lpp_checked_clause_coordinate_value[OF head_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF parameter_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF tail_map, of k eta sigma rho]
    lpp_checked_clause_coordinate_value[OF output_map, of k eta sigma rho]
  by (simp_all add: nu_def)
 have finite_after: "lpp_finite_term (lp_isubst (LPIFun p [input_value,parameter,output_value]) sigma)"
  by (rule lpp_cons_head_finite_instance[where H="[n,out]", unfolded list.map,
    OF spine actual distinct _ finite]) simp
 have fresh: "observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh nu)
   (LPIFun (encode LPPStructureLeaf) [])"
  using actual_fresh_output_observation[OF fresh_map actual finite_after, of k eta encode C]
  by (auto simp: nu_def)
 show ?thesis
  using cons_actual_observation_split[OF spine actual distinct finite input_observed]
    cons_actual_parameter_output_observations[OF spine actual distinct finite tracked parameter_observed output_observed]
    fresh coordinates by auto
qed

ML \<open>
val checked = @{thms cons_actual_output_structure cons_actual_parameter_output_observations cons_five_successor_observations};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons output observations" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-output/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Actual cons parameter/output observations transported; full residual assembly remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_CONS_OUTPUT_KERNEL_CHECKED";
\<close>
end
