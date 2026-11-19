theory Global_Cons_Observation_Check
 imports Global_Cons_Invariant_Check
begin

lemma cons_actual_child_structures:
 fixes input_value parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes spine: "lpp_list_length input_value spine_length"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and distinct: "distinct [x,y,n,out]"
 and finite: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and observed: "lpp_runtime_structure input_value input_tree"
 shows "\<exists>head_tree tail_tree.
  input_tree = Fun (Inl (LPCUser ''2:prolog_data_2e'')) [head_tree,tail_tree] \<and>
  lpp_runtime_structure (rho x) head_tree \<and> lpp_runtime_structure (rho y) tail_tree"
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
 and input_before: "input_value = lp_ieval input_template LPIVar"
  using before by (cases template) (auto simp: map_eq_Cons_conv)
 obtain h t where input_shape: "input_template = Fun (LPCUser ''2:prolog_data_2e'') [h,t]"
 and children: "rho x = lp_ieval h (LPIVar \<circ> rename)" "rho y = lp_ieval t (LPIVar \<circ> rename)"
  using after[unfolded template] by (cases input_template) (auto simp: map_eq_Cons_conv)
 have old: "lpp_runtime_structure input_value (Fun (Inl (LPCUser ''2:prolog_data_2e''))
   [lpp_structure_template h,lpp_structure_template t])"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ input_template]) (simp add: input_before input_shape)
 have head_tree: "lpp_runtime_structure (rho x) (lpp_structure_template h)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "map_term id rename h"]) (simp add: children lpp_ieval_template_rename lpp_structure_template_rename)
 have tail_tree: "lpp_runtime_structure (rho y) (lpp_structure_template t)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "map_term id rename t"]) (simp add: children lpp_ieval_template_rename lpp_structure_template_rename)
 show ?thesis using lpp_runtime_structure_unique[OF observed old] head_tree tail_tree by blast
qed

lemma cons_actual_observation_split:
 fixes input_value parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes spine: "lpp_list_length input_value spine_length"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
 and distinct: "distinct [x,y,n,out]"
 and finite: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"

 and observed: "observed_leaf_coordinate encode A initial_tree input_value input_shadow"
 shows "\<exists>head_tree tail_tree head_shadow tail_shadow.
  observed_leaf_coordinate encode A head_tree (rho x) head_shadow \<and>
  observed_leaf_coordinate encode A tail_tree (rho y) tail_shadow \<and>
  input_shadow = LPIFun (encode LPPStructureNode)
   [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
    LPIFun (encode LPPStructureCons) [head_shadow,
     LPIFun (encode LPPStructureCons) [tail_shadow,LPIFun (encode LPPStructureNil) []]]]"
proof -
 obtain input_tree where input_structure: "lpp_runtime_structure input_value input_tree"
 and encoded: "input_shadow = lp_ieval (map_term encode id (lpp_reify_structure input_tree)) (\<lambda>_. LPIVar undefined)"
  using observed by (auto simp: observed_leaf_coordinate_def)
 obtain head_tree tail_tree where shape: "input_tree = Fun (Inl (LPCUser ''2:prolog_data_2e'')) [head_tree,tail_tree]"
 and head_structure: "lpp_runtime_structure (rho x) head_tree"
 and tail_structure: "lpp_runtime_structure (rho y) tail_tree"
  using cons_actual_child_structures[OF spine actual distinct finite input_structure] by blast
 let ?hs = "lp_ieval (map_term encode id (lpp_reify_structure head_tree)) (\<lambda>_. LPIVar undefined)"
 let ?ts = "lp_ieval (map_term encode id (lpp_reify_structure tail_tree)) (\<lambda>_. LPIVar undefined)"
 have head_observed: "observed_leaf_coordinate encode A head_tree (rho x) ?hs"
  using head_structure lpp_template_leaf_effect_reflexive
  unfolding observed_leaf_coordinate_def lpp_runtime_structure_def by blast
 have tail_observed: "observed_leaf_coordinate encode A tail_tree (rho y) ?ts"
  using tail_structure lpp_template_leaf_effect_reflexive
  unfolding observed_leaf_coordinate_def lpp_runtime_structure_def by blast
 have split: "input_shadow = LPIFun (encode LPPStructureNode)
   [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
    LPIFun (encode LPPStructureCons) [?hs,
     LPIFun (encode LPPStructureCons) [?ts,LPIFun (encode LPPStructureNil) []]]]"
  by (simp add: encoded shape)
 show ?thesis using head_observed tail_observed split by blast
qed

ML \<open>
val checked = @{thms cons_actual_child_structures cons_actual_observation_split};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons observations" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-observation/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Remaining cons coordinates and full row assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_CONS_OBSERVATION_KERNEL_CHECKED";
\<close>
end
