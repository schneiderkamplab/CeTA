theory Global_Cons_Residual_Check
 imports Global_Cons_Output_Check
begin

lemma cons_six_to_ten_step:
 assumes clause: "((source_symbol,[Var r0,Var r1,Var r2,
  Fun (encode LPPStructureNode) [Fun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
   Fun (encode LPPStructureCons) [Var sh,Fun (encode LPPStructureCons) [Var st,Fun (encode LPPStructureNil) []]]],
  Var sp,Var so]),[(target_symbol,map Var [rh,rn,rf,rt,ro,sh,sp,sf,st,so])]) \<in> set Q"
 and distinct: "distinct [r0,r1,r2,sh,st,sp,so,rh,rn,rf,rt,ro,sf]"
 shows "([(source_symbol,[input_value,parameter,output_value,
  LPIFun (encode LPPStructureNode) [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
   LPIFun (encode LPPStructureCons) [head_shadow,LPIFun (encode LPPStructureCons) [tail_shadow,LPIFun (encode LPPStructureNil) []]]],
  parameter_shadow,output_shadow])],
  [(target_symbol,[head_value,next_parameter,fresh_value,tail_value,next_output,
    head_shadow,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),tail_shadow,output_shadow])]) \<in> lp_ild Q"
proof -
 let ?nu = "\<lambda>v. if v=r0 then input_value else if v=r1 then parameter else if v=r2 then output_value else
  if v=sh then head_shadow else if v=st then tail_shadow else if v=sp then parameter_shadow else
  if v=so then output_shadow else if v=rh then head_value else if v=rn then next_parameter else
  if v=rf then fresh_value else if v=rt then tail_value else if v=ro then next_output else (LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm)"
 show ?thesis
  using lp_seg_residual_step[OF clause, where
   a="(source_symbol,[input_value,parameter,output_value,
    LPIFun (encode LPPStructureNode) [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
     LPIFun (encode LPPStructureCons) [head_shadow,LPIFun (encode LPPStructureCons) [tail_shadow,LPIFun (encode LPPStructureNil) []]]],
    parameter_shadow,output_shadow])"
   and \<sigma>=LPIVar and \<rho>="?nu" and rest="[]"] distinct
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
qed

lemma actual_cons_six_to_ten_observations:
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
 and clause: "((source_symbol,[Var r0,Var r1,Var r2,
  Fun (encode LPPStructureNode) [Fun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
   Fun (encode LPPStructureCons) [Var sh,Fun (encode LPPStructureCons) [Var st,Fun (encode LPPStructureNil) []]]],
  Var sp,Var so]),[(target_symbol,map Var [rh,rn,rf,rt,ro,sh,sp,sf,st,so])]) \<in> set Q"
 and residual_distinct: "distinct [r0,r1,r2,sh,st,sp,so,rh,rn,rf,rt,ro,sf]"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x)
   (lp_cut_resolution_env k l eta sigma rho)"
 shows "\<exists>head_tree tail_tree head_shadow tail_shadow.
  lp_ieval target_parameter nu = parameter \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter nu) \<and>
  observed_leaf_coordinate encode C head_tree (lp_ieval target_head nu) head_shadow \<and>
  observed_leaf_coordinate encode A parameter_tree (lp_ieval target_parameter nu) parameter_shadow \<and>
  observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh nu) ((LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm)) \<and>
  observed_leaf_coordinate encode C tail_tree (lp_ieval target_tail nu) tail_shadow \<and>
  observed_leaf_coordinate encode B output_tree (lp_ieval target_output nu) output_shadow \<and>
  ([(source_symbol,[input_value,parameter,output_value,input_shadow,parameter_shadow,output_shadow])],
   [(target_symbol,[lp_ieval target_head nu,lp_ieval target_parameter nu,lp_ieval target_fresh nu,
     lp_ieval target_tail nu,lp_ieval target_output nu,
     head_shadow,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),tail_shadow,output_shadow])]) \<in> (lp_ild Q)\<^sup>+"
proof -
 obtain head_tree tail_tree head_shadow tail_shadow where facts: "lp_ieval target_parameter nu = parameter \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter nu) \<and>
  observed_leaf_coordinate encode C head_tree (lp_ieval target_head nu) head_shadow \<and>
  observed_leaf_coordinate encode A parameter_tree (lp_ieval target_parameter nu) parameter_shadow \<and>
  observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh nu) ((LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm)) \<and>
  observed_leaf_coordinate encode C tail_tree (lp_ieval target_tail nu) tail_shadow \<and>
  observed_leaf_coordinate encode B output_tree (lp_ieval target_output nu) output_shadow \<and>
  input_shadow = LPIFun (encode LPPStructureNode)
   [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
    LPIFun (encode LPPStructureCons) [head_shadow,
     LPIFun (encode LPPStructureCons) [tail_shadow,LPIFun (encode LPPStructureNil) []]]]"
  using cons_five_successor_observations[OF spine actual distinct finite tracked input_observed
   parameter_observed output_observed head_map parameter_map tail_map output_map fresh_map, of k eta]
  by (auto simp: nu_def)
 have edge: "([(source_symbol,[input_value,parameter,output_value,
  LPIFun (encode LPPStructureNode) [LPIFun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
   LPIFun (encode LPPStructureCons) [hs,LPIFun (encode LPPStructureCons) [ts,LPIFun (encode LPPStructureNil) []]]],
  parameter_shadow,output_shadow])],
  [(target_symbol,[lp_ieval target_head nu,lp_ieval target_parameter nu,lp_ieval target_fresh nu,
   lp_ieval target_tail nu,lp_ieval target_output nu,hs,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),ts,output_shadow])]) \<in> lp_ild Q" for hs ts
  by (rule cons_six_to_ten_step[OF clause residual_distinct])
 show ?thesis
  apply (rule exI[of _ head_tree])
  apply (rule exI[of _ tail_tree])
  apply (rule exI[of _ head_shadow])
  apply (rule exI[of _ tail_shadow])
  using facts edge[of head_shadow tail_shadow] by (auto intro: r_into_trancl)
qed

ML \<open>
val checked = @{thms cons_six_to_ten_step actual_cons_six_to_ten_observations};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons residual" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-residual/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Complete source row and family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_CONS_RESIDUAL_KERNEL_CHECKED";
\<close>
end
