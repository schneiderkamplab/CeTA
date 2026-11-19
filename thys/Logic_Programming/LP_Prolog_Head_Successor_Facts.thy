theory LP_Prolog_Head_Successor_Facts
 imports LP_Prolog_Parameter_Head_Return LP_Prolog_Parameter_Coordinate_Link
   LP_Prolog_Fresh_Continuation_Separation
begin

text \<open>Head and body coordinates use the actual clause environment.
Freeness is not freshness: separation from a live caller also needs its finite
value and coverage by the same MGU. Saved environments are not refreshed.\<close>

definition lpp_check_clause_coordinate where
 "lpp_check_clause_coordinate l source_term target_term bindings =
  (target_term \<cdot> lp_cut_instance_subst bindings =
   source_term \<cdot> (\<lambda>x. Var (lp_prefix l x)))"

lemma lpp_checked_clause_coordinate_value:
 assumes checked: "lpp_check_clause_coordinate l source_term target_term bindings"
 shows "lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)) =
  lp_ieval source_term rho"
 using checked
 by (simp add: lpp_check_clause_coordinate_def lp_ieval_finite_subst[symmetric] lp_cut_resolution_clause)

lemma lpp_checked_head_coordinate_value:
 assumes checked: "lpp_check_clause_coordinate l (heads!i) target_term bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p actuals) gs (Fun p heads) bs sigma rho"
 and bound: "i<length heads"
 shows "lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)) =
  lp_isubst (actuals!i) sigma"
proof -
 have equation: "map (\<lambda>t. lp_isubst t sigma) actuals=map (\<lambda>t. lp_ieval t rho) heads"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have lengths: "length actuals=length heads" using equation by (metis length_map)
 have component: "lp_isubst (actuals!i) sigma=lp_ieval (heads!i) rho"
  using arg_cong[OF equation, of "\<lambda>xs. xs!i"] bound lengths by simp
 show ?thesis using lpp_checked_clause_coordinate_value[OF checked] component by simp
qed

lemma lpp_checked_head_parameter_successor:
 assumes checked: "lpp_check_clause_coordinate l (heads!i) target_term bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p actuals) gs (Fun p heads) bs sigma rho"
 and bound: "i<length heads"
 and tracked: "lpp_runtime_parameter c (actuals!i)"
 shows "lpp_runtime_parameter c (lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))"
 using lpp_checked_head_coordinate_value[OF checked mgu bound, of k eta]
  lpp_runtime_parameter_subst[OF tracked, of sigma] by simp

lemma lpp_checked_head_free_successor:
 assumes checked: "lpp_check_clause_coordinate l (heads!i) target_term bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p actuals) gs (Fun p heads) bs sigma rho"
 and bound: "i<length heads"
 and free: "\<exists>x. lp_isubst (actuals!i) sigma=LPIVar x"
 shows "\<exists>x. lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))=LPIVar x"
 using lpp_checked_head_coordinate_value[OF checked mgu bound, of k eta] free by simp

definition lpp_check_body_output where
 "lpp_check_body_output h bs l body_variable target_term bindings =
  (body_variable\<in>lpc_body_only_variables h bs \<and>
   lpp_check_clause_coordinate l (Var body_variable) target_term bindings)"

lemma lpp_checked_body_output_value:
 assumes checked: "lpp_check_body_output h bs l body_variable target_term bindings"
 shows "lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))=rho body_variable"
 using checked lpp_checked_clause_coordinate_value[where source_term="Var body_variable"]
 by (auto simp: lpp_check_body_output_def)

lemma lpp_checked_body_output_free:
 assumes checked: "lpp_check_body_output h bs l body_variable target_term bindings"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 shows "\<exists>x. lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))=LPIVar x"
 using lpc_mgu_body_only_knowledge[OF mgu] checked
  lpp_checked_body_output_value[OF checked, of k eta sigma rho]
 by (auto simp: lpp_check_body_output_def lpc_free_knowledge_def)

lemma lpp_checked_body_output_separate_head:
 assumes checked: "lpp_check_body_output h bs l body_variable target_term bindings"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "set2_lp_iterm (lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))
   \<inter> set2_lp_iterm (lp_isubst a sigma)={}"
proof -
 obtain g t where body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "body_variable\<in>vars_term t"
 and absent: "body_variable\<notin>vars_term h"
  using checked by (auto simp: lpp_check_body_output_def lpc_body_only_variables_def)
 obtain x where variable: "rho body_variable=LPIVar x"
  using lpc_mgu_body_only_variable_free[OF mgu body absent] by blast
 have separate: "x\<notin>set2_lp_iterm (lp_isubst a sigma)"
  by (rule lpp_mgu_fresh_body_avoids_finite_head[OF mgu body absent variable finite])
 show ?thesis using lpp_checked_body_output_value[OF checked, of k eta sigma rho] variable separate by simp
qed

lemma lpp_checked_body_output_separate_caller:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes checked: "lpp_check_body_output h bs l body_variable target_term bindings"
 and mgu: "lpc_mgu_resolve a (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and finite: "lpp_finite_term (lp_isubst (eta v) sigma)"
 shows "set2_lp_iterm (lp_ieval target_term
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))
   \<inter> set2_lp_iterm (lp_isubst (eta v) sigma)={}"
proof -
 have member: "body_variable\<in>lpc_body_only_variables h bs"
  using checked by (simp add: lpp_check_body_output_def)
 show ?thesis using lpp_mgu_body_only_separate_live_caller[OF mgu member covered finite]
  lpp_checked_body_output_value[OF checked, of k eta sigma rho] by simp
qed

lemma lpp_clause_coordinate_positive:
 "lpp_check_clause_coordinate 3 (Var ''N'' :: (nat,string) term) (Var ''V1'') [(''V1'',Var ''$$$N'')]"
 by (simp add: lpp_check_clause_coordinate_def lp_cut_instance_subst_def lp_prefix_def numeral_3_eq_3)

lemma lpp_clause_coordinate_stale_negative:
 "\<not>lpp_check_clause_coordinate 3 (Var ''N'' :: (nat,string) term) (Var ''V1'') [(''V1'',Var ''N'')]"
 by (simp add: lpp_check_clause_coordinate_def lp_cut_instance_subst_def lp_prefix_def numeral_3_eq_3)

lemma lpp_body_output_head_variable_rejected:
 "x\<in>vars_term h \<Longrightarrow> \<not>lpp_check_body_output h bs l x target_term bindings"
 by (simp add: lpp_check_body_output_def lpc_body_only_variables_def)

lemma lpp_checked_recursive_head_successor_facts:
 assumes parameter_map: "lpp_check_clause_coordinate l (heads!i) target_parameter bindings"
 and fresh_map: "lpp_check_body_output (Fun p heads) bs l body_variable target_output bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p actuals) gs (Fun p heads) bs sigma rho"
 and bound: "i<length heads"
 and tracked: "lpp_runtime_parameter c (actuals!i)"
 and finite: "lpp_finite_term (lp_isubst (LPIFun p actuals) sigma)"
 shows "lpp_runtime_parameter c (lp_ieval target_parameter
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))) \<and>
  (\<exists>x. lp_ieval target_output
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))=LPIVar x) \<and>
  set2_lp_iterm (lp_ieval target_output
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))
   \<inter> set2_lp_iterm (lp_isubst (LPIFun p actuals) sigma)={}"
 using lpp_checked_head_parameter_successor[OF parameter_map mgu bound tracked, of k eta]
  lpp_checked_body_output_free[OF fresh_map mgu, of k eta]
  lpp_checked_body_output_separate_head[OF fresh_map mgu finite, of k eta] by blast

lemma lpp_checked_matching_head_successor_facts:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes matching: "lpp_check_matching_outputs [output_variable] (Fun p actual_terms) gs (Fun p heads) match_bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun p actual_terms) eta)
  (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun p heads) bs sigma rho"
 and parameter_map: "lpp_check_clause_coordinate l (heads!parameter_index) target_parameter bindings"
 and output_map: "lpp_check_clause_coordinate l (heads!output_index) target_output bindings"
 and bounds: "parameter_index<length actual_terms" "parameter_index<length heads" "output_index<length actual_terms" "output_index<length heads"
 and parameter_arg: "actual_terms!parameter_index=Var parameter_variable"
 and output_arg: "actual_terms!output_index=Var output_variable"
 and free: "lpc_free_knowledge {output_variable} eta"
 and tracked: "lpp_runtime_parameter c (eta parameter_variable)"
 shows "lpp_runtime_parameter c (lp_ieval target_parameter
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))) \<and>
  (\<exists>x. lp_ieval target_output
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))=LPIVar x)"
proof -
 have actual_mgu: "lpc_mgu_resolve (LPIFun p (map (\<lambda>t. lp_ieval t eta) actual_terms))
  (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun p heads) bs sigma rho"
  using mgu by simp
 have source_parameter: "lpp_runtime_parameter c ((map (\<lambda>t. lp_ieval t eta) actual_terms)!parameter_index)"
  using tracked bounds parameter_arg by simp
 have preserved: "lpc_free_knowledge {output_variable} (\<lambda>x. lp_isubst (eta x) sigma)"
  using lpp_checked_matching_parameter_outputs[OF matching mgu _ tracked] free by simp
 have source_free: "\<exists>x. lp_isubst ((map (\<lambda>t. lp_ieval t eta) actual_terms)!output_index) sigma=LPIVar x"
  using preserved bounds output_arg by (auto simp: lpc_free_knowledge_def)
 show ?thesis using lpp_checked_head_parameter_successor[OF parameter_map actual_mgu bounds(2) source_parameter, of k eta]
  lpp_checked_head_free_successor[OF output_map actual_mgu bounds(4) source_free, of k eta] by blast
qed

lemma lpp_body_output_positive:
 "lpp_check_body_output (Fun (0::nat) [Var ''N''])
  [LPCAtom (Fun 1 [Var ''N'',Var ''Fresh''])] 3 ''Fresh'' (Var ''V2'') [(''V2'',Var ''$$$Fresh'')]"
 by (simp add: lpp_check_body_output_def lpc_body_only_variables_def lpp_check_clause_coordinate_def
  lp_cut_instance_subst_def lp_prefix_def numeral_3_eq_3)

lemma lpp_body_output_missing_occurrence_negative:
 "\<not>lpp_check_body_output (Fun (0::nat) [Var ''N''])
  [LPCAtom (Fun 1 [Var ''N''])] 3 ''Fresh'' (Var ''V2'') [(''V2'',Var ''$$$Fresh'')]"
 by (simp add: lpp_check_body_output_def lpc_body_only_variables_def)

ML \<open>
val checked = @{thms lpp_checked_clause_coordinate_value lpp_checked_head_coordinate_value
 lpp_checked_head_parameter_successor lpp_checked_head_free_successor lpp_checked_body_output_value
 lpp_checked_body_output_free lpp_checked_body_output_separate_head lpp_checked_body_output_separate_caller
 lpp_clause_coordinate_positive lpp_clause_coordinate_stale_negative lpp_body_output_head_variable_rejected
 lpp_checked_recursive_head_successor_facts lpp_checked_matching_head_successor_facts
 lpp_body_output_positive lpp_body_output_missing_occurrence_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted head successor facts" else ();
\<close>
end
