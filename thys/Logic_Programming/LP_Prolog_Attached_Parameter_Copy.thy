theory LP_Prolog_Attached_Parameter_Copy
 imports LP_Prolog_Parameter_Head_Return LP_Prolog_Observer_Conditioned_Matching
begin

text \<open>The repeated-parameter head copies the actual current ground parameter.
Coverage is obtained from the attached caller continuation, not from helper
finiteness alone. Saved alternatives retain their original environments.\<close>

lemma lpp_attached_parameter_copy_leaf_step:
 fixes env :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved)) event tt"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs tt"
proof -
 have live: "set (map fst specs) \<subseteq>
   (\<Union>goal\<in>set rest. \<Union>t\<in>set (lp_cut_terms goal). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have support: "set2_lp_iterm (env slot) \<subseteq> insert output_variable
  (\<Union>goal\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest).
    \<Union>t\<in>set (lp_cut_terms goal). set2_lp_iterm t)"
  if "(slot,shape)\<in>set specs" for slot shape
 proof -
  have pair_image: "fst (slot,shape)\<in>fst ` set specs"
   by (rule imageI[OF that])
  have membership: "slot\<in>set (map fst specs)"
   using pair_image by (simp only: set_map fst_conv)
  have occurrence: "slot\<in>(\<Union>goal\<in>set rest. \<Union>t\<in>set (lp_cut_terms goal). vars_term t)"
   by (rule subsetD[OF live membership])
  show ?thesis using lpp_attached_slot_runtime_coverage[OF occurrence, of env gs] by blast
 qed
 have attached: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved))"
  using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
  using lpp_parameter_copy_head_base_step[OF step[unfolded lpc_attach_answers_def, simplified] head spine tracked finite_rest
    attached[unfolded lpc_attach_answers_def, simplified] support] by simp

qed

lemma lpp_parameter_copy_head_finite_instance:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,LPIVar output_variable]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "lpp_finite_term (lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho)"
proof -
 have copied: "rho n= parameter"
  using lpp_parameter_copy_head_return[OF spine mgu tracked] by blast
 have finite_parameter: "lpp_finite_term parameter"
  by (rule lpp_ground_finite_term[OF lpp_runtime_parameter_ground[OF tracked]])
 show ?thesis using finite_parameter by (simp add: copied)
qed

lemma lpp_attached_parameter_copy_finite_step:
 fixes env :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved))"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix call pending clause mark ret alternatives sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) c m,env)#saved)=
  (LPCClause (LPCAtom call#pending) clause mark,ret)#alternatives"
 and bound: "clause<length P"
 and mgu: "lpc_mgu_resolve call pending (fst (P!clause)) (snd (P!clause)) sigma rho"
 have actual: "call=LPIFun p [input_value,parameter,LPIVar output_variable]" "clause=c"
  using shape by (auto simp: lpc_attach_answers_def)
 show "lpp_finite_term (lp_ieval (fst (P!clause)) rho)"
  unfolding actual head by (rule lpp_parameter_copy_head_finite_instance[OF mgu[unfolded actual head] spine tracked])
qed (auto simp: lpc_attach_answers_def)

lemma lpp_parameter_copy_successor_value:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes coordinate: "lpp_check_clause_coordinate l (Var n) target_output bindings"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,LPIVar output_variable]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "lp_ieval target_output
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho))= parameter \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval target_output
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))"
 using lpp_checked_clause_coordinate_value[OF coordinate, of k eta sigma rho]
  lpp_parameter_copy_head_return[OF spine mgu tracked] by auto

ML \<open>
val checked = @{thms lpp_attached_parameter_copy_leaf_step lpp_parameter_copy_head_finite_instance
 lpp_attached_parameter_copy_finite_step lpp_parameter_copy_successor_value};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached parameter copy" else ();
\<close>
end
