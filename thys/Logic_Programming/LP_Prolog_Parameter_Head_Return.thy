theory LP_Prolog_Parameter_Head_Return
 imports LP_Prolog_Repeated_Parameter_Head LP_Prolog_Runtime_Parameter
   LP_Prolog_Relational_Matching_Leaf LP_Prolog_Actual_Returns
begin

text \<open>Matching preserves free outputs up to renaming. Repeated-parameter
heads bind a free output by copying the current parameter. Coverage includes
the actual active continuation; no constraint is imposed on saved environments.\<close>

lemma lpp_matching_free_outputs:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu=lp_ieval call eta"
 and free: "lpc_free_knowledge F eta"
 and covered: "F \<subseteq> vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpc_free_knowledge F (\<lambda>x. lp_isubst (eta x) sigma)"
proof -
 obtain delta where inverse: "\<And>x. x\<in>F \<Longrightarrow>
   lp_isubst (lp_isubst (eta x) sigma) delta=eta x"
  using lpp_matching_context_inverse[OF mgu matching] covered by blast
 have variables: "\<forall>x\<in>F. \<exists>y. lp_isubst (eta x) sigma=LPIVar y"
 proof (intro ballI)
  fix x assume x: "x\<in>F"
  obtain y where represented_value: "eta x=LPIVar y"
   using free x by (auto simp: lpc_free_knowledge_def)
  show "\<exists>y. lp_isubst (eta x) sigma=LPIVar y"
   by (rule lpc_isubst_variable_reflect) (use inverse[OF x] represented_value in simp)
 qed
 have injective: "inj_on (\<lambda>x. lp_isubst (eta x) sigma) F"
 proof (rule inj_onI)
  fix x y assume x: "x\<in>F" and y: "y\<in>F"
  and same: "lp_isubst (eta x) sigma=lp_isubst (eta y) sigma"
  have old: "eta x=eta y" using inverse[OF x] inverse[OF y] same by metis
  show "x=y" using free x y old by (auto simp: lpc_free_knowledge_def inj_on_def)
 qed
 show ?thesis using variables injective by (simp add: lpc_free_knowledge_def)
qed

lemma lpp_matching_parameter_and_free_outputs:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu=lp_ieval call eta"
 and free: "lpc_free_knowledge F eta"
 and covered: "F \<subseteq> vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and parameter: "lpp_runtime_parameter c (eta p)"
 shows "lpc_free_knowledge F (\<lambda>x. lp_isubst (eta x) sigma) \<and>
   lpp_runtime_parameter c (lp_isubst (eta p) sigma)"
 using lpp_matching_free_outputs[OF mgu matching free covered]
  lpp_runtime_parameter_subst[OF parameter] by blast

fun lpp_check_parameter_copy_head where
 "lpp_check_parameter_copy_head (Fun p [Fun nil [],Var n,Var m]) = (n=m)"
| "lpp_check_parameter_copy_head _ = False"

lemma lpp_parameter_copy_head_shape:
 "lpp_check_parameter_copy_head h \<Longrightarrow>
  \<exists>p nil n. h=Fun p [Fun nil [],Var n,Var n]"
 by (cases h rule: lpp_check_parameter_copy_head.cases) auto

lemma lpp_parameter_copy_head_input:
 assumes spine: "lpp_finite_spine cons nil input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_variable]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 shows "input_value=LPIFun nil []"
proof -
 have equation: "lp_isubst (LPIFun p [input_value,parameter,output_variable]) sigma =
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 show ?thesis using spine equation by (cases rule: lpp_finite_spine.cases) auto
qed

lemma lpp_parameter_copy_head_return:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes spine: "lpp_finite_spine cons nil input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,LPIVar output_variable]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "input_value=LPIFun nil [] \<and> sigma output_variable= parameter \<and>
  rho n= parameter \<and> lpp_runtime_parameter initial_parameter (sigma output_variable) \<and>
  lpp_runtime_parameter initial_parameter (rho n)"
proof -
 have ground: "lp_seg_ground parameter" by (rule lpp_runtime_parameter_ground[OF tracked])
 have equation: "lp_isubst (LPIFun p [input_value,parameter,LPIVar output_variable]) sigma =
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have copied: "sigma output_variable= parameter" "rho n= parameter"
  using equation by (auto simp: lp_seg_ground_subst[OF ground])
 show ?thesis using lpp_parameter_copy_head_input[OF spine mgu] copied tracked by simp
qed

lemma lpp_parameter_copy_head_caller_leaf:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes spine: "lpp_finite_spine cons nil input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,LPIVar output_variable]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and finite_rest: "lpp_finite_goals gs"
 and observed: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) shape caller"
 and covered: "set2_lp_iterm caller \<subseteq> insert output_variable
  (\<Union>goal\<in>set gs. \<Union>t\<in>set (lp_cut_terms goal). set2_lp_iterm t)"
 shows "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter)
  shape (lp_isubst caller sigma)"
proof -
 obtain current where represented_value: "parameter=lp_ieval current LPIVar"
 and relation: "lpp_parameter_return initial_parameter current"
 and closed: "vars_term initial_parameter={}"
  using tracked by (auto simp: lpp_runtime_parameter_def)
 have allowed: "current\<in>lpp_parameter_leaf_templates f g initial_parameter"
  using relation by (auto simp: lpp_parameter_return_def lpp_parameter_leaf_templates_def)
 obtain qs where rest: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have exact: "input_value=LPIFun nil []" by (rule lpp_parameter_copy_head_input[OF spine mgu])
 have actual_mgu: "lpc_mgu_resolve
  (LPIFun p [lp_ieval (Fun nil []) LPIVar,lp_ieval current LPIVar,LPIVar output_variable])
  (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs)
  (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
  using mgu by (simp add: exact represented_value rest)
 have support: "set2_lp_iterm caller \<subseteq> insert output_variable
  (\<Union>goal\<in>set qs. \<Union>t\<in>set (lp_cut_terms goal). vars_term t)"
  using covered unfolding rest[symmetric]
  by (simp add: lpp_template_runtime_support lpp_evaluated_goals_runtime_support lpp_finite_goal_map)
 have ground_templates: "vars_term v={}" if "v\<in>lpp_parameter_leaf_templates f g initial_parameter" for v
  by (rule lpp_parameter_leaf_templates_ground[OF closed that])
 show ?thesis by (rule lpp_repeated_parameter_head_leaf_transport[OF actual_mgu _ allowed ground_templates observed support]) simp
qed

lemma lpp_parameter_copy_head_positive:
 "lpp_check_parameter_copy_head (Fun (0::nat) [Fun 1 [],Var (''N''),Var ''N''])"
 by simp

lemma lpp_parameter_copy_head_nonrepeated_negative:
 "\<not>lpp_check_parameter_copy_head (Fun (0::nat) [Fun 1 [],Var (''N''),Var ''M''])"
 by simp

definition lpp_check_matching_outputs where
 "lpp_check_matching_outputs F call gs h bindings =
  (lp_cut_check_match call h bindings \<and>
   list_all (\<lambda>x. x\<in>vars_term call \<or>
    list_ex (\<lambda>goal. list_ex (\<lambda>t. x\<in>vars_term t) (lp_cut_terms goal)) gs) F)"

lemma lpp_checked_matching_parameter_outputs:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes checked: "lpp_check_matching_outputs F call gs h bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and free: "lpc_free_knowledge (set F) eta"
 and parameter: "lpp_runtime_parameter c (eta p)"
 shows "lpc_free_knowledge (set F) (\<lambda>x. lp_isubst (eta x) sigma) \<and>
   lpp_runtime_parameter c (lp_isubst (eta p) sigma)"
proof -
 have matching: "lp_ieval h (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval call eta"
  using checked by (simp add: lpp_check_matching_outputs_def lp_cut_check_match_def lp_ieval_finite_subst[symmetric])
 have coverage: "set F \<subseteq> vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using checked by (auto simp: lpp_check_matching_outputs_def list_all_iff list_ex_iff)
 show ?thesis by (rule lpp_matching_parameter_and_free_outputs[OF mgu matching free coverage parameter])
qed

lemma lpp_matching_outputs_positive:
 "lpp_check_matching_outputs [''X''] (Fun (0::nat) [Var ''X'']) []
  (Fun 0 [Var ''H'']) [(''H'',Var ''X'')]"
 by (simp add: lpp_check_matching_outputs_def lp_cut_check_match_def lp_cut_match_subst_def)

lemma lpp_matching_outputs_missing_coverage_negative:
 "\<not>lpp_check_matching_outputs [''Y''] (Fun (0::nat) [Var ''X'']) []
  (Fun 0 [Var ''H'']) [(''H'',Var ''X'')]"
 by (simp add: lpp_check_matching_outputs_def lp_cut_check_match_def lp_cut_match_subst_def)

lemma lpp_parameter_copy_head_base_step:
 fixes env :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) clause scope,env)#saved) event tt"
 and head: "fst (P!clause)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and finite_rest: "lpp_finite_goals gs"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) clause scope,env)#saved)"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm (env slot) \<subseteq> insert output_variable
    (\<Union>goal\<in>set gs. \<Union>t\<in>set (lp_cut_terms goal). set2_lp_iterm t)"
 shows "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 fix a goals c m eta es sigma rho
 assume shape: "((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) clause scope,env)#saved)=
   (LPCClause (LPCAtom a#goals) c m,eta)#es"
 and bound: "c<length P"
 and mgu: "lpc_mgu_resolve a goals (fst (P!c)) (snd (P!c)) sigma rho"
 have exact: "a=LPIFun p [input_value,parameter,LPIVar output_variable]" "goals=gs" "c=clause" "eta=env"
  using shape by auto
 show "lpp_leaf_environment_transport (lpp_parameter_leaf_templates f g initial_parameter) specs eta sigma"
  unfolding lpp_leaf_environment_transport_def
  using lpp_parameter_copy_head_caller_leaf[OF spine mgu[unfolded exact head] tracked finite_rest] covered
  by (auto simp: exact)
next
 fix a b goals eta es sigma
 assume "((LPCClause (LPCAtom (LPIFun p [input_value,parameter,LPIVar output_variable])#gs) clause scope,env)#saved)=
   (LPCGoals (LPCUnify a b#goals),eta)#es"
 then show "lpp_leaf_environment_transport (lpp_parameter_leaf_templates f g initial_parameter) specs eta sigma" by simp
qed

ML \<open>
val checked = @{thms lpp_matching_free_outputs lpp_matching_parameter_and_free_outputs
 lpp_parameter_copy_head_shape lpp_parameter_copy_head_input lpp_parameter_copy_head_return
 lpp_parameter_copy_head_caller_leaf lpp_parameter_copy_head_positive
 lpp_parameter_copy_head_nonrepeated_negative lpp_checked_matching_parameter_outputs
 lpp_matching_outputs_positive lpp_matching_outputs_missing_coverage_negative
 lpp_parameter_copy_head_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter head return" else ();
\<close>
end
