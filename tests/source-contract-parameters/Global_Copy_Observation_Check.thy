theory Global_Copy_Observation_Check
 imports Global_Runtime_Signature_Check
begin

text \<open>Successful repeated-parameter resolution copies the tracked parameter,
including compound ground values. Reuse its structural observation only after
proving the actual output's restricted leaf effect.\<close>

lemma copy_actual_step_preserves_observer:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime = (LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved"
 and invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime"
 and head: "fst (P!c) = Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
  (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) runtime)) event result"
 shows "event = None \<and> (\<exists>child.
  lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child \<and>
  result = lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) child) \<and>
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child)"
proof -
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?A = "lpp_parameter_leaf_templates f g initial_parameter"
 have active: "lpc_prefix_active runtime" by (simp add: shape)
 obtain child where silent: "event = None"
 and joint: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child"
 and actual: "result = lpc_attach_answers rest (lpc_reinterface ?R child)"
  using lpp_attached_observer_product_step[OF active step] by blast
 have leaf: "lpp_leaf_stack_invariant ?A specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
 and shared: "lpp_observer_output_alias oi hi runtime"
  using invariant by (simp_all add: lpp_observer_output_invariant_def lpp_observer_invariant_def)
 have base: "lpc_answer_transition P
  (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,?R env)#lpc_reinterface ?R saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 have finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R env))) rest)"
  using finite by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have child_leaf: "lpp_leaf_stack_invariant ?A specs result"
  by (rule lpp_attached_caller_copy_leaf_step[OF base head spine tracked mode finite_call finite_rest _ covered])
   (use leaf in \<open>simp add: shape lpc_reinterface_def\<close>)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_attached_caller_copy_finite_step[OF base _ head spine tracked])
   (use finite in \<open>simp add: shape lpc_reinterface_def\<close>)
 have child_shared: "lpp_observer_output_alias oi hi child"
  using lpp_observer_output_alias_step[OF joint shared] by blast
 have preserved: "lpp_observer_output_invariant ?A specs rest oi hi child"
  using child_leaf child_finite child_shared actual
  by (simp add: lpp_observer_output_invariant_def lpp_observer_invariant_def lpp_leaf_stack_attachment)
 show ?thesis using silent joint actual preserved by blast
qed

lemma copy_resolution_reuses_observation:
 fixes parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 shows "lp_isubst output_value sigma = parameter \<and> rho n = parameter \<and>
  lpp_runtime_parameter initial_parameter (lp_isubst output_value sigma) \<and>
  observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_isubst output_value sigma) shadow"
proof -
 have ground: "lp_seg_ground parameter" by (rule lpp_runtime_parameter_ground[OF tracked])
 have copied: "lp_isubst output_value sigma = parameter" "rho n = parameter"
  using actual ground by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)
 have after_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_isubst output_value sigma)"
 proof (cases "lp_seg_ground output_value")
  case True
  show ?thesis using effect lp_seg_ground_subst[OF True, of sigma] by simp
 next
  case False
  obtain x where shape: "output_value = LPIVar x"
   using mode False by (auto simp: lpp_caller_output_mode_def)
  show ?thesis unfolding shape
   by (rule lpp_parameter_copy_head_caller_leaf[OF spine actual[unfolded shape] tracked
    finite_rest effect[unfolded shape]]) auto
 qed
 show ?thesis using copied tracked observed_coordinate_new_leaf_history[OF after_effect] observed by simp
qed

lemma copy_six_to_two_global_step:
 assumes clause: "((source_symbol,map Var [x0,x1,x2,s0,sn,s2]),[(target_symbol,map Var [n,sn])]) \<in> set Q"
 and distinct: "distinct [x0,x1,x2,s0,sn,s2,n]"
 shows "([(source_symbol,[input_value,parameter,output_value,input_shadow,parameter_shadow,output_shadow])],
   [(target_symbol,[parameter,parameter_shadow])]) \<in> lp_ild Q"
proof -
 let ?nu = "\<lambda>x. if x=x0 then input_value else if x=x1 then parameter else
   if x=x2 then output_value else if x=s0 then input_shadow else
   if x=sn then parameter_shadow else if x=s2 then output_shadow else parameter"
 show ?thesis
  using lp_seg_residual_step[OF clause, where
   a="(source_symbol,[input_value,parameter,output_value,input_shadow,parameter_shadow,output_shadow])"
   and \<sigma>=LPIVar and \<rho>="?nu" and rest="[]"] distinct
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
qed

lemma copy_ten_to_six_global_step:
 assumes clause: "((source_symbol,map Var [x0,n,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [n,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,n,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 shows "([(source_symbol,[input_value,parameter,output_value,saved_parameter,functor_value,
    input_shadow,parameter_shadow,output_shadow,saved_shadow,functor_shadow])],
   [(target_symbol,[parameter,saved_parameter,next_functor,parameter_shadow,saved_shadow,next_functor_shadow])]) \<in> lp_ild Q"
proof -
 let ?nu = "\<lambda>x. if x=x0 then input_value else if x=n then parameter else
  if x=x2 then output_value else if x=x3 then saved_parameter else if x=x4 then functor_value else
  if x=s0 then input_shadow else if x=sn then parameter_shadow else if x=s2 then output_shadow else
  if x=s3 then saved_shadow else if x=s4 then functor_shadow else if x=y then next_functor else next_functor_shadow"
 show ?thesis
  using lp_seg_residual_step[OF clause, where
   a="(source_symbol,[input_value,parameter,output_value,saved_parameter,functor_value,
    input_shadow,parameter_shadow,output_shadow,saved_shadow,functor_shadow])"
   and \<sigma>=LPIVar and \<rho>="?nu" and rest="[]"] distinct
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
qed

lemma actual_copy_six_to_two_observation:
 fixes parameter output_value :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and clause: "((source_symbol,map Var [x0,x1,x2,s0,sn,s2]),[(target_symbol,map Var [rn,sn])]) \<in> set Q"
 and distinct: "distinct [x0,x1,x2,s0,sn,s2,rn]"
 shows "lpp_runtime_parameter initial_parameter (lp_isubst output_value sigma) \<and>
  observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_isubst output_value sigma) shadow \<and>
  ([(source_symbol,[input_value,parameter,output_value,input_shadow,shadow,output_shadow])],
   [(target_symbol,[lp_isubst output_value sigma,shadow])]) \<in> (lp_ild Q)\<^sup>+"
 using copy_resolution_reuses_observation[OF actual spine tracked mode finite_rest effect observed]
  copy_six_to_two_global_step[OF clause distinct, of input_value parameter output_value input_shadow shadow output_shadow]
 by blast

lemma actual_copy_ten_to_six_observation:
 fixes parameter output_value saved_parameter :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and saved_ground: "lp_seg_ground saved_parameter"
 and clause: "((source_symbol,map Var [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [rn,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 shows "lpp_runtime_parameter initial_parameter (lp_isubst output_value sigma) \<and>
  observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_isubst output_value sigma) shadow \<and>
  lp_isubst saved_parameter sigma = saved_parameter \<and>
  ([(source_symbol,[input_value,parameter,output_value,saved_parameter,functor_value,
    input_shadow,shadow,output_shadow,saved_shadow,functor_shadow])],
   [(target_symbol,[lp_isubst output_value sigma,lp_isubst saved_parameter sigma,next_functor,
     shadow,saved_shadow,next_functor_shadow])]) \<in> (lp_ild Q)\<^sup>+"
 using copy_resolution_reuses_observation[OF actual spine tracked mode finite_rest effect observed]
  lp_seg_ground_subst[OF saved_ground, of sigma]
  copy_ten_to_six_global_step[OF clause distinct, of input_value parameter output_value saved_parameter
   functor_value input_shadow shadow output_shadow saved_shadow functor_shadow next_functor next_functor_shadow]
 by (auto intro: r_into_trancl)

ML \<open>
val checked = @{thms copy_actual_step_preserves_observer copy_resolution_reuses_observation copy_six_to_two_global_step
 copy_ten_to_six_global_step actual_copy_six_to_two_observation actual_copy_ten_to_six_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted global copy observations" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-observation/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Full row contracts and family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_OBSERVATION_KERNEL_CHECKED";
\<close>
end
