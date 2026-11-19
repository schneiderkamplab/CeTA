theory Global_Cons_Invariant_Check
 imports Recursive_Split_Observer_Check
begin

lemma cons_actual_step_preserves_observer:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime = (LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved"
 and invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime"
 and head: "fst (P!c) = Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]"
 and spine: "lpp_list_length input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and distinct: "distinct [x,y,n,out]"
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
 have initial_ground: "vars_term initial_parameter = {}"
  using tracked by (simp add: lpp_runtime_parameter_def)
 have ground_templates: "vars_term v = {}" if "v \<in> ?A" for v
  by (rule lpp_parameter_leaf_templates_ground[OF initial_ground that])
 have live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have child_leaf: "lpp_leaf_stack_invariant ?A specs result"
  by (rule lpp_attached_cons_leaf_step[where H="[n,out]", OF base _ ground_templates _ spine distinct _ finite_call finite_rest live])
   (use leaf head in \<open>simp_all add: shape lpc_reinterface_def\<close>)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_attached_cons_finite_step[where H="[n,out]", OF base _ _ spine distinct])
   (use finite head in \<open>simp_all add: shape lpc_reinterface_def\<close>)
 have child_shared: "lpp_observer_output_alias oi hi child"
  using lpp_observer_output_alias_step[OF joint shared] by blast
 have preserved: "lpp_observer_output_invariant ?A specs rest oi hi child"
  using child_leaf child_finite child_shared actual
  by (simp add: lpp_observer_output_invariant_def lpp_observer_invariant_def lpp_leaf_stack_attachment)
 show ?thesis using silent joint actual preserved by blast
qed


ML \<open>
val checked = @{thms cons_actual_step_preserves_observer};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons invariant" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-invariant/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Residual row/family assembly remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_CONS_INVARIANT_KERNEL_CHECKED";
\<close>
end
