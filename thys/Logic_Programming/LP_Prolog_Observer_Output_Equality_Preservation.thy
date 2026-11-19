theory LP_Prolog_Observer_Output_Equality_Preservation
 imports LP_Prolog_Observer_Output_Copy_Node LP_Prolog_Partial_Parameter_Equality_Node
begin

text \<open>Equality preserves the combined observer invariant independently of
residual-node representation. Both successful substitutions and failure rollback
use the actual attached transition, with caller coverage retained explicitly.\<close>

lemma lpp_observer_output_equality_child_invariant:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime = (LPCGoals (LPCUnify a b#gs),env)#saved"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and replacement: "b = lp_ieval replacement_template LPIVar"
 and allowed: "replacement_template \<in> A"
 and ground: "\<And>v. v \<in> A \<Longrightarrow> vars_term v = {}"
 and closed: "\<And>v. lpp_finite_template_subterm v replacement_template \<Longrightarrow> v \<in> A"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) runtime)) event result"
 and joint: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child"
 and actual: "result = lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) child)"
 shows "lpp_observer_output_invariant A specs rest oi hi child"
proof -
 let ?R = "\<lambda>e x. e (Inr x)"
 have leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
 and shared: "lpp_observer_output_alias oi hi runtime"
  using invariant by (simp_all add: lpp_observer_output_invariant_def lpp_observer_invariant_def)
 have finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R env))) rest)"
  using finite by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),?R env)#lpc_reinterface ?R saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_equality_base)
 have child_leaf: "lpp_leaf_stack_invariant A specs result"
  by (rule lpp_attached_subterm_equality_leaf_base_step[OF base _ finite_rest finite_call replacement allowed ground closed covered])
   (use leaf in \<open>simp add: shape lpc_reinterface_def\<close>)
 have actual_ground: "lp_seg_ground b"
  using ground[OF allowed] by (simp add: replacement lp_seg_ground_eval)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_finite_attached_ground_equality_step[OF base _ actual_ground])
   (use finite in \<open>simp add: shape lpc_reinterface_def\<close>)
 have child_shared: "lpp_observer_output_alias oi hi child"
  using lpp_observer_output_alias_step[OF joint shared] by blast
 show ?thesis using child_leaf child_finite child_shared actual
  by (simp add: lpp_observer_output_invariant_def lpp_observer_invariant_def lpp_leaf_stack_attachment)
qed

lemma lpp_observer_output_equality_preservation:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime = (LPCGoals (LPCUnify a b#gs),env)#saved"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and replacement: "b = lp_ieval replacement_template LPIVar"
 and allowed: "replacement_template \<in> A"
 and ground: "\<And>v. v \<in> A \<Longrightarrow> vars_term v = {}"
 and closed: "\<And>v. lpp_finite_template_subterm v replacement_template \<Longrightarrow> v \<in> A"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) runtime)) event result"
 shows "event = None \<and> (\<exists>child.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child \<and>
   result = lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) child) \<and>
   lpp_observer_output_invariant A specs rest oi hi child)"
proof -
 have active: "lpc_prefix_active runtime" by (simp add: shape)
 obtain child where silent: "event = None"
 and joint: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child"
 and actual: "result = lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) child)"
  using lpp_attached_observer_product_step[OF active step] by blast
 have preserved: "lpp_observer_output_invariant A specs rest oi hi child"
  by (rule lpp_observer_output_equality_child_invariant[OF shape invariant covered replacement allowed ground closed step joint actual])
 show ?thesis using silent joint actual preserved by blast
qed

lemma lpp_observer_output_scalar_equality_preservation:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime = (LPCGoals (LPCUnify a (LPIFun (LPCUser scalar) [])#gs),env)#saved"
 and invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and initial_ground: "vars_term initial_parameter = {}"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) runtime)) event result"
 shows "event = None \<and> (\<exists>child.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None child \<and>
   result = lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) child) \<and>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child)"
proof -
 let ?A = "lpp_parameter_leaf_templates f g initial_parameter"
 have allowed: "Fun (LPCUser scalar) [] \<in> ?A" by (simp add: lpp_parameter_leaf_templates_def)
 have ground: "vars_term v = {}" if "v \<in> ?A" for v
  by (rule lpp_parameter_leaf_templates_ground[OF initial_ground that])
 have closed: "v \<in> ?A" if "lpp_finite_template_subterm v (Fun (LPCUser scalar) [])" for v
  using that allowed by (cases rule: lpp_finite_template_subterm.cases) auto
 show ?thesis
  by (rule lpp_observer_output_equality_preservation[OF shape invariant covered _ allowed ground closed step]) simp
qed

ML \<open>
val checked = @{thms lpp_observer_output_equality_child_invariant lpp_observer_output_equality_preservation
 lpp_observer_output_scalar_equality_preservation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted equality preservation" else ();
\<close>
end
