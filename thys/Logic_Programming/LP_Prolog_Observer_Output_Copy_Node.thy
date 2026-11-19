theory LP_Prolog_Observer_Output_Copy_Node
 imports LP_Prolog_Observer_Caller_Copy_Node LP_Prolog_Observer_Output_Alias
begin

definition lpp_observer_output_invariant where
 "lpp_observer_output_invariant A specs rest oi hi runtime =
   (lpp_observer_invariant A specs rest runtime \<and> lpp_observer_output_alias oi hi runtime)"

lemma lpp_observer_output_invariant_scopes:
 assumes "lpc_rest_scopes rest = {}"
 shows "lpp_observer_output_invariant A specs rest oi hi (lpc_return_scope_word swaps runtime) =
   lpp_observer_output_invariant A specs rest oi hi runtime"
 by (simp add: lpp_observer_output_invariant_def lpp_observer_invariant_scopes[OF assms]
   lpp_observer_output_alias_scopes)

lemma lpp_observer_output_prefix_initial:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and p q :: "string lp_cut_symbol"
 assumes checked: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 and entry: "lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot eta"
 and helper_coordinate: "oi < length helper_payload" "helper_payload ! oi = Var helper_slot"
 defines rest_def: "rest \<equiv> [LPCAtom (Fun q [Var ti,Var hi,Var ci])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun p [eta input_slot,eta parameter_slot,eta helper_slot])],
   case_sum (lpc_return_env helper_payload eta) (lpc_return_env payload eta))]"
 shows "\<exists>xs caller_shape.
   lpp_runtime_structure (lpc_return_env payload eta ti) (lpp_structural_argument_list xs) \<and>
   lpp_runtime_structure (lpc_return_env payload eta ci) caller_shape \<and>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
    [(hi,Fun (Inr ()) []),(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest oi hi runtime"
proof -
 have shared: "lpp_observer_output_alias oi hi runtime"
  unfolding runtime_def
  apply (rule lpp_observer_output_alias_initial[OF helper_coordinate])
  using checked by (simp_all add: lpp_check_prefix_caller_coordinates_def)
 show ?thesis
  using lpp_restricted_prefix_output_initial[OF checked entry, where p=p and q=q
    and helper_env="lpc_return_env helper_payload eta" and f=f and g=g] shared
  by (simp add: lpp_observer_output_invariant_def rest_def runtime_def)
qed

lemma lpp_checked_observer_output_copy_contract:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs source_context source_functors yes no"
    and success_conditions: "\<And>sigma rho. lpc_mgu_resolve (lp_ieval a eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
      node_conditions (lpcl_target yes)
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
          (lp_cut_resolution_env k l eta sigma rho))"
    and failure_conditions: "node_conditions (lpcl_target no)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and call_shape: "lp_ieval a eta=LPIFun p [input_value,parameter,output_value]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and caller_mode: "lpp_caller_output_mode output_value"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"

 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest runtime"
 and shared: "lpp_observer_output_alias oi hi runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof (rule lpp_observer_silent_contract[OF _ lower])
 fix event result
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
 have leaf: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp_all add: lpp_observer_invariant_def)
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
   map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)"
  using finite by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 obtain child u swaps where silent: "event=None"
 and joint: "?T runtime None child"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface ?R child)"
 and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions (lpc_reinterface ?L (lpc_return_scope_word swaps child)) u"
 and child_leaf: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs (lpc_reinterface ?R (lpc_return_scope_word swaps child))"
  using lpp_checked_observer_caller_copy[where node_conditions=node_conditions, OF compatible program checked success_conditions
    failure_conditions known free observed functors head call_shape spine tracked caller_mode shape represented
    finite_call finite_rest covered leaf step] by blast
 have base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
    ?R combined_env)#lpc_reinterface ?R combined_saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_attached_caller_copy_finite_step[OF base[unfolded call_shape] _ head spine tracked])
   (use finite in \<open>simp add: shape lpc_reinterface_def call_shape\<close>)
 have child_shared: "lpp_observer_output_alias oi hi child"
  using lpp_observer_output_alias_step[OF joint shared] by blast
 have child_invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child"
  using child_leaf child_finite actual child_shared
  by (simp add: lpp_observer_output_invariant_def lpp_observer_invariant_def lpp_observer_reinterface_scopes lpp_leaf_stack_scopes)
 have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions (lpc_reinterface ?L child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_observer_reinterface_scopes)
 show "event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface ?R child) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface ?L child) u \<and>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child)"
  using silent actual strict module child_invariant by blast
qed

lemma lpp_observer_output_copy_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m helper_payload helper_saved k l refreshed next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=(LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and call_shape: "a=Fun p [input_term,parameter_term,output_term]"
 and entry: "\<And>eta. node_conditions i eta \<Longrightarrow>
   (\<exists>spine_length. lpp_finite_spine cons nil (lp_ieval input_term eta) spine_length) \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval parameter_term eta)"
 and output_coordinate: "oi < length helper_payload" "helper_payload ! oi = output_term"
 and output_observed: "(hi,Fun (Inr ()) []) \<in> set specs"
 and success_init: "\<And>eta sigma rho. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   lpp_finite_term (lp_ieval a eta) \<Longrightarrow>
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   node_conditions (lpcl_target yes) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
     (lp_cut_resolution_env k l eta sigma rho))"
 and failure_init: "\<And>eta. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   node_conditions (lpcl_target no) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime \<Longrightarrow>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_output_invariant_scopes[OF clear])
next
 fix eta runtime
 show "node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 proof (intro impI)
  assume conditions: "node_conditions i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
  and free: "lpc_free_knowledge (set (Fs!i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
  and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i)"
  and invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: source_shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  obtain spine_length where
   spine: "lpp_finite_spine cons nil (lp_ieval input_term eta) spine_length"
   and tracked: "lpp_runtime_parameter initial_parameter (lp_ieval parameter_term eta)"
   using entry[OF conditions] by blast
  have original_invariant: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest runtime"
  and shared: "lpp_observer_output_alias oi hi runtime"
   using invariant by (simp_all add: lpp_observer_output_invariant_def)
  have initial_ground: "vars_term initial_parameter = {}"
   using tracked by (simp add: lpp_runtime_parameter_def)
  have output_mode: "lpp_caller_output_mode (lp_ieval output_term eta)"
   using lpp_observer_output_alias_mode[OF shared[unfolded runtime_shape]
     represented[unfolded runtime_shape source_shape] output_coordinate
     original_invariant[unfolded runtime_shape] output_observed
     lpp_parameter_leaf_templates_ground[where f=f and g=g, OF initial_ground]] by blast
  have actual_call: "lp_ieval a eta=LPIFun p [lp_ieval input_term eta,lp_ieval parameter_term eta,lp_ieval output_term eta]"
   by (simp add: call_shape)
  have finite_call: "lpp_finite_term (lp_ieval a eta)"
   using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_invariant_def runtime_shape
    lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
  have success_conditions: "node_conditions (lpcl_target yes)
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x) (lp_cut_resolution_env k l eta sigma rho))"
   if mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho" for sigma rho
   by (rule success_init[OF conditions known free observed finite_call mgu])
  have failure_conditions: "node_conditions (lpcl_target no)
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
   by (rule failure_init[OF conditions known observed])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_observer_output_copy_contract[where node_conditions=node_conditions and eta=eta and runtime=runtime and specs=specs
    and combined_env=combined_env and combined_saved=combined_saved and names=names and rest=rest,
    OF compatible transfer checked
    success_conditions failure_conditions known free observed functors
    head actual_call spine tracked output_mode runtime_shape represented[unfolded source_shape] covered original_invariant shared])
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict module child_invariant by blast
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_observer_output_prefix_initial lpp_observer_output_invariant_scopes lpp_checked_observer_output_copy_contract
 lpp_observer_output_copy_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output copy node" else ();
\<close>
end
