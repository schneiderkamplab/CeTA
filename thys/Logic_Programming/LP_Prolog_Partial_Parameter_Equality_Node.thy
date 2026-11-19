theory LP_Prolog_Partial_Parameter_Equality_Node
 imports LP_Prolog_Observer_Conditioned_Subterm_Equality LP_Prolog_Observer_Subterm_Parameter_Equality
begin

lemma lpp_checked_observer_partial_parameter_equality_contract:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs helper_payload helper_saved k l next mode outputs source_context source_functors yes no"
    and success_conditions: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      node_conditions (lpcl_target yes)
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
          (lp_cut_resolution_env k l eta sigma eta))"
    and failure_conditions: "node_conditions (lpcl_target no)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and ground: "vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
 and binding: "lpp_check_parameter_replacement parameter f g b"
 and tracked_parameter: "lpp_runtime_parameter initial_parameter (eta parameter)"
 and shape: "runtime=(LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),helper_payload)#helper_saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 obtain current_parameter where parameter: "eta parameter=lp_ieval current_parameter LPIVar"
 and returned_parameter: "lpp_parameter_return initial_parameter current_parameter"
 and ground_parameter: "vars_term initial_parameter={}"
  using tracked_parameter by (auto simp: lpp_runtime_parameter_def)
 obtain replacement_template where replacement: "lp_ieval b eta=lp_ieval replacement_template LPIVar"
 and original_allowed: "replacement_template\<in>lpp_parameter_leaf_templates f g initial_parameter"
  using lpp_checked_parameter_replacement_sound[where eta=eta and d=current_parameter and c=initial_parameter, OF binding parameter returned_parameter] by blast
 have allowed: "replacement_template\<in>lpp_parameter_subterm_templates f g initial_parameter"
  using original_allowed lpp_parameter_subterm_templates_include[of f g initial_parameter] by blast
 have closed: "v\<in>lpp_parameter_subterm_templates f g initial_parameter"
  if "lpp_finite_template_subterm v replacement_template" for v
  by (rule lpp_parameter_subterm_templates_closed[OF allowed that])
 have ground_templates: "vars_term v={}" if "v\<in>lpp_parameter_subterm_templates f g initial_parameter" for v
  by (rule lpp_parameter_subterm_templates_ground[OF ground_parameter that])
 show ?thesis by (rule lpp_checked_observer_conditioned_subterm_equality_contract[where node_conditions=node_conditions, OF
  compatible program checked success_conditions failure_conditions
  known free observed functors ground closed replacement allowed ground_templates
  shape represented covered invariant lower])
qed

theorem lpp_observer_partial_parameter_equality_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs helper_payload helper_saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=(LPCGoals (LPCUnify a b#gs),helper_payload)#helper_saved"
 and ground: "vars_term b \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and binding: "lpp_check_parameter_replacement parameter f g b"
 and tracked_parameter: "\<And>eta. node_conditions i eta \<Longrightarrow> lpp_runtime_parameter initial_parameter (eta parameter)"
 and success_init: "\<And>eta sigma. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
   node_conditions (lpcl_target yes) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
     (lp_cut_resolution_env k l eta sigma eta))"
 and failure_init: "\<And>eta. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   node_conditions (lpcl_target no) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest runtime \<Longrightarrow>
   lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest child \<longrightarrow>
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
  and invariant: "lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: source_shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  have tracked: "lpp_runtime_parameter initial_parameter (eta parameter)"
   by (rule tracked_parameter[OF conditions])
  have success_conditions: "node_conditions (lpcl_target yes)
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
      (lp_cut_resolution_env k l eta sigma eta))"
   if mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
     (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma" for sigma
   by (rule success_init[OF conditions known observed mgu])
  have failure_conditions: "node_conditions (lpcl_target no)
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
   by (rule failure_init[OF conditions known observed])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_observer_partial_parameter_equality_contract[
    where eta=eta and runtime=runtime and specs=specs and node_conditions=node_conditions
    and combined_env=combined_env and combined_saved=combined_saved and names=names and rest=rest,
    OF compatible transfer checked success_conditions failure_conditions known free observed functors
    ground binding tracked runtime_shape represented[unfolded source_shape] covered invariant])
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict module child_invariant by blast
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_checked_observer_partial_parameter_equality_contract
 lpp_observer_partial_parameter_equality_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter equality node" else ();
\<close>
end
