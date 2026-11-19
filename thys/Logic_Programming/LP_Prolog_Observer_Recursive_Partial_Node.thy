theory LP_Prolog_Observer_Recursive_Partial_Node
 imports LP_Prolog_Observer_Cons_Node LP_Prolog_Recursive_Partial_Entry LP_Prolog_Parameter_Subterms
begin

text \<open>Discharge the widened recursive-entry fragment inside the cons node's
successor initialization. Other node conditions and failure initialization remain
explicit; the family induction still requires strict residual descent.\<close>

lemma lpp_observer_recursive_partial_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m helper_payload helper_saved k l refreshed next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=(LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved"
 and head: "fst (P!c)=Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var z]"
 and call_shape: "a=Fun p [input_term,Var parameter_variable,Var output_variable]"
 and coordinates: "lpp_check_recursive_entry_coordinates
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var z]) (snd (P!c)) l x y n z fresh_variable
   input_slot parameter_slot helper_slot tail_slot caller_slot (lpcl_bindings yes)"
 and entry: "\<And>eta. node_conditions i eta \<Longrightarrow>
   (\<exists>spine_length. lpp_list_length (lp_ieval input_term eta) spine_length) \<and>
   lpp_runtime_parameter initial_parameter (eta parameter_variable)"
 and initial_ground: "vars_term initial_parameter={}"
 and success_init: "\<And>eta sigma rho. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   lpp_finite_term (lp_ieval a eta) \<Longrightarrow>
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot
    (\<lambda>v. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) v) (lp_cut_resolution_env k l eta sigma rho)) \<Longrightarrow>
   node_conditions (lpcl_target yes) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
     (lp_cut_resolution_env k l eta sigma rho))"
 and failure_init: "\<And>eta. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   node_conditions (lpcl_target no) (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs rest) rest returned i"
proof -
 have ground_templates: "vars_term v={}" if "v\<in>lpp_parameter_subterm_templates f g initial_parameter" for v
  by (rule lpp_parameter_subterm_templates_ground[OF initial_ground that])
 have distinct: "distinct [x,y,n,z]"
  using coordinates by (simp add: lpp_check_recursive_entry_coordinates_def)
 show ?thesis
 proof (rule lpp_observer_cons_node_contract[where node_conditions=node_conditions and i=i and H="[n,z]" and argument_terms="[Var parameter_variable,Var output_variable]",
   unfolded list.map, OF program clear compatible transfer checked source_shape head call_shape distinct _ _ ground_templates _ failure_init covered])
  show "length [n,z]=length [Var parameter_variable,Var output_variable]" by simp
 next
  fix eta assume conditions: "node_conditions i eta"
  show "\<exists>spine_length. lpp_list_length (lp_ieval input_term eta) spine_length"
   using entry[OF conditions] by blast
 next
  fix eta sigma rho
  assume conditions: "node_conditions i eta"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and free: "lpc_free_knowledge (set (Fs!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
   and finite: "lpp_finite_term (lp_ieval a eta)"
   and mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
     (fst (P!c)) (snd (P!c)) sigma rho"
  obtain spine_length where spine: "lpp_list_length (lp_ieval input_term eta) spine_length"
   and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_variable)"
   using entry[OF conditions] by blast
  have successor: "lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot
    (\<lambda>v. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) v) (lp_cut_resolution_env k l eta sigma rho))"
   by (rule lpp_checked_recursive_partial_entry[OF coordinates mgu[unfolded call_shape head]
     spine finite[unfolded call_shape] tracked])
  show "node_conditions (lpcl_target yes) (\<lambda>v. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) v)
    (lp_cut_resolution_env k l eta sigma rho))"
   by (rule success_init[OF conditions known free observed finite mgu successor])
 qed
qed

ML \<open>
val checked = @{thms lpp_observer_recursive_partial_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive caller node" else ();
\<close>
end
