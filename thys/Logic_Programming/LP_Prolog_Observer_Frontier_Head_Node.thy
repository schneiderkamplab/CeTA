theory LP_Prolog_Observer_Frontier_Head_Node
 imports LP_Prolog_Observer_Frontier_Resolution_Node LP_Prolog_Observer_Head_Node
begin

theorem lpp_checked_frontier_observer_head_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and scope_free: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c witness"
 and success_member: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpcl_target yes\<in>frontier_nodes"
 and failure_member: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpcl_target no\<in>frontier_nodes"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
 apply (rule lpp_frontier_observer_resolution_node_contract[where yes_separation="[]" and no_separation="[]",
   OF program scope_free compatible transfer checked shape head success_member failure_member _ _ _ _ covered])
 using success_target failure_target
 by (auto simp: lpp_empty_separation_target_def lpp_check_separation_transport_def)

ML \<open>
val checked = @{thms lpp_checked_frontier_observer_head_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer head node" else ();
\<close>
end
