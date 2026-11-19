theory LP_Prolog_Observer_Planned_Family
 imports LP_Prolog_Observer_Plan_Nodes
begin

theorem lpp_observer_planned_family_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes finite: "finite members"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and checked: "\<And>m. m\<in>members \<Longrightarrow>
  lpp_check_observer_continuing_plan T fuel P Q (family_nodes m) (states m) (contexts m) (frees m) (functors m)
   (return_symbols m) (arities m) (separations m) (versions m) (plans m) (frontiers m) (actions m) (witnesses m)"
 and selected_conditions: "\<And>m. m\<in>members \<Longrightarrow> node_conditions m=
  lpp_observer_frontier_conditions (set (frontiers m)) (lpp_separation_node_conditions (separations m))"
 and external: "\<And>m j role. m\<in>members \<Longrightarrow> j<length (family_nodes m) \<Longrightarrow>
  (j,role)\<in>set (plans m) \<Longrightarrow>
  (role=LPPORBoundary \<or> (\<exists>saved. role=LPPORReturned saved)) \<Longrightarrow>
  lpp_observer_referenced_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (node_conditions m)
   (lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors node_conditions)
   (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned j"
 and represented: "lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors node_conditions runtime subject"
 and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof (rule lpp_observer_family_contract_from_nodes[where J="lpp_observer_invariant {v. vars_term v={}} specs rest" and rest=rest and returned=returned and B=lpp_builtin_signature and U="lpp_univ_source_builtin names operation" and D=lpp_univ_source_domain, OF finite _ represented invariant residual])
 fix m j
 assume member: "m\<in>members" and bound: "j<length (family_nodes m)"
 have included: "lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors node_conditions child u"
  if "lpp_premised_functor_module_rep names operation SP (family_nodes m) (states m) (contexts m) (frees m) (functors m)
   (lpp_observer_frontier_conditions (set (frontiers m)) (lpp_separation_node_conditions (separations m)))
   (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u" for child u
  by (rule lpp_observer_family_member[OF member]) (use that selected_conditions[OF member] in simp)
 show "lpp_observer_referenced_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (node_conditions m)
   (lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors node_conditions)
   (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned j"
  unfolding selected_conditions[OF member]
  apply (rule lpp_observer_planned_node_contract[OF compatible transfer program clear covered checked[OF member] bound _])
  subgoal for child u by (rule included) assumption
  subgoal for role using external[OF member bound, of role] selected_conditions[OF member] by simp
  done
qed

ML \<open>
val thms = @{thms lpp_observer_planned_family_contract};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted planned observer family" else ();
\<close>
end
