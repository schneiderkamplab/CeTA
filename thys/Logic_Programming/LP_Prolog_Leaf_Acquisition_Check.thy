theory LP_Prolog_Leaf_Acquisition_Check
 imports LP_Prolog_Leaf_Unification_Check
begin

theorem lpp_checked_leaf_separation_reflexive_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and extra: "lpp_check_separation_reflexive (nds!i) (contexts!i) separation_contexts i a b gs k l mode yes no retained no_separation"
 and coverage: "lpp_check_ground_relational_leaf_coverage
   (set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i))
   (functor_contexts!i) (map fst specs) active a gs"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
 apply (rule lpp_reflexive_leaf_separation_node_contract[OF compatible transfer checked shape])
 using extra coverage by (auto simp: lpp_check_separation_reflexive_def)

theorem lpp_checked_leaf_separation_fresh_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 and coverage: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active a gs"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
 apply (rule lpp_relational_fresh_matching_leaf_node_contract[OF compatible transfer checked shape])
 using extra coverage by (auto simp: lpp_check_separation_fresh_def)

ML \<open>
val checked = @{thms lpp_checked_leaf_separation_reflexive_node_contract lpp_checked_leaf_separation_fresh_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf acquisition checker" else ();
\<close>
end
