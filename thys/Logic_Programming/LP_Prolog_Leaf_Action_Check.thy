theory LP_Prolog_Leaf_Action_Check
 imports LP_Prolog_Leaf_Acquisition_Check LP_Prolog_Separation_Action_Check
begin

fun lpp_check_leaf_action_coverage where
 "lpp_check_leaf_action_coverage nd ctx facts separation slots action LPPSOrdinaryAction = True"
| "lpp_check_leaf_action_coverage nd ctx facts separation slots action (LPPSUnificationAction head) =
   lpp_check_leaf_unification_coverage nd ctx facts slots action"
| "lpp_check_leaf_action_coverage nd ctx facts separation slots action LPPSPairAction =
   (case action of LPPFCut (LPCREquality a b gs active saved k l successor mode outputs yes no) fs ns \<Rightarrow>
     lpp_check_ground_relational_leaf_coverage (set (lpcn_ground nd) \<union> lpp_source_context_ground ctx) facts slots active b gs \<and>
     lpp_check_leaf_pair_protection (set (lpcn_ground nd) \<union> lpp_source_context_ground ctx) facts separation a slots active
   | _ \<Rightarrow> False)"
| "lpp_check_leaf_action_coverage nd ctx facts separation slots action (LPPSReflexiveAction retained failed) =
   lpp_check_leaf_unification_coverage nd ctx facts slots action"
| "lpp_check_leaf_action_coverage nd ctx facts separation slots action (LPPSFreshAction normalized_facts failed x y z matching) =
   lpp_check_leaf_unification_coverage nd ctx facts slots action"
| "lpp_check_leaf_action_coverage nd ctx facts separation slots action (LPPSUnivAction pair_symbol output_name output_args) = True"

theorem lpp_checked_leaf_separation_action_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_separation_action fuel P (nds!i) (contexts!i) (Fs!i) separation_contexts i (states!i) action witness"
 and coverage: "lpp_check_leaf_action_coverage (nds!i) (contexts!i) (functor_contexts!i)
   (separation_contexts!i) (map fst specs) action witness"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (cases witness)
 case LPPSOrdinaryAction
 have local_check: "lpp_check_separation_ordinary separation_contexts (states!i) action"
  using extra LPPSOrdinaryAction by simp
 show ?thesis by (rule lpp_leaf_separation_ordinary_node_contract[OF compatible transfer checked local_check])
next
 case (LPPSUnificationAction head)
 have local_check: "lpp_check_separation_unification P (nds!i) (contexts!i) separation_contexts action head"
  using extra LPPSUnificationAction by simp
 show ?thesis
  apply (rule lpp_checked_leaf_separation_unification_node_contract[OF compatible transfer checked local_check])
  using coverage LPPSUnificationAction by simp
next
 case LPPSPairAction
 obtain a b gs active saved k l successor mode outputs yes no fs ns where operation: "action=LPPFCut (LPCREquality a b gs active saved k l successor mode outputs yes no) fs ns"
  and local_check: "lpp_check_separation_pair separation_contexts i (Fs!i) a b mode yes no"
  using extra LPPSPairAction by (auto split: lpp_functor_action.splits lpc_return_action.splits)
 have shape: "states!i=(LPCGoals (LPCUnify a b#gs),active)#saved"
  and source_check: "lpp_check_functor_equality_node T fs ns fuel P Q nds states contexts Fs functor_contexts
    (nds!i) (Fs!i) a b gs active saved k l successor mode outputs (contexts!i) (functor_contexts!i) yes no"
  using checked operation by (auto simp: lpp_check_functor_source_action_def)
 show ?thesis
  apply (rule lpp_leaf_empty_separation_pair_node_contract[OF compatible transfer source_check shape])
  using local_check coverage LPPSPairAction operation
  by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def)
next
 case (LPPSReflexiveAction retained failed)
 obtain a b gs active saved k l successor mode outputs yes no fs ns where operation: "action=LPPFCut (LPCREquality a b gs active saved k l successor mode outputs yes no) fs ns"
  and local_check: "lpp_check_separation_reflexive (nds!i) (contexts!i) separation_contexts i a b gs k l mode yes no retained failed"
  using extra LPPSReflexiveAction by (auto split: lpp_functor_action.splits lpc_return_action.splits)
 have shape: "states!i=(LPCGoals (LPCUnify a b#gs),active)#saved"
  and source_check: "lpp_check_functor_equality_node T fs ns fuel P Q nds states contexts Fs functor_contexts
    (nds!i) (Fs!i) a b gs active saved k l successor mode outputs (contexts!i) (functor_contexts!i) yes no"
  using checked operation by (auto simp: lpp_check_functor_source_action_def)
 show ?thesis
  apply (rule lpp_checked_leaf_separation_reflexive_node_contract[OF compatible transfer source_check shape local_check])
  using coverage LPPSReflexiveAction operation by simp
next
 case (LPPSFreshAction normalized_facts failed x y z matching)
 obtain a gs c m active saved k l A successor anchors bindings mode outputs yes no fs ns where operation: "action=LPPFCut (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no) fs ns"
  and local_check: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts failed x y z matching"
  using extra LPPSFreshAction by (auto split: lpp_functor_action.splits lpc_return_action.splits)
 have shape: "states!i=(LPCClause (LPCAtom a#gs) c m,active)#saved"
  and source_check: "lpp_check_functor_resolution_node T fs ns fuel P Q nds states contexts Fs functor_contexts
    (nds!i) (Fs!i) a gs c m active saved k l A successor anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
  using checked operation by (auto simp: lpp_check_functor_source_action_def)
 show ?thesis
  apply (rule lpp_checked_leaf_separation_fresh_node_contract[OF compatible transfer source_check shape local_check])
  using coverage LPPSFreshAction operation by simp
next
 case (LPPSUnivAction pair_symbol output_name output_args)
 obtain value_var name_var args_var middle facts where operation: "action=LPPFUniv value_var name_var args_var middle facts"
  and local_check: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
  using extra LPPSUnivAction by (auto split: lpp_functor_action.splits lpc_return_action.splits)
 show ?thesis by (rule lpp_checked_leaf_separation_univ_node_contract[OF compatible transfer checked[unfolded operation] local_check])
qed

ML \<open>
val checked = @{thms lpp_checked_leaf_separation_action_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted leaf action dispatcher" else ();
\<close>
end
