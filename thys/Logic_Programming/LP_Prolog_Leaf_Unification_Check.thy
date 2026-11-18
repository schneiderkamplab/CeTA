theory LP_Prolog_Leaf_Unification_Check
 imports LP_Prolog_Leaf_Head_Check
begin

fun lpp_check_leaf_unification_coverage where
 "lpp_check_leaf_unification_coverage nd ctx facts slots (LPPFCut control fs ns) =
  (case control of
    LPCREquality a b gs active saved k l next mode outputs yes no \<Rightarrow>
     lpp_check_ground_relational_leaf_coverage
       (set (lpcn_ground nd) \<union> lpp_source_context_ground ctx) facts slots active a gs
  | LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no \<Rightarrow>
     lpp_check_relational_leaf_coverage facts slots active a gs
  | _ \<Rightarrow> False)"
| "lpp_check_leaf_unification_coverage nd ctx facts slots action = False"

theorem lpp_checked_leaf_separation_unification_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_separation_unification P (nds!i) (contexts!i) separation_contexts action witness"
 and coverage: "lpp_check_leaf_unification_coverage (nds!i) (contexts!i) (functor_contexts!i) (map fst specs) action"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (cases action)
 case (LPPFCut control fs ns)
 show ?thesis
 proof (cases control)
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have shape: "states!i=(LPCGoals (LPCUnify a b#gs),active)#saved"
   and check: "lpp_check_functor_equality_node T fs ns fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) a b gs active saved k l successor mode outputs (contexts!i) (functor_contexts!i) yes no"
   using checked LPPFCut LPCREquality by (auto simp: lpp_check_functor_source_action_def)
  have ground: "vars_term b\<subseteq> set (lpcn_ground (nds!i))\<union>lpp_source_context_ground (contexts!i)"
   and branches: "lpp_empty_separation_branches separation_contexts mode yes no"
   using extra LPPFCut LPCREquality by auto
  have leaf: "lpp_check_ground_relational_leaf_coverage
    (set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i))
    (functor_contexts!i) (map fst specs) active a gs"
    using coverage LPPFCut LPCREquality by simp
  show ?thesis
   apply (rule lpp_ground_leaf_empty_separation_equality_node_contract[OF compatible transfer check shape ground leaf])
   using branches by (auto simp: lpp_empty_separation_branches_def)
 next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have shape: "states!i=(LPCClause (LPCAtom a#gs) c m,active)#saved"
   and check: "lpp_check_functor_resolution_node T fs ns fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) a gs c m active saved k l A successor anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
   using checked LPPFCut LPCRResolution by (auto simp: lpp_check_functor_source_action_def)
  obtain head where head: "lpp_check_separation_head P (nds!i) (contexts!i) a c head"
   and branches: "lpp_empty_separation_branches separation_contexts mode yes no"
   using extra LPPFCut LPCRResolution by (auto split: option.splits)
  have leaf: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active a gs"
    using coverage LPPFCut LPCRResolution by simp
  show ?thesis
   apply (rule lpp_checked_leaf_separation_head_node_contract[OF compatible transfer check shape head leaf])
   using branches by (auto simp: lpp_empty_separation_branches_def)
 next
  case LPCRTerminal then show ?thesis using extra LPPFCut by simp
 next
  case LPCRInconsistent then show ?thesis using extra LPPFCut by simp
 next
  case LPCRAdmin then show ?thesis using extra LPPFCut by simp
 next
  case LPCRCase then show ?thesis using extra LPPFCut by simp
 next
  case LPCRMeta then show ?thesis using extra LPPFCut by simp
 qed
next
 case LPPFTest then show ?thesis using extra by simp
next
 case LPPFIs then show ?thesis using extra by simp
next
 case LPPFUniv then show ?thesis using extra by simp
next
 case LPPFTrim then show ?thesis using extra by simp
next
 case LPPFParallel then show ?thesis using extra by simp
qed

ML \<open>
val checked = @{thms lpp_checked_leaf_separation_unification_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf unification checker" else ();
\<close>
end
