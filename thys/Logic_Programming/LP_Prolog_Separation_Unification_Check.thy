theory LP_Prolog_Separation_Unification_Check
 imports LP_Prolog_Separation_Head_Check
begin

definition lpp_empty_separation_branches where
 "lpp_empty_separation_branches separation_contexts mode yes no =
  ((mode\<noteq>LPCAlwaysFailure \<longrightarrow> lpp_empty_separation_target separation_contexts yes) \<and>
   (mode\<noteq>LPCAlwaysSuccess \<longrightarrow> lpp_empty_separation_target separation_contexts no))"

fun lpp_check_separation_unification where
 "lpp_check_separation_unification P nd ctx separation_contexts (LPPFCut control fs ns) witness =
  (case control of
    LPCREquality a b gs active saved k l next mode outputs yes no \<Rightarrow>
     (witness=None \<and> vars_term b\<subseteq> set (lpcn_ground nd)\<union>lpp_source_context_ground ctx \<and>
      lpp_empty_separation_branches separation_contexts mode yes no)
  | LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no \<Rightarrow>
     (case witness of None \<Rightarrow> False | Some head \<Rightarrow>
      lpp_check_separation_head P nd ctx a c head \<and>
      lpp_empty_separation_branches separation_contexts mode yes no)
  | _ \<Rightarrow> False)"
| "lpp_check_separation_unification P nd ctx separation_contexts action witness = False"

theorem lpp_checked_separation_unification_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_separation_unification P (nds!i) (contexts!i) separation_contexts action witness"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
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
  show ?thesis
   apply (rule lpp_finite_empty_separation_ground_equality_node_contract[OF compatible transfer check shape ground])
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
  show ?thesis
   apply (rule lpp_checked_separation_head_node_contract[OF compatible transfer check shape head])
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

lemma lpp_separation_resolution_missing_head_rejected:
 "\<not>lpp_check_separation_unification P nd ctx separation_contexts
   (LPPFCut (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) fs ns) None"
 by simp

lemma lpp_separation_failure_context_required:
 "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> \<not>lpp_empty_separation_target separation_contexts no \<Longrightarrow>
  \<not>lpp_empty_separation_branches separation_contexts mode yes no"
 by (simp add: lpp_empty_separation_branches_def)

lemma lpp_separation_success_context_required:
 "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> \<not>lpp_empty_separation_target separation_contexts yes \<Longrightarrow>
  \<not>lpp_empty_separation_branches separation_contexts mode yes no"
 by (simp add: lpp_empty_separation_branches_def)

ML \<open>
val checked = @{thms lpp_checked_separation_unification_node_contract
 lpp_separation_resolution_missing_head_rejected lpp_separation_failure_context_required
 lpp_separation_success_context_required};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation unification checker" else ();
\<close>
end
