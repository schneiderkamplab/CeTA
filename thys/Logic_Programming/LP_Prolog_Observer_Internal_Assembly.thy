theory LP_Prolog_Observer_Internal_Assembly
 imports LP_Prolog_Observer_Plan LP_Prolog_Observer_Ground_Equality_Simulation
begin

lemma lpp_observer_equality_template:
 "lpp_observer_equality_frame (lpc_return_eval eta ss) = lpp_observer_equality_frame ss"
 by (induction ss rule: lpp_observer_equality_frame.induct)
    (auto simp: lpc_return_eval_def)

fun lpp_observer_may_univ where
 "lpp_observer_may_univ ((LPCGoals (LPCAtom (Var x)#gs),payload)#saved) = True"
| "lpp_observer_may_univ ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),payload)#saved) = (f=''2:=..'')"
| "lpp_observer_may_univ ss = False"

lemma lpp_observer_univ_template:
 "lpp_observer_univ_frame (lpc_return_eval eta ss) \<Longrightarrow> lpp_observer_may_univ ss"
 by (induction ss rule: lpp_observer_may_univ.induct)
    (auto simp: lpc_return_eval_def)

fun lpp_observer_equality_witness where
 "lpp_observer_equality_witness LPPSPairAction = True"
| "lpp_observer_equality_witness (LPPSReflexiveAction retained failed) = True"
| "lpp_observer_equality_witness (LPPSUnificationAction None) = True"
| "lpp_observer_equality_witness _ = False"

lemma lpp_observer_equality_receipt_sound:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functors
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functors!i) yes no"
 and shape: "states!i=(LPCGoals (LPCUnify a b#gs),active)#saved"
 and kind: "lpp_observer_equality_witness witness"
 and extra: "lpp_check_separation_action fuel P (nds!i) (contexts!i) (Fs!i) separation_contexts i (states!i)
  (LPPFCut (LPCREquality a b gs active saved k l next mode outputs yes no) yes_facts no_facts) witness"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
  (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
proof (cases witness)
 case LPPSPairAction
 have check: "lpp_check_separation_pair separation_contexts i (Fs!i) a b mode yes no"
 using extra LPPSPairAction by simp
 show ?thesis by (rule lpp_checked_separation_pair_node_simulation[OF compatible transfer checked shape check])
next
 case (LPPSReflexiveAction retained failed)
 have check: "lpp_check_separation_reflexive (nds!i) (contexts!i) separation_contexts i a b gs k l mode yes no retained failed"
 using extra LPPSReflexiveAction by simp
 show ?thesis by (rule lpp_checked_separation_reflexive_node_simulation[OF compatible transfer checked shape check])
next
 case (LPPSUnificationAction head)
 have head: "head=None" using kind LPPSUnificationAction by (cases head) auto
 have ground: "vars_term b \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and success: "mode \<noteq> LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure: "mode \<noteq> LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 using extra LPPSUnificationAction head by (auto simp: lpp_empty_separation_branches_def)
 show ?thesis by (rule lpp_finite_empty_separation_ground_equality_node_simulation[OF compatible transfer checked shape ground success failure])
next
 case LPPSOrdinaryAction then show ?thesis using kind by simp
next
 case LPPSFreshAction then show ?thesis using kind by simp
next
 case LPPSUnivAction then show ?thesis using kind by simp
qed

ML \<open>
val thms = @{thms lpp_observer_equality_template lpp_observer_univ_template lpp_observer_equality_receipt_sound};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted internal observer coverage" else ();
\<close>
end
