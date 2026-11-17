theory LP_Prolog_Separation_Pair_Check
 imports LP_Prolog_Separation_Unification_Check LP_Prolog_Separation_Pair_Control
begin

definition lpp_check_separation_pair where
 "lpp_check_separation_pair separation_contexts i F a b mode yes no =
  (i<length separation_contexts \<and>
   lpp_check_separated_pair F (separation_contexts!i) a b \<and>
   lpp_empty_separation_branches separation_contexts mode yes no)"

theorem lpp_checked_separation_pair_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and extra: "lpp_check_separation_pair separation_contexts i (Fs!i) a b mode yes no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
 apply (rule lpp_separated_pair_node_contract[where yes_separation="[]" and no_separation="[]", OF compatible transfer checked shape])
 subgoal using extra by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def
   lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal using extra by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def
   lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal by simp
 subgoal by simp
 subgoal using extra by (simp add: lpp_check_separation_pair_def)
 done

lemma lpp_separation_pair_missing_context_rejected:
 "\<not>lpp_check_separation_pair [] i F a b mode yes no"
 by (simp add: lpp_check_separation_pair_def)

lemma lpp_separation_pair_missing_fact_rejected:
 "separation_contexts!i=[] \<Longrightarrow>
  \<not>lpp_check_separation_pair separation_contexts i F a b mode yes no"
 by (simp add: lpp_check_separation_pair_def lpp_separated_pair_missing_fact_rejected[OF refl])

lemma lpp_separation_pair_missing_failure_rejected:
 "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> \<not>lpp_empty_separation_target separation_contexts no \<Longrightarrow>
  \<not>lpp_check_separation_pair separation_contexts i F a b mode yes no"
 by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def)

ML \<open>
val checked = @{thms lpp_checked_separation_pair_node_contract lpp_separation_pair_missing_context_rejected
 lpp_separation_pair_missing_fact_rejected lpp_separation_pair_missing_failure_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation pair checker" else ();
\<close>
end
