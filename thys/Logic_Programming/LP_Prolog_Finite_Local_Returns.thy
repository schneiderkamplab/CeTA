theory LP_Prolog_Finite_Local_Returns
 imports LP_Prolog_Finite_Local_Split
begin

text \<open>The continuation consumes checked facts about actual returns. This
predicate checks only variables used by its goals, not the entire answer
interface. A finite rational graph supplies no finite-term premise.\<close>

definition lpp_check_finite_return_goals where
 "lpp_check_finite_return_goals A G gs =
   list_all (\<lambda>g. lpp_direct_source_goal g \<and> lpp_static_template A g \<and>
     list_all (\<lambda>t. vars_term t \<subseteq> set G) (lp_cut_terms g)) gs"

lemma lpp_finite_return_goal:
 assumes direct: "lpp_direct_source_goal g"
   and static: "lpp_static_template A g"
   and finite: "\<And>t x. t\<in>set (lp_cut_terms g) \<Longrightarrow> x\<in>vars_term t \<Longrightarrow> lpp_finite_term (eta x)"
 shows "lpp_finite_direct_goal (lp_cut_map (\<lambda>t. lp_ieval t eta) g) \<and>
   lpp_static_goal A (lp_cut_map (\<lambda>t. lp_ieval t eta) g)"
 using direct static finite
 by (cases g; auto intro: lpp_finite_term_eval; metis lpp_direct_source_goal.simps lp_ieval.simps term.exhaust)

lemma lpp_checked_finite_return_goals:
 assumes checked: "lpp_check_finite_return_goals A G gs"
   and finite: "\<And>x. x\<in>set G \<Longrightarrow> lpp_finite_term (eta x)"
 shows "lpp_finite_direct_invariant A (lpc_return_eval eta [(LPCGoals gs,outputs)])"
proof -
 have each: "lpp_finite_direct_goal (lp_cut_map (\<lambda>t. lp_ieval t eta) g) \<and>
     lpp_static_goal A (lp_cut_map (\<lambda>t. lp_ieval t eta) g)" if "g\<in>set gs" for g
   by (rule lpp_finite_return_goal)
     (use checked finite that in \<open>auto simp: lpp_check_finite_return_goals_def list_all_iff\<close>)
 show ?thesis using each
 by (auto simp: lpp_check_finite_return_goals_def lpp_finite_direct_invariant_def
   lpp_finite_direct_state_def lpp_static_state_def lpc_return_eval_def list_all_iff)
qed

lemma lpp_checked_ground_return_goals:
 assumes checked: "lpp_check_finite_return_goals A G gs"
   and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 shows "lpp_finite_direct_invariant A (lpc_return_eval eta [(LPCGoals gs,outputs)])"
 by (rule lpp_checked_finite_return_goals[OF checked])
   (rule lpp_ground_finite_term, rule ground, assumption)

theorem lpp_finite_local_ground_split_interface_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context outgoing_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and continuation: "lpp_check_finite_return_goals A
      (lpcts_ground receipt @ filter (\<lambda>x. x\<in>lpp_source_context_ground outgoing_context)
        (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and returns: "\<And>rho. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      \<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
        lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
        lpp_stable_context_holds operation SP outgoing_context theta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP outgoing_context theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof (rule lpp_finite_local_split_interface_lower[OF compatible transfer checked program known observed free finite _ first_descent return_descent lower]; (assumption)?)
 fix rho
 assume actual: "lpp_stable_actual_return operation P
   (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
 obtain theta where rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
   and ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
   and observed_return: "lpp_stable_context_holds operation SP outgoing_context theta"
   using returns[OF actual] by blast
 have context_ground: "\<forall>x\<in>lpp_source_context_ground outgoing_context. lp_seg_ground (theta x)"
   by (rule lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground
     lpp_stable_context_finite_envelope[OF compatible observed_return]])
 have continuation_finite: "lpp_finite_direct_invariant A
     (lpc_return_eval theta [(LPCGoals (lpcts_rest receipt),map Var (lpcn_vars (lpctr_node entry)))])"
   by (rule lpp_checked_ground_return_goals[OF continuation])
     (use ground context_ground in \<open>auto simp: lp_cut_knowledge_def\<close>)
 show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
     lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
     lpp_stable_context_holds operation SP outgoing_context theta \<and>
     lpp_finite_direct_invariant A
       (lpc_return_eval theta [(LPCGoals (lpcts_rest receipt),map Var (lpcn_vars (lpctr_node entry)))])"
   using rho ground observed_return continuation_finite by blast
qed

ML \<open>
val checked = [@{thm lpp_finite_local_ground_split_interface_lower}, @{thm lpp_checked_finite_return_goals}, @{thm lpp_checked_ground_return_goals}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local return transport" else ();
\<close>
end
