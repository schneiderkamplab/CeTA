theory LP_Prolog_Functor_Finite_Unification
 imports LP_Prolog_Functor_Simple_Control LP_Prolog_Finite_Matching_Head LP_Prolog_Stable_Builtins
begin

text \<open>Finite preservation may use checked incoming knowledge. Keeping
  these premises inside the node contract avoids turning a conditional source
  fact into a global invariant or copying it onto a resumed alternative.\<close>

lemma lpp_functor_contextual_cut_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and stable: "\<And>eta ev ys.
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_functor_control_cut_contract[where J=J, OF compatible transfer checked])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal using stable by blast
 subgoal by blast
 done

lemma lpp_finite_ground_equality_base_step:
 assumes step: "lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),eta)#saved) event tt"
 and finite: "lpp_finite_execution ((LPCGoals (LPCUnify a b#gs),eta)#saved)"
 and ground: "lp_seg_ground b"
 shows "lpp_finite_execution tt"
 by (rule lpp_finite_base_answer_step[OF step finite]) (use ground in auto)

lemma lpp_finite_matching_resolution_base_step:
 assumes step: "lpc_answer_transition P ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved) event tt"
 and finite: "lpp_finite_execution ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix a' gs' c' m' eta' es sigma rho
 assume shape: "((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)=
   (LPCClause (LPCAtom a'#gs') c' m',eta')#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have matched: "lp_ieval (fst (P!c)) (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval a eta"
  using matching unfolding lp_cut_check_match_def by (simp add: lp_ieval_finite_subst[symmetric])
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
  using finite by (auto simp: lpp_finite_execution_def lpp_finite_goals_def lp_cut_terms.simps)
 show "lpp_finite_term (lp_ieval (fst (P!c')) rho)"
  using lpp_matching_head_finite_instance[OF _ matched finite_call] mgu shape by auto
qed auto

lemma lpp_finite_functor_ground_equality_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and ground: "vars_term b \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
proof (rule lpp_functor_contextual_cut_node_contract[OF compatible transfer checked])
 fix eta ev ys
 assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have runtime_ground: "lp_seg_ground (lp_ieval b eta)"
  using ground known lpp_stable_context_ground_sound[OF observed]
  by (auto simp: lp_seg_ground_eval lp_cut_knowledge_def)
 have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta (states!i)) ev ys"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show "lpp_finite_execution ys"
  using lpp_finite_ground_equality_base_step[OF _ _ runtime_ground] base finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_finite_functor_matching_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
proof (rule lpp_functor_cut_node_contract[OF compatible transfer checked])
 fix eta ev ys
 assume step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta (states!i)) ev ys"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show "lpp_finite_execution ys"
  using lpp_finite_matching_resolution_base_step[OF _ _ matching] base finite
  by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = @{thms lpp_functor_contextual_cut_node_contract lpp_finite_ground_equality_base_step
 lpp_finite_matching_resolution_base_step lpp_finite_functor_ground_equality_node_contract
 lpp_finite_functor_matching_node_contract};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted finite functor unification dependency" else ();
\<close>
end
