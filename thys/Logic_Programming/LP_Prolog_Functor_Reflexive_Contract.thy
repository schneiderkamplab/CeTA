theory LP_Prolog_Functor_Reflexive_Contract
 imports LP_Prolog_Functor_Finite_Unification LP_Prolog_Separation_Reflexive LP_Prolog_Equation_Rewrite
begin

text \<open>The input/value equality from univ initialization remains an
  explicit checked context equation. It justifies a reflexive actual MGU,
  without assuming arbitrary finite-term unification preserves finiteness.\<close>

lemma lpp_finite_reflexive_equality_base_step:
 assumes step: "lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),eta)#saved) event tt"
 and finite: "lpp_finite_execution ((LPCGoals (LPCUnify a b#gs),eta)#saved)"
 and equal: "a=b"
 shows "lpp_finite_execution tt"
 using step finite equal
 by (cases rule: lpc_answer_transition.cases)
   (auto simp: lpp_finite_execution_def lpp_finite_goals_def list_all_iff
     dest: lpp_reflexive_mgu_finite_goals)

lemma lpp_finite_functor_reflexive_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and equation: "lpp_check_equation_rewrite (contexts!i) a b"
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
 have runtime_equal: "lp_ieval a eta=lp_ieval b eta"
  by (rule lpp_equation_rewrite_equal[where E="lpp_stable_scalar_evaluation operation" and SP=SP, OF equation])
    (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
 have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta (states!i)) ev ys"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show "lpp_finite_execution ys"
  using lpp_finite_reflexive_equality_base_step[OF _ _ runtime_equal] base finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_initialized_univ_equation_available:
 "lpp_check_equation_rewrite
   (lpp_context_with_equations ctx [(input_template,Var value_variable)]) input_template (Var value_variable)"
 by (cases ctx; cases input_template)
   (auto simp: lpp_check_equation_rewrite_def lpp_check_context_equation_rewrite_def)

lemma lpp_reflexive_context_missing_equation_rejected:
 "a\<noteq>b \<Longrightarrow> \<not>lpp_check_equation_rewrite ([],[],[]) a b"
 by (simp add: lpp_check_equation_rewrite_def lpp_check_context_equation_rewrite_def)

ML \<open>
val checked = @{thms lpp_initialized_univ_equation_available lpp_reflexive_context_missing_equation_rejected lpp_finite_reflexive_equality_base_step lpp_finite_functor_reflexive_node_contract};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted reflexive functor contract dependency" else ();
\<close>
end
