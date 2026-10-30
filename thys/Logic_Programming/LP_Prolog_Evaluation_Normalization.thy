theory LP_Prolog_Evaluation_Normalization
 imports LP_Answer_Initial_Refinement LP_Prolog_Context_Is_Staged
begin

text \<open>Evaluation is normalized to the existing shared equality semantics.
This includes unification failure and saved alternatives. The premise requires
an actual integer evaluation; finite groundness alone is insufficient.\<close>
lemma lpp_integer_evaluation_normalized_contract:
  assumes evaluated: "lpp_integer_evaluation e n"
    and contract: "lp_answer_contract
      (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      ((LPCGoals (LPCUnify a (lpp_integer_value n)#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_initial_refinement[OF contract])
  fix event tt
  assume step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  have exact: "\<And>outcome. lpp_integer_source_builtin ''2:is'' [a,e] outcome = lpp_integer_is_outcome a e outcome"
    by simp
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
    using step evaluated by (auto simp: lpp_domain_answers_def)
  have equality: "lpc_answer_transition P
    ((LPCGoals (LPCUnify a (lpp_integer_value n)#gs),eta)#saved) event tt"
    by (rule lpp_checked_is_uses_shared_equality[OF evaluated exact actual])
  have normalized: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
    ((LPCGoals (LPCUnify a (lpp_integer_value n)#gs),eta)#saved) event tt"
    by (rule lpp_answer_transition.base[OF _ equality]) (simp add: lpp_builtin_active_def)
  show "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain
    ((LPCGoals (LPCUnify a (lpp_integer_value n)#gs),eta)#saved) event tt"
    using normalized by (simp add: lpp_domain_answers_def)
qed

end
