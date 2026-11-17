theory LP_Prolog_Finite_Direct_Test
 imports LP_Prolog_Finite_Direct_Observed_Is
begin

lemma scalar_equality_admitted:
 "lpp_finite_direct_goal (LPCUnify (LPIVar ''x'') (LPIFun (LPCUser ''17'') []))"
 by simp

lemma rational_cycle_equation_excluded:
 "\<not>lpp_finite_direct_goal (LPCUnify (LPIVar ''x'')
    (LPIFun (LPCUser ''f'') [LPIVar ''x'']))"
 by simp

lemma unbounded_dynamic_call_excluded:
 "\<not>lpp_finite_direct_goal (LPCMeta (LPIVar ''x''))"
 by simp

lemma saved_unsafe_equation_not_erased:
 "\<not>lpp_finite_direct_state
   [(LPCGoals [],eta), (LPCGoals [LPCUnify (LPIVar ''x'')
      (LPIFun (LPCUser ''f'') [LPIVar ''x''])],rho)]"
 by (simp add: lpp_finite_direct_state_def)

lemma unrestricted_initial_expression_is_finite:
 "lpp_finite_source_domain ''2:is'' [a,lp_ieval e LPIVar]"
 by (rule lpp_finite_is_source_domain[OF lpp_finite_term_initial])

lemma three_argument_expression_error:
 "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
   ((LPCGoals [LPCAtom (LPIFun (LPCUser ''2:is'')
     [a,lp_ieval (Fun (LPCUser ''renamed'') [x,y,z]) LPIVar])],eta)#saved) R t ret"
 by (simp only: lp_ieval.simps list.map; rule lpp_finite_large_arity_error_contract)
    (simp_all add: lpp_finite_term_initial)

end
